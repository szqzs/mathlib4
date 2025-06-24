/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Mathlib.Control.Basic
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.Maximize.MoreParsing
-- import Mathlib.Tactic.Linarith.Oracle.SimplexAlgorithm
import Mathlib.Tactic.Ring.Basic

/-!
# `linarith`: solving linear arithmetic goals

`linarith` is a tactic for solving goals with linear arithmetic.

Suppose we have a set of hypotheses in `n` variables
`S = {a₁x₁ + a₂x₂ + ... + aₙxₙ R b₁x₁ + b₂x₂ + ... + bₙxₙ}`,
where `R ∈ {<, ≤, =, ≥, >}`.
Our goal is to determine if the inequalities in `S` are jointly satisfiable, that is, if there is
an assignment of values to `x₁, ..., xₙ` such that every inequality in `S` is true.

Specifically, we aim to show that they are *not* satisfiable. This amounts to proving a
contradiction. If our goal is also a linear inequality, we negate it and move it to a hypothesis
before trying to prove `False`.

When the inequalities are over a dense linear order, `linarith` is a decision procedure: it will
prove `False` if and only if the inequalities are unsatisfiable. `linarith` will also run on some
types like `ℤ` that are not dense orders, but it will fail to prove `False` on some unsatisfiable
problems. It will run over concrete types like `ℕ`, `ℚ`, and `ℝ`, as well as abstract types that
are instances of `LinearOrderedCommRing`.

## Algorithm sketch

First, the inequalities in the set `S` are rearranged into the form `tᵢ Rᵢ 0`, where
`Rᵢ ∈ {<, ≤, =}` and each `tᵢ` is of the form `∑ cⱼxⱼ`.

`linarith` uses an untrusted oracle to search for a certificate of unsatisfiability.
The oracle searches for a list of natural number coefficients `kᵢ` such that `∑ kᵢtᵢ = 0`, where for
at least one `i`, `kᵢ > 0` and `Rᵢ = <`.

Given a list of such coefficients, `linarith` verifies that `∑ kᵢtᵢ = 0` using a normalization
tactic such as `ring`. It proves that `∑ kᵢtᵢ < 0` by transitivity, since each component of the sum
is either equal to, less than or equal to, or less than zero by hypothesis. This produces a
contradiction.

## Preprocessing

`linarith` does some basic preprocessing before running. Most relevantly, inequalities over natural
numbers are cast into inequalities about integers, and rational division by numerals is canceled
into multiplication. We do this so that we can guarantee the coefficients in the certificate are
natural numbers, which allows the tactic to solve goals over types that are not fields.

Preprocessors are allowed to branch, that is, to case split on disjunctions. `linarith` will succeed
overall if it succeeds in all cases. This leads to exponential blowup in the number of `linarith`
calls, and should be used sparingly. The default preprocessor set does not include case splits.

## Oracles

There are two oracles that can be used in `linarith` so far.

1. **Fourier-Motzkin elimination.**
  This technique transforms a set of inequalities in `n` variables to an equisatisfiable set in
  `n - 1` variables. Once all variables have been eliminated, we conclude that the original set was
  unsatisfiable iff the comparison `0 < 0` is in the resulting set.
  While performing this elimination, we track the history of each derived comparison. This allows us
  to represent any comparison at any step as a positive combination of comparisons from the original
  set. In particular, if we derive `0 < 0`, we can find our desired list of coefficients
  by counting how many copies of each original comparison appear in the history.
  This oracle was historically implemented earlier, and is sometimes faster on small states, but it
  has [bugs](https://github.com/leanprover-community/mathlib4/issues/2717) and can not handle
  large problems. You can use it with `linarith (config := { oracle := .fourierMotzkin })`.

2. **Simplex Algorithm (default).**
  This oracle reduces the search for a unsatisfiability certificate to some Linear Programming
  problem. The problem is then solved by a standard Simplex Algorithm. We use
  [Bland's pivot rule](https://en.wikipedia.org/wiki/Bland%27s_rule) to guarantee that the algorithm
  terminates.
  The default version of the algorithm operates with sparse matrices as it is usually faster. You
  can invoke the dense version by `linarith (config := { oracle := .simplexAlgorithmDense })`.

## Implementation details

`linarith` homogenizes numerical constants: the expression `1` is treated as a variable `t₀`.

Often `linarith` is called on goals that have comparison hypotheses over multiple types. This
creates multiple `linarith` problems, each of which is handled separately; the goal is solved as
soon as one problem is found to be contradictory.

Disequality hypotheses `t ≠ 0` do not fit in this pattern. `linarith` will attempt to prove equality
goals by splitting them into two weak inequalities and running twice. But it does not split
disequality hypotheses, since this would lead to a number of runs exponential in the number of
disequalities in the context.

The oracle is very modular. It can easily be replaced with another function of type
`List Comp → ℕ → MetaM ((Std.HashMap ℕ ℕ))`,
which takes a list of comparisons and the largest variable
index appearing in those comparisons, and returns a map from comparison indices to coefficients.
An alternate oracle can be specified in the `LinarithConfig` object.

A variant, `nlinarith`, adds an extra preprocessing step to handle some basic nonlinear goals.
There is a hook in the `LinarithConfig` configuration object to add custom preprocessing routines.

The certificate checking step is *not* by reflection. `linarith` converts the certificate into a
proof term of type `False`.

Some of the behavior of `linarith` can be inspected with the option
`set_option trace.linarith true`.
However, both oracles mainly runs outside the tactic monad, so we cannot trace intermediate
steps there.

## File structure

The components of `linarith` are spread between a number of files for the sake of organization.

* `Lemmas.lean` contains proofs of some arithmetic lemmas that are used in preprocessing and in
  verification.
* `Datatypes.lean` contains data structures that are used across multiple files, along with some
  useful auxiliary functions.
* `Preprocessing.lean` contains functions used at the beginning of the tactic to transform
  hypotheses into a shape suitable for the main routine.
* `Parsing.lean` contains functions used to compute the linear structure of an expression.
* The `Oracle` folder contains files implementing the oracles that can be used to produce a
  certificate of unsatisfiability.
* `Verification.lean` contains the certificate checking functions that produce a proof of `False`.
* `Frontend.lean` contains the control methods and user-facing components of the tactic.

## Tags

linarith, nlinarith, lra, nra, Fourier-Motzkin, linear arithmetic, linear programming
-/

open Lean Elab Parser Tactic Meta
open Batteries


namespace Mathlib.Tactic.Linarith

/-! ### Config objects

The config object is defined in the frontend, instead of in `Datatypes.lean`, since the oracles must
be in context to choose a default.

-/

section

/-- A configuration object for `linarith`. -/
structure LinarithConfig : Type where
  /-- Discharger to prove that a candidate linear combination of hypothesis is zero. -/
  -- TODO There should be a def for this, rather than calling `evalTactic`?
  discharger : TacticM Unit := do evalTactic (← `(tactic| ring1))
  -- We can't actually store a `Type` here,
  -- as we want `LinarithConfig : Type` rather than ` : Type 1`,
  -- so that we can define `elabLinarithConfig : Lean.Syntax → Lean.Elab.TermElabM LinarithConfig`.
  -- For now, we simply don't support restricting the type.
  -- (restrict_type : Option Type := none)
  /-- Prove goals which are not linear comparisons by first calling `exfalso`. -/
  exfalso : Bool := true
  /-- Transparency mode for identifying atomic expressions in comparisons. -/
  transparency : TransparencyMode := .reducible
  /-- Split conjunctions in hypotheses. -/
  splitHypotheses : Bool := true
  /-- Split `≠` in hypotheses, by branching in cases `<` and `>`. -/
  splitNe : Bool := false
  /-- Override the list of preprocessors. -/
  preprocessors : List GlobalBranchingPreprocessor := defaultPreprocessors


end

/-! ### Control -/

/--
If `e` is a comparison `a R b` or the negation of a comparison `¬ a R b`, found in the target,
`getContrLemma e` returns the name of a lemma that will change the goal to an
implication, along with the type of `a` and `b`.

For example, if `e` is `(a : ℕ) < b`, returns ``(`lt_of_not_ge, ℕ)``.
-/
def getContrLemma (e : Expr) : MetaM (Name × Expr) := do
  match ← e.ineqOrNotIneq? with
  | (true, Ineq.lt, t, _) => pure (``lt_of_not_ge, t)
  | (true, Ineq.le, t, _) => pure (``le_of_not_gt, t)
  | (true, Ineq.eq, t, _) => pure (``eq_of_not_lt_of_not_gt, t)
  | (false, _, t, _) => pure (``Not.intro, t)

/--
`applyContrLemma` inspects the target to see if it can be moved to a hypothesis by negation.
For example, a goal `⊢ a ≤ b` can become `a > b ⊢ false`.
If this is the case, it applies the appropriate lemma and introduces the new hypothesis.
It returns the type of the terms in the comparison (e.g. the type of `a` and `b` above) and the
newly introduced local constant.
Otherwise returns `none`.
-/
def applyContrLemma (g : MVarId) : MetaM (Option (Expr × Expr) × MVarId) := do
  try
    let (nm, tp) ← getContrLemma (← withReducible g.getType')
    let [g] ← g.apply (← mkConst' nm) | failure
    let (f, g) ← g.intro1P
    return (some (tp, .fvar f), g)
  catch _ => return (none, g)

/-- A map of keys to values, where the keys are `Expr` up to defeq and one key can be
associated to multiple values. -/
abbrev ExprMultiMap α := Array (Expr × List α)


/-- Insert a new value into the map at key `k`. This does a defeq check with all other keys
in the map. -/
def ExprMultiMap.insert {α : Type} (self : ExprMultiMap α) (k : Expr) (v : α) :
    MetaM (ExprMultiMap α) := do
  for h : i in [:self.size] do
    if ← isDefEq self[i].1 k then
      return self.modify i fun (k, vs) => (k, v::vs)
  return self.push (k, [v])

/--
`partitionByType l` takes a list `l` of proofs of comparisons. It sorts these proofs by
the type of the variables in the comparison, e.g. `(a : ℚ) < 1` and `(b : ℤ) > c` will be separated.
Returns a map from a type to a list of comparisons over that type.
-/
def partitionByType (l : List Expr) : MetaM (ExprMultiMap Expr) :=
  l.foldlM (fun m h => do m.insert (← typeOfIneqProof h) h) #[]

/--
Given a list `ls` of lists of proofs of comparisons, `findLinarithContradiction cfg ls` will try to
prove `False` by calling `linarith` on each list in succession. It will stop at the first proof of
`False`, and fail if no contradiction is found with any list.
-/
def findLinarithContradiction (cfg : LinarithConfig) (g : MVarId) (ls : List (Expr × List Expr)) :
    MetaM (List Comp × ℕ) :=
  try
    ls.firstM (fun ⟨α, L⟩ =>
      withTraceNode `linarith (return m!"{exceptEmoji ·} running on type {α}") <|
        getCoeffs cfg.transparency g L)
  catch e => throwError "linarith failed to find a contradiction\n{g}\n{e.toMessageData}"


/--
Given a list `hyps` of proofs of comparisons, `runLinarith cfg hyps prefType`
preprocesses `hyps` according to the list of preprocessors in `cfg`.
This results in a list of branches (typically only one),
each of which must succeed in order to close the goal.

In each branch, we partition the list of hypotheses by type, and run `linarith` on each class
in the partition; one of these must succeed in order for `linarith` to succeed on this branch.
If `prefType` is given, it will first use the class of proofs of comparisons over that type.
-/
-- If it succeeds, the passed metavariable should have been assigned.
def runLinarith (cfg : LinarithConfig) (prefType : Option Expr) (g : MVarId)
    (hyps : List Expr) : MetaM Unit := do
  let singleProcess (g : MVarId) (hyps : List Expr) : MetaM Unit := g.withContext do
    linarithTraceProofs s!"after preprocessing, linarith has {hyps.length} facts:" hyps
    let mut hyp_set ← partitionByType hyps
    trace[linarith] "hypotheses appear in {hyp_set.size} different types"
    let stuff ← findLinarithContradiction cfg g hyp_set.toList
  let mut preprocessors := cfg.preprocessors
  let branches ← preprocess preprocessors g hyps
  for (g, es) in branches do
    let r ← singleProcess g es


/--
`linarith only_on hyps cfg` tries to close the goal using linear arithmetic. It fails
if it does not succeed at doing this.

* `hyps` is a list of proofs of comparisons to include in the search.
* If `only_on` is true, the search will be restricted to `hyps`. Otherwise it will use all
  comparisons in the local context.
* If `cfg.transparency := semireducible`,
  it will unfold semireducible definitions when trying to match atomic expressions.
-/
partial def linarith (cfg : LinarithConfig := {})
    (g : MVarId) : MetaM Unit := g.withContext do

  /- If we are proving a comparison goal (and not just `False`), we consider the type of the
    elements in the comparison to be the "preferred" type. That is, if we find comparison
    hypotheses in multiple types, we will run `linarith` on the goal type first.
    In this case we also receive a new variable from moving the goal to a hypothesis.
    Otherwise, there is no preferred type and no new variable; we simply change the goal to `False`.
  -/

  let (g, target_type, new_var) ← match ← applyContrLemma g with
  | (none, g) => failure
  | (some (t, v), g) => pure (g, some t, some v)

  g.withContext do
  -- set up the list of hypotheses, considering the `only_on` and `restrict_type` options
    let hyps := (← getLocalHyps).toList

    -- TODO in mathlib3 we could specify a restriction to a single type.
    -- I haven't done that here because I don't know how to store a `Type` in `LinarithConfig`.
    -- There's only one use of the `restrict_type` configuration option in mathlib3,
    -- and it can be avoided just by using `linarith only`.

    linarithTraceProofs "linarith is running on the following hypotheses:" hyps
    runLinarith cfg target_type g hyps

end Linarith


end Mathlib.Tactic
