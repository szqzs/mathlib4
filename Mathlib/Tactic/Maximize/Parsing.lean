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


namespace Mathlib.Tactic.Maximize
open Mathlib.Tactic.Linarith

/-! ### Config objects

The config object is defined in the frontend, instead of in `Datatypes.lean`, since the oracles must
be in context to choose a default.

-/

section


def defaultPreprocessors : List Preprocessor := [filterComparisons, removeNegations, strengthenStrictInt,
    compWithZero, cancelDenoms]

/--
`preprocess pps l` takes a list `l` of proofs of propositions.
It maps each preprocessor `pp ∈ pps` over this list.
The preprocessors are run sequentially: each receives the output of the previous one.
Note that a preprocessor may produce multiple or no expressions from each input expression,
so the size of the list may change.
-/
def preprocess' (pps : List Preprocessor) (l : List Expr) :
    MetaM (List Expr) := do
  let zz ← pps.foldlM (init := l) fun ls pp => pp.globalize.transform ls
  return (zz)

end




def extractByType (ty : Expr) : List Expr → MetaM (List Expr)
  | [] => return []
  | h :: l => do
    let l' ← extractByType ty l
    if (ty == (← typeOfIneqProof h)) then
      return h :: l'
    else
      return l'


partial def parseLinarithStructure (ty : Expr) (g : MVarId)
    (cfg : TransparencyMode := .reducible) : MetaM (List Comp × ℕ) := g.withContext do

  let hyps := (← getLocalHyps).toList

  let es ← preprocess' defaultPreprocessors hyps
  let hyp_set ← extractByType ty es
  let r ← getCoeffs cfg g hyp_set
  return r


end Maximize


end Mathlib.Tactic
