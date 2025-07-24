/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuli Chen, Robert Y. Lewis, Heather Macbeth, Siqing Zhang, Runtian Zhou
-/
import Lean.Meta.Basic
import Mathlib.Control.Basic
import Mathlib.Data.Ineq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.Linarith.Verification
import Mathlib.Tactic.Polyrith
import Mathlib.Tactic.Ring.Basic
import Mathlib.Util.Qq

/-!
# Linear Optimization Tactics

This file implements `maximize` and `minimize` tactics that find upper and lower
bounds for linear expressions given linear constraints using the simplex algorithm.

## Main declarations

* `maximize` - Finds an upper bound for a linear expression
* `minimize` - Finds a lower bound for a linear expression
* `findPositiveVector` - Finds a positive vector solution using simplex algorithm
* `runSimplexAlgorithm` - Core simplex algorithm implementation

## Implementation

Both tactics work by:
1. Parsing the linear constraints and target expression
2. Converting them to matrix form suitable for the simplex algorithm
3. Finding the optimal solution using simplex with Bland's rule for pivoting
4. Suggesting a `have` statement with the computed bound

The certificate search is reduced to finding a nonnegative vector `v` such that some
coordinates from strict inequalities are positive and `A v = 0`. This is solved using:

1. Translation to a Linear Programming problem
2. Gaussian elimination to get initial tableau
3. Simplex algorithm with Bland's rule until solution is found
-/

open Lean Lean.Elab Lean.Elab.Tactic Lean.Meta
open Mathlib.Tactic.Linarith Mathlib.Tactic.Linarith.SimplexAlgorithm
open Qq

namespace Mathlib.Tactic.LinearOptim

section Preprocessing

/-- The default preprocessors for the linear optimization tactics.
Throws away non-linear-inequality hypotheses, pushes negations, turns inequalities into ≤,
moves terms to the left hand side, and cancels denominators. -/
def defaultPreprocessors : List Preprocessor :=
  [filterComparisons, removeNegations, strengthenStrictInt, compWithZero, cancelDenoms]

/-- `preprocess pps l` takes a list `l` of proofs of propositions.
It maps each preprocessor `pp ∈ pps` over this list.
The preprocessors are run sequentially: each receives the output of the previous one.
Note that a preprocessor may produce multiple or no expressions from each input expression,
so the size of the list may change. -/
def preprocess (pps : List Preprocessor) (l : List Expr) : MetaM (List Expr) := do
  let result ← pps.foldlM (init := l) fun ls pp => pp.globalize.transform ls
  return result

/-- Extract expressions from a list that have the specified type. -/
def extractByType (ty : Expr) : List Expr → MetaM (List Expr)
  | [] => return []
  | h :: l => do
    let l' ← extractByType ty l
    if ty == (← typeOfIneqProof h) then
      return h :: l'
    else
      return l'

/-- `getCoeffs` extracts linear combinations from a list of inequality proofs.
This is the core function that converts hypothesis proofs into the coefficient matrix
needed for the simplex algorithm. -/
def getCoeffs (transparency : TransparencyMode) : MVarId → List Expr → MetaM (List Comp × ℕ)
  | _, [] => throwError "no args to linarith"
  | _, l@(h::_) => do
      Lean.Core.checkSystem decl_name%.toString
      -- For the elimination to work properly, we must add a proof of `-1 < 0` to the list,
      -- along with negated equality proofs.
      let l' ← addNegEqProofs l
      let inputs := (← mkNegOneLtZeroProof (← typeOfIneqProof h))::l'.reverse
      trace[linarith.detail] "inputs:{indentD <| toMessageData (← inputs.mapM inferType)}"
      let (comps, maxVar) ← linearFormsAndMaxVar transparency inputs
      trace[linarith.detail] "comps:{indentD <| toMessageData comps}"
      return (comps, maxVar)

/-- Parse the linarith structure by turning hypotheses and goal into a matrix. -/
partial def parseLinarithStructure (ty H : Expr) (g : MVarId)
    (cfg : TransparencyMode := .reducible) : MetaM (List Comp × ℕ) := g.withContext do
  let hyps := H :: (← getLocalHyps).toList
  let es ← preprocess defaultPreprocessors hyps
  let hypSet ← extractByType ty es
  -- This getCoeffs is the key function in this definition
  let r ← getCoeffs cfg g hypSet
  return r

end Preprocessing

section SimplexAlgorithm

-- Re-export simplex algorithm types and functions
open Mathlib.Tactic.Linarith.SimplexAlgorithm (SimplexAlgorithmException SimplexAlgorithmM)
open Mathlib.Tactic.Linarith.SimplexAlgorithm (doPivotOperation chooseEnteringVar chooseExitingVar
  choosePivots)

variable {matType : Nat → Nat → Type} [UsableInSimplexAlgorithm matType]

/-- Check if the solution is found: the objective function is positive and all basic variables are
nonnegative. -/
def checkSuccess : SimplexAlgorithmM matType Bool := do
  let tableau ← get
  trace[debug] "checkSuccess: Current matrix is {getValues tableau.mat}"
  let lastIdx := tableau.free.size - 1
  -- First check feasibility: all basic variables must be non-negative
  -- check last column
  let feasible ← tableau.basic.size.allM (fun i _ => do
    if i ≠ 0 then
      return tableau.mat[(i, lastIdx)]! ≥ 0
    else
      return true
    )
  if not feasible then return false
  -- Check optimality: all reduced costs should be ≤ 0 for maximization
  -- (Skip the last column which is RHS)
  -- check first row
  tableau.free.size.allM (fun j _ => do
    if j == lastIdx then return true  -- Skip RHS column
    return tableau.mat[(0, j)]! ≤ 0)  -- All reduced costs ≤ 0





/-- Runs the Simplex Algorithm inside the `SimplexAlgorithmM`. It always terminates, finding
solution if such exists. -/
def runSimplexAlgorithm : SimplexAlgorithmM matType (Rat) := do
  while !(← checkSuccess) do
    Lean.Core.checkSystem decl_name%.toString
    let ⟨exitIdx, enterIdx⟩ ← choosePivots
    doPivotOperation exitIdx enterIdx
  let tableau ← get
  let lastIdx := tableau.free.size - 1
  trace[debug] "entry is {tableau.mat[(0, lastIdx)]!}"
  return tableau.mat[(0, lastIdx)]!

/-- Finds a nonnegative vector `v`, such that `A v = 0` and some of its coordinates from
`strictCoords` are positive, in the case such `v` exists. If not, throws the error. The latter
prevents `linarith` from doing useless post-processing. -/
def findPositiveVector {n m : Nat} {matType : Nat → Nat → Type}
    [UsableInSimplexAlgorithm matType] (A : matType n m) (_strictIndexes : List Nat) :
    Lean.Meta.MetaM <| Rat := do
  -- State the linear programming problem.
  -- Using Gaussian elimination split variable into free and basic forming the tableau
  -- that will be operated by the Simplex Algorithm.
  let initTableau ← Gauss.getTableau A
  -- Run the Simplex Algorithm and extract the solution.
  let res ← runSimplexAlgorithm.run initTableau
  match res.fst with
  | .ok r => return r
  | .error _e => throwError "Simplex Algorithm failed"

end SimplexAlgorithm

section MatrixPreprocessing

/-- Preprocessing for maximization: goal coefficients are negated. -/
def preprocessMaximize (matType : ℕ → ℕ → Type) [UsableInSimplexAlgorithm matType]
    (rH : Linarith.Comp) (rr : List Linarith.Comp) (maxVar : ℕ) :
    matType (maxVar + 1) (rr.length + 1) × List Nat :=
  let hyps := rr ++ [rH]
  let values : List (ℕ × ℕ × ℚ) :=
    hyps.foldlIdx (init := []) fun idx cur comp =>
    if idx == rr.length then
      -- Special handling for the goal (maximize: negate coefficients)
      cur ++ comp.coeffs.map fun (var, c) =>
        (var, idx, c * -1)  -- goal
    else if idx == rr.length - 1 then
      cur ++ comp.coeffs.map fun (var, c) =>
        (var, 0, c)  -- let -1 < 0 be the first column
    else
      -- Normal handling for all other rows
      cur ++ comp.coeffs.map fun (var, c) =>
        (var, idx + 1, c)
  let strictIndexes := hyps.findIdxs (·.str == Ineq.lt)
  (ofValues values, strictIndexes)

/-- Preprocessing for minimization: goal coefficients are kept as-is. -/
def preprocessMinimize (matType : ℕ → ℕ → Type) [UsableInSimplexAlgorithm matType]
    (rH : Linarith.Comp) (rr : List Linarith.Comp) (maxVar : ℕ) :
    matType (maxVar + 1) (rr.length + 1) × List Nat :=
  let hyps := rr ++ [rH]
  let values : List (ℕ × ℕ × ℚ) :=
    hyps.foldlIdx (init := []) fun idx cur comp =>
    if idx == rr.length then
      -- Special handling for the goal (minimize: keep coefficients as-is)
      cur ++ comp.coeffs.map fun (var, c) =>
        (var, idx, c)  -- goal
    else if idx == rr.length - 1 then
      cur ++ comp.coeffs.map fun (var, c) =>
        (var, 0, c)  -- let -1 < 0 be the first column
    else
      -- Normal handling for all other rows
      cur ++ comp.coeffs.map fun (var, c) =>
        (var, idx + 1, c)
  let strictIndexes := hyps.findIdxs (·.str == Ineq.lt)
  (ofValues values, strictIndexes)

end MatrixPreprocessing

section BoundComputation

/-- Compute the best upper bound for maximization. -/
def bestUpperBound (rH : Linarith.Comp) (rr : List Linarith.Comp) (n : ℕ) :
    MetaM (TSyntax `term) := do
  trace[debug] "there are {n} atoms"
  trace[debug] "maximizing {rH}, hypotheses are {rr}"
  let (A, strictIndexes) := preprocessMaximize DenseMatrix rH rr n
  let r ← findPositiveVector A strictIndexes
  return quote (-r)

/-- Compute the best lower bound for minimization. -/
def bestLowerBound (rH : Linarith.Comp) (rr : List Linarith.Comp) (n : ℕ) :
    MetaM (TSyntax `term) := do
  trace[debug] "there are {n} atoms"
  trace[debug] "minimizing {rH}, hypotheses are {rr}"
  let (A, strictIndexes) := preprocessMinimize DenseMatrix rH rr n
  let r ← findPositiveVector A strictIndexes
  return quote r

end BoundComputation

section TacticImplementation

/-- The `maximize` tactic finds an upper bound for a linear expression. -/
elab "maximize" e_stx:term "with" h_stx:ident : tactic => do
  let e_exp : Expr ← Elab.Tactic.elabTerm e_stx none
  let ⟨u, ty, e_exp⟩ ← inferTypeQ' e_exp -- `ty : Q(Type u)`, `e_exp : Q($ty)`
  let _i ← synthInstanceQ q(PartialOrder $ty)
  let _i ← synthInstanceQ q(Semiring $ty)
  assumeInstancesCommute
  have H : Q($e_exp < 0) := q(sorry)
  -- Turn both the hypotheses and goal into a matrix r and a number n for atoms
  let (r, n) ← parseLinarithStructure ty H (← getMainGoal)
  -- Split off the goal vector rH from the matrix r and leave the hypothesis matrix rr
  let rH :: rr := r.reverse | failure
  -- Wrap the bound computation in try-catch
  let bound ← try
    bestUpperBound rH rr n
  catch _e =>
    throwError "maximize: an upper bound cannot be produced for {e_stx}.
    The constraints may be inconsistent or the expression may be unbounded."
  -- Create the tactic syntax with explicit formatting
  let tacticStx ← `(tactic| have $h_stx : $e_stx ≤ $bound := by linarith)
  -- Add suggestion using getRef for current tactic position
  Lean.Meta.Tactic.TryThis.addSuggestion (← getRef) tacticStx (header := "Try this:")
  -- Execute the tactic
  Elab.Tactic.evalTactic tacticStx

/-- The `minimize` tactic finds a lower bound for a linear expression. -/
elab "minimize" e_stx:term "with" h_stx:ident : tactic => do
  let e_exp : Expr ← Elab.Tactic.elabTerm e_stx none
  let ⟨u, ty, e_exp⟩ ← inferTypeQ' e_exp -- `ty : Q(Type u)`, `e_exp : Q($ty)`
  let _i ← synthInstanceQ q(PartialOrder $ty)
  let _i ← synthInstanceQ q(Semiring $ty)
  assumeInstancesCommute
  have H : Q($e_exp < 0) := q(sorry)
  -- Turn both the hypotheses and goal into a matrix r and a number n for atoms
  let (r, n) ← parseLinarithStructure ty H (← getMainGoal)
  -- Split off the goal vector rH from the matrix r and leave the hypothesis matrix rr
  let rH :: rr := r.reverse | failure
  -- Wrap the bound computation in try-catch
  let bound ← try
    bestLowerBound rH rr n
  catch _e =>
    throwError "minimize: a lower bound cannot be produced for {e_stx}.
    The constraints may be inconsistent or the expression may be unbounded."
  -- Create the tactic syntax with explicit formatting
  let tacticStx ← `(tactic| have $h_stx : $bound ≤ $e_stx := by linarith)
  -- Add suggestion using getRef for current tactic position
  Lean.Meta.Tactic.TryThis.addSuggestion (← getRef) tacticStx (header := "Try this:")
  -- Execute the tactic
  Elab.Tactic.evalTactic tacticStx

end TacticImplementation

end Mathlib.Tactic.LinearOptim


