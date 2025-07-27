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
import Mathlib.Tactic.CancelDenoms.Core

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
This is a wrapper around linarith's `getLinearCombinations` that maintains API compatibility. -/
def getCoeffs (transparency : TransparencyMode) : MVarId → List Expr → MetaM (List Comp × ℕ)
  | g, l => do
      let (comps, maxVar, _) ← Mathlib.Tactic.Linarith.getLinearCombinations transparency g l
      return (comps, maxVar)

/-- Extract the scaling factor that CancelDenoms applies to the goal expression.
Returns 1 if no scaling is applied. -/
def extractGoalScalingFactor (H : Expr) : MetaM ℕ := do
  try
    let goalType ← inferType H
    let (_, lhs) ← parseCompAndExpr goalType
    let containsDiv := lhs.containsConst fun n =>
      n = ``HDiv.hDiv || n = ``Div.div || n = ``Inv.inv || n == ``OfScientific.ofScientific
    
    if containsDiv then
      let (scalingFactor, _) ← CancelDenoms.derive lhs
      return scalingFactor
    else
      return 1
  catch _ =>
    return 1

/-- Parse the linarith structure by turning hypotheses and goal into a matrix.
Returns (List Comp, ℕ, ℕ) where the third component is the scaling factor applied to the goal. -/
partial def parseLinarithStructure (ty H : Expr) (g : MVarId)
    (cfg : TransparencyMode := .reducible) : MetaM (List Comp × ℕ × ℕ) := g.withContext do
  let hyps := H :: (← getLocalHyps).toList
  let goalScalingFactor ← extractGoalScalingFactor H
  let es ← preprocess defaultPreprocessors hyps
  let hypSet ← extractByType ty es
  let (comps, maxVar) ← getCoeffs cfg g hypSet
  return (comps, maxVar, goalScalingFactor)

end Preprocessing

section SimplexAlgorithm

-- Re-export simplex algorithm types and functions
open Mathlib.Tactic.Linarith.SimplexAlgorithm (SimplexAlgorithmException SimplexAlgorithmM)
open Mathlib.Tactic.Linarith.SimplexAlgorithm (doPivotOperation chooseEnteringVar chooseExitingVar
  choosePivots)

variable {matType : Nat → Nat → Type} [UsableInSimplexAlgorithm matType]

def checkSuccess : SimplexAlgorithmM matType Bool := do
  let tableau ← get
  let lastIdx := tableau.free.size - 1
  let feasible ← tableau.basic.size.allM (fun i _ => do
    if i ≠ 0 then
      let val := tableau.mat[(i, lastIdx)]!
      return val ≥ 0
    else
      return true
    )
  if not feasible then
    return false
  let optimal ← tableau.free.size.allM (fun j _ => do
    if j == lastIdx then
      return true
    else
      let val := tableau.mat[(0, j)]!
      return val ≤ 0)
  return optimal





/-- Runs the Simplex Algorithm inside the `SimplexAlgorithmM`. It always terminates, finding
solution if such exists. -/
def runSimplexAlgorithm : SimplexAlgorithmM matType (Rat) := do
  let mut iteration : Nat := 0
  while !(← checkSuccess) do
    iteration := iteration + 1
    Lean.Core.checkSystem decl_name%.toString
    let ⟨exitIdx, enterIdx⟩ ← choosePivots
    doPivotOperation exitIdx enterIdx
  let tableau ← get
  let lastIdx := tableau.free.size - 1
  return tableau.mat[(0, lastIdx)]!

/-- Finds a nonnegative vector `v`, such that `A v = 0` and some of its coordinates from
`strictCoords` are positive, in the case such `v` exists. If not, throws the error. The latter
prevents `linarith` from doing useless post-processing. -/
def findPositiveVector {n m : Nat} {matType : Nat → Nat → Type}
    [UsableInSimplexAlgorithm matType] (A : matType n m) :
    Lean.Meta.MetaM <| Rat := do
  -- State the linear programming problem.
  -- Using Gaussian elimination split variable into free and basic forming the tableau
  -- that will be operated by the Simplex Algorithm.
  let initTableau ← Gauss.getTableau A
  -- Run the Simplex Algorithm and extract the solution.
  let res ← runSimplexAlgorithm.run initTableau
  match res.fst with
  | .ok r =>
    return r
  | .error _e =>
    throwError "Simplex Algorithm failed"

end SimplexAlgorithm

section MatrixPreprocessing

def preprocessMaximize (matType : ℕ → ℕ → Type) [UsableInSimplexAlgorithm matType]
      (rH : Linarith.Comp) (rr : List Linarith.Comp) (maxVar : ℕ) :
      matType (maxVar + 1) (rr.length + 1) :=
    let hyps := rr ++ [rH]
    let values : List (ℕ × ℕ × ℚ) :=
      hyps.foldlIdx (init := []) fun idx cur comp =>
      if idx == rr.length then
        cur ++ comp.coeffs.map fun (var, c) =>
          (var, idx, c * -1)
      else if idx == rr.length - 1 then
        cur ++ comp.coeffs.map fun (var, c) =>
          (var, 0, c)
      else
        cur ++ comp.coeffs.map fun (var, c) =>
          (var, idx + 1, c)
    ofValues values

/-- Preprocessing for minimization: goal coefficients are kept as-is. -/
def preprocessMinimize (matType : ℕ → ℕ → Type) [UsableInSimplexAlgorithm matType]
    (rH : Linarith.Comp) (rr : List Linarith.Comp) (maxVar : ℕ) :
    matType (maxVar + 1) (rr.length + 1) :=
  let hyps := rr ++ [rH]
  let values : List (ℕ × ℕ × ℚ) :=
    hyps.foldlIdx (init := []) fun idx cur comp =>
    if idx == rr.length then
      cur ++ comp.coeffs.map fun (var, c) =>
        (var, idx, c)
    else if idx == rr.length - 1 then
      cur ++ comp.coeffs.map fun (var, c) =>
        (var, 0, c)
    else
      cur ++ comp.coeffs.map fun (var, c) =>
        (var, idx + 1, c)
  ofValues values

end MatrixPreprocessing

section BoundComputation

/-- Compute the best upper bound for maximization. -/
def bestUpperBound (rH : Linarith.Comp) (rr : List Linarith.Comp) (n : ℕ) (scalingFactor : ℕ) :
    MetaM (TSyntax `term) := do
  let A := preprocessMaximize DenseMatrix rH rr n
  let r ← findPositiveVector A
  let scaledR := if scalingFactor == 1 then r else r / scalingFactor
  return quote (-scaledR)

/-- Compute the best lower bound for minimization. -/
def bestLowerBound (rH : Linarith.Comp) (rr : List Linarith.Comp) (n : ℕ) (scalingFactor : ℕ) :
    MetaM (TSyntax `term) := do
  let A := preprocessMinimize DenseMatrix rH rr n
  let r ← findPositiveVector A
  let scaledR := if scalingFactor == 1 then r else r / scalingFactor
  return quote scaledR

end BoundComputation

section TacticImplementation

/--
Common setup for linear optimization tactics.

Handles type inference, instance synthesis, and parsing of the linear structure.
Returns `(e_exp, ty, rH, rr, n, scalingFactor)` where:
- `e_exp` is the elaborated expression
- `ty` is the type of the expression  
- `rH` is the goal vector (linear combination)
- `rr` is the list of hypothesis vectors
- `n` is the maximum variable index
- `scalingFactor` is the scaling factor from `CancelDenoms`
-/
def setupLinearOptimTactic (e_stx : Term) :
    TacticM (Expr × Expr × Linarith.Comp × List Linarith.Comp × ℕ × ℕ) := do
  let e_exp : Expr ← Elab.Tactic.elabTerm e_stx none
  let ⟨u, ty, e_exp⟩ ← inferTypeQ' e_exp -- `ty : Q(Type u)`, `e_exp : Q($ty)`
  let _i ← synthInstanceQ q(PartialOrder $ty)
  let _i ← synthInstanceQ q(Semiring $ty)
  assumeInstancesCommute
  have H : Q($e_exp < 0) := q(sorry)
  -- Turn both the hypotheses and goal into a matrix r and a number n for atoms
  let (r, n, scalingFactor) ← parseLinarithStructure ty H (← getMainGoal)
  -- Split off the goal vector rH from the matrix r and leave the hypothesis matrix rr
  let rH :: rr := r.reverse | failure
  return (e_exp, ty, rH, rr, n, scalingFactor)

/--
Common finalization for linear optimization tactics.

Takes a generated tactic syntax and:
1. Adds it as a "Try this:" suggestion to the info view
2. Executes the tactic to complete the goal
-/
def finalizeTacticWithSuggestion (tacticStx : TSyntax `tactic) : TacticM Unit := do
  -- Add suggestion using getRef for current tactic position
  Lean.Meta.Tactic.TryThis.addSuggestion (← getRef) tacticStx (header := "Try this:")
  -- Execute the tactic
  Elab.Tactic.evalTactic tacticStx

/-- The `maximize` tactic finds an upper bound for a linear expression. -/
elab "maximize" e_stx:term "with" h_stx:ident : tactic => do
  let (_e_exp, _ty, rH, rr, n, scalingFactor) ← setupLinearOptimTactic e_stx
  -- Wrap the bound computation in try-catch
  let bound ← try
    bestUpperBound rH rr n scalingFactor
  catch _e =>
    throwError "maximize: an upper bound cannot be produced for {e_stx}.\n    \
      The constraints may be inconsistent or the expression may be unbounded."
  -- Create the tactic syntax with explicit formatting
  let tacticStx ← `(tactic| have $h_stx : $e_stx ≤ $bound := by linarith)
  finalizeTacticWithSuggestion tacticStx

/-- The `minimize` tactic finds a lower bound for a linear expression. -/
elab "minimize" e_stx:term "with" h_stx:ident : tactic => do
  let (_e_exp, _ty, rH, rr, n, scalingFactor) ← setupLinearOptimTactic e_stx
  -- Wrap the bound computation in try-catch
  let bound ← try
    bestLowerBound rH rr n scalingFactor
  catch _e =>
    throwError "minimize: a lower bound cannot be produced for {e_stx}.
    The constraints may be inconsistent or the expression may be unbounded."
  -- Create the tactic syntax with explicit formatting
  let tacticStx ← `(tactic| have $h_stx : $bound ≤ $e_stx := by linarith)
  finalizeTacticWithSuggestion tacticStx

end TacticImplementation

end Mathlib.Tactic.LinearOptim
