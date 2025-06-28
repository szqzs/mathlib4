/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuli Chen, Robert Y. Lewis, Heather Macbeth, Siqing Zhang, Runtian Zhou
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linarith.Verification
import Mathlib.Tactic.Polyrith
import Mathlib.Data.Ineq
import Mathlib.Util.Qq
import Mathlib.Control.Basic
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.Ring.Basic
import Lean.Meta.Basic

/-!
# Maximize Tactic

This file implements a `maximize` tactic that finds upper bounds for linear expressions
given linear constraints using the simplex algorithm.

## Main declarations

* `maximize` - The main tactic that finds an upper bound for a linear expression
* `findPositiveVectorS` - Finds a positive vector solution using simplex algorithm
* `runSimplexAlgorithmS` - Core simplex algorithm implementation

## Implementation Notes

The tactic works by:
1. Parsing the linear constraints and target expression
2. Converting them to matrix form suitable for the simplex algorithm
3. Finding the optimal solution using simplex with Bland's rule for pivoting
4. Suggesting a `have` statement with the computed bound

## Algorithm Overview

The certificate search is reduced to finding a nonnegative vector `v` such that some coordinates
from strict inequalities are positive and `A v = 0`. This is solved using:

1. Translation to a Linear Programming problem
2. Gaussian elimination to get initial tableau
3. Simplex algorithm with Bland's rule until solution is found
-/

open Mathlib
open Mathlib.Tactic
open Lean
open Meta
open Qq
open Parser.Category
open Elab
open Tactic
open Batteries

open Mathlib.Tactic.Linarith.SimplexAlgorithm
open Mathlib.Tactic.Linarith

namespace Mathlib.Tactic.Maximize

-- ========== PARSING AND PREPROCESSING ==========

section
-- The default preprocessor throws away non-linear-inequality hypothesis, push negations, turn
-- inequality into ≤, move terms to the left hand side, cancel denominators
def defaultPreprocessors : List Preprocessor := [filterComparisons, removeNegations,
  strengthenStrictInt, compWithZero, cancelDenoms]

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

-- This step extract the type of the terms in the hypothesis
def extractByType (ty : Expr) : List Expr → MetaM (List Expr)
  | [] => return []
  | h :: l => do
    let l' ← extractByType ty l
    if (ty == (← typeOfIneqProof h)) then
      return h :: l'
    else
      return l'

/--
`getCoeffs` extracts linear combinations from a list of inequality proofs.
This is the core function that converts hypothesis proofs into the coefficient matrix
needed for the simplex algorithm.
-/
def getCoeffs (transparency : TransparencyMode) : MVarId → List Expr → MetaM (List Comp × ℕ)
  | _, [] => throwError "no args to linarith"
  | _, l@(h::_) => do
      Lean.Core.checkSystem decl_name%.toString
      -- for the elimination to work properly, we must add a proof of `-1 < 0` to the list,
      -- along with negated equality proofs.
      let l' ← addNegEqProofs l
      let inputs := (← mkNegOneLtZeroProof (← typeOfIneqProof h))::l'.reverse
      trace[linarith.detail] "inputs:{indentD <| toMessageData (← inputs.mapM inferType)}"
      let (comps, max_var) ←
        linearFormsAndMaxVar transparency inputs
      trace[linarith.detail] "comps:{indentD <| toMessageData comps}"
      return (comps, max_var)

-- This step turns the hypothesis and goal into a matrix
partial def parseLinarithStructure (ty H : Expr) (g : MVarId)
    (cfg : TransparencyMode := .reducible) : MetaM (List Comp × ℕ) := g.withContext do
  let hyps := H :: (← getLocalHyps).toList
  let es ← preprocess' defaultPreprocessors hyps
  let hyp_set ← extractByType ty es
-- This getCoeffs is the key function in this def
  let r ← getCoeffs cfg g hyp_set
  return r

-- ========== SIMPLEX ALGORITHM IMPLEMENTATION ==========

/-- An exception in the `SimplexAlgorithmM` monad. -/
inductive SimplexAlgorithmException
  /-- The solution is infeasible. -/
  | infeasible : SimplexAlgorithmException

/-- The monad for the Simplex Algorithm. -/
abbrev SimplexAlgorithmM (matType : Nat → Nat → Type) [UsableInSimplexAlgorithm matType] :=
  ExceptT SimplexAlgorithmException <| StateT (Tableau matType) Lean.CoreM

variable {matType : Nat → Nat → Type} [UsableInSimplexAlgorithm matType]

/--
Given indexes `exitIdx` and `enterIdx` of exiting and entering variables in the `basic` and `free`
arrays, performs pivot operation, i.e. expresses one through the other and makes the free one basic
and vice versa.
-/
def doPivotOperation (exitIdx enterIdx : Nat) : SimplexAlgorithmM matType Unit :=
  modify fun s : Tableau matType => Id.run do
    let mut mat := s.mat
    let intersectCoef := mat[(exitIdx, enterIdx)]!

    for i in [:s.basic.size] do
      if i == exitIdx then
        continue
      let coef := mat[(i, enterIdx)]! / intersectCoef
      if coef != 0 then
        mat := subtractRow mat exitIdx i coef
      mat := setElem mat i enterIdx coef
    mat := setElem mat exitIdx enterIdx (-1)
    mat := divideRow mat exitIdx (-intersectCoef)

    let newBasic := s.basic.set! exitIdx s.free[enterIdx]!
    let newFree := s.free.set! enterIdx s.basic[exitIdx]!

    have hb : newBasic.size = s.basic.size := by apply Array.size_setIfInBounds
    have hf : newFree.size = s.free.size := by apply Array.size_setIfInBounds

    return (⟨newBasic, newFree, hb ▸ hf ▸ mat⟩ : Tableau matType)

/--
Check if the solution is found: the objective function is positive and all basic variables are
nonnegative.
-/
def checkSuccessS : SimplexAlgorithmM matType Bool := do
  let tableau ← get
  trace[debug] "checkSuccessS: Current matrix is {getValues tableau.mat}"
  let lastIdx := tableau.free.size - 1
  -- First check feasibility: all basic variables must be non-negative
  -- check last cloumn
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

/--
Chooses an entering variable: among the variables with a positive coefficient in the objective
function, the one with the smallest index (in the initial indexing).
-/
def chooseEnteringVar : SimplexAlgorithmM matType Nat := do
  let mut enterIdxOpt : Option Nat := .none -- index of entering variable in the `free` array
  let mut minIdx := 0
  for i in [:(← get).free.size - 1] do
    if (← get).mat[(0, i)]! > 0 &&
        (enterIdxOpt.isNone || (← get).free[i]! < minIdx) then
      enterIdxOpt := i
      minIdx := (← get).free[i]!

  /- If there is no such variable the solution does not exist for sure. -/
  match enterIdxOpt with
  | .none => throwThe SimplexAlgorithmException SimplexAlgorithmException.infeasible
  | .some enterIdx => return enterIdx

/--
Chooses an exiting variable: the variable imposing the strictest limit on the increase of the
entering variable, breaking ties by choosing the variable with smallest index.
-/
def chooseExitingVar (enterIdx : Nat) : SimplexAlgorithmM matType Nat := do
  let mut exitIdxOpt : Option Nat := .none -- index of entering variable in the `basic` array
  let mut minCoef := 0
  let mut minIdx := 0
  for i in [1:(← get).basic.size] do
    if (← get).mat[(i, enterIdx)]! >= 0 then
      continue
    let lastIdx := (← get).free.size - 1
    let coef := -(← get).mat[(i, lastIdx)]! / (← get).mat[(i, enterIdx)]!
    if exitIdxOpt.isNone || coef < minCoef ||
        (coef == minCoef && (← get).basic[i]! < minIdx) then
      exitIdxOpt := i
      minCoef := coef
      minIdx := (← get).basic[i]!
  return exitIdxOpt.get! -- such variable always exists because our problem is bounded

/--
Chooses entering and exiting variables using
[Bland's rule](https://en.wikipedia.org/wiki/Bland%27s_rule) that guarantees that the Simplex
Algorithm terminates.
-/
def choosePivots : SimplexAlgorithmM matType (Nat × Nat) := do
  let enterIdx ← chooseEnteringVar
  let exitIdx ← chooseExitingVar enterIdx
  return ⟨exitIdx, enterIdx⟩

/--
Runs the Simplex Algorithm inside the `SimplexAlgorithmM`. It always terminates, finding solution if
such exists.
-/
def runSimplexAlgorithmS : SimplexAlgorithmM matType (Rat) := do
  while !(← checkSuccessS) do
    Lean.Core.checkSystem decl_name%.toString
    let ⟨exitIdx, enterIdx⟩ ← choosePivots
    doPivotOperation exitIdx enterIdx
  let tableau ← get
  let lastIdx := tableau.free.size - 1
  trace[debug] "entry is {tableau.mat[(0, lastIdx)]!}"
  return tableau.mat[(0, lastIdx)]!

-- ========== POSITIVE VECTOR FINDING ==========


/-- Extracts target vector from the tableau, putting auxiliary variables aside. -/
def extractSolution (tableau : Tableau matType) : Array Rat := Id.run do
  let mut ans : Array Rat := Array.replicate (tableau.basic.size + tableau.free.size - 3) 0
  for h : i in [1:tableau.basic.size] do
    ans := ans.set! (tableau.basic[i] - 2) <| tableau.mat[(i, tableau.free.size - 1)]!
  return ans

/--
Finds a nonnegative vector `v`, such that `A v = 0` and some of its coordinates from
`strictCoords` are positive, in the case such `v` exists. If not, throws the error. The latter
prevents `linarith` from doing useless post-processing.
-/
def findPositiveVectorS {n m : Nat} {matType : Nat → Nat → Type} [UsableInSimplexAlgorithm matType]
    (A : matType n m) (strictIndexes : List Nat) : Lean.Meta.MetaM <| Rat := do
  /- State the linear programming problem. -/
  /- Using Gaussian elimination split variable into free and basic forming the tableau that will be
  operated by the Simplex Algorithm. -/
  -- we don't need to use stateLP anymore
  let initTableau ← Gauss.getTableau A
  /- Run the Simplex Algorithm and extract the solution. -/
  let res ← runSimplexAlgorithmS.run initTableau
  match res.fst with
  | .ok r => return r
  | .error e => throwError "Simplex Algorithm failed"

-- ========== MATRIX PREPROCESSING FOR SIMPLEX ==========

def preprocessS (matType : ℕ → ℕ → Type) [UsableInSimplexAlgorithm matType] (rH : Linarith.Comp)
    (rr : List Linarith.Comp) (maxVar : ℕ) : matType (maxVar + 1) (rr.length + 1) × List Nat :=
  -- dbg_trace "rH length is {rr.length}"
  let hyps := rr ++ [rH]
  let values : List (ℕ × ℕ × ℚ) := hyps.foldlIdx (init := []) fun idx cur comp =>
    if idx == rr.length then
      -- special handling for the goal
      cur ++ comp.coeffs.map fun (var, c) =>
        (var, idx, c * -1)  -- goal
    else if idx == rr.length - 1 then
      cur ++ comp.coeffs.map fun (var, c) =>
        (var, 0, c)  -- let -1 < 0 be the first column
    else
      -- normal handling for all other rows
      cur ++ comp.coeffs.map fun (var, c) =>
        (var, idx + 1, c)
  let strictIndexes := hyps.findIdxs (·.str == Ineq.lt)
  -- dbg_trace values
  (ofValues (values), strictIndexes)

-- ========== MAIN BOUND COMPUTATION ==========

def bestBound (rH : Linarith.Comp) (rr : List Linarith.Comp) (n : ℕ) :
    MetaM (TSyntax `term) := do
  trace[debug] "there are {n} atoms"
  trace[debug] "maximizing {rH}, hypotheses are {rr}"
  let (A, strictIndexes) := preprocessS DenseMatrix rH rr n
  let r ← findPositiveVectorS A strictIndexes
  return quote (-r)

-- ========== MAIN TACTIC IMPLEMENTATION ==========

elab "maximize" e_stx:term "with" h_stx:ident : tactic => do
  let e_exp : Expr ← Elab.Tactic.elabTerm e_stx none
  let ⟨u, ty, e_exp⟩ ← inferTypeQ' e_exp -- `ty : Q(Type u)`, `e_exp : Q($ty)`
  -- let ty ← inferType e_exp -- `ty : Expr`
  let i ← synthInstanceQ q(PartialOrder $ty)
  let i ← synthInstanceQ q(Semiring $ty)
  assumeInstancesCommute
  have H : Q($e_exp < 0) := q(sorry)
  -- This step turns both the hypotheses and goal into a matrix r and a number n for atoms
  let (r, n) ← parseLinarithStructure ty H (← getMainGoal)
  -- This step splits off the goal vector rH from the matrix r and leave the hypothesis matrix rr
  let rH :: rr := r.reverse | failure
  -- Wrap the bound computation in try-catch
  let bound ← try
    bestBound rH rr n
  catch e =>
    -- Check if it's a SimplexAlgorithm failure or similar
    throwError "maximize: an upper bound cannot be produced for {e_stx}.
    The constraints may be inconsistent or the expression may be unbounded."
  -- Create the tactic syntax with explicit formatting
  let tacticStx ← `(tactic| have $h_stx : $e_stx ≤ $bound := by linarith)
  -- Add suggestion using getRef for current tactic position
  Lean.Meta.Tactic.TryThis.addSuggestion (← getRef) tacticStx (header := "Try this:")
  -- Execute the tactic
  Elab.Tactic.evalTactic tacticStx

end Mathlib.Tactic.Maximize

/-Below are the test examples-/
-- set_option trace.debug true
set_option linter.unusedVariables false

example {x y : ℚ} (h1 : 3 * x + y < 4) (h2 : x < 2) : True := by
  maximize 4 * x + y with H
  -- should have 6
  trivial

example {x y : ℚ} (h1 : 4 * x + 2 * y < 4) (h2 : x + y < 2) : True := by
  maximize 5 * x + 3 * y with H
  -- should have 6
  trivial

example {x y : ℚ} (h1 : 3 * x + y ≤ 7) (h2 : x < 6) : True := by
  maximize 5 * x + 3 * y with H
  -- in this case should be unable to produce an upper bound,
  -- should give an error explaining this to the user
  sorry

example {x y z : ℚ} (h1 : x + y < 7) (h2 : 3 * y + 4 * z < 2) (h3 : x - y + z < 1)
  : True := by
  maximize x - y + z with H
  -- should have 1
  trivial

example {x y z : ℚ} (h1 : x + y + z < 7) (h2 : x + 3 * y + 4 * z < 2) (h3 : x + 10 * y + z < 1)
  : True := by
  maximize x + 5 * y + 2 * z with H
  -- should have 28 / 9
  trivial

example {x y z : ℚ} (h1 : x + y + 2 * z > 7) (h2 : x + 3 * y + 4 * z > 2)
  (h3 : x + 10 * y + z > 1) : True := by
  maximize - x - 5 * y - 2 * z with T
  -- should have - 18 /5
  trivial

example {x y z w : ℚ} (h : x < 1) : True := by
  maximize x with F
  -- should have 1
  trivial

example {x y : ℚ} (h1 : x + y < 10) (h2 : x + 11 * y < 9) : True := by
  maximize x + 7 * y with H
  -- should have 47 / 5
  trivial

example {x y : ℚ} (h1 : -2 * x - y < 10) (h2 : -x - 11 * y < 9) : True
  := by
    maximize - x - 7 * y with H
    -- should have 157 / 21
    trivial

example {x y : ℚ} (h1 : -2 * x - y < 10) (h2 : -x - 11 * y < 9) :
∃ z : ℚ, (z < 157 / 20) ∧ (- x - 7 * y ≤ z)
  := by
  maximize -x - 7 * y with H
  exact ⟨157 / 21, by linarith, H⟩
