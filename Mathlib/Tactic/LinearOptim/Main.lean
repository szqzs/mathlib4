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
import Mathlib.Tactic.Linarith.Oracle.SimplexAlgorithm.PositiveVector
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
open Mathlib.Tactic (getWithArg)
open Qq

namespace Mathlib.Tactic.LinearOptim

section Preprocessing

/-- Parse the linarith structure by turning hypotheses and goal into a matrix.
Returns `(comps, maxVar, goalScalingFactor) : List Comp × ℕ × ℤ. -/
partial def parseLinarithStructure (ty H : Expr) (g : MVarId)
    (cfg : TransparencyMode := .reducible) : MetaM (List Comp × ℕ × ℤ) := g.withContext do
  let hyps := H :: (← getLocalHyps).toList
  let es ← Linarith.preprocessSimple Linarith.defaultLinearOptimPreprocessors hyps
  let hypSet ← es.filterM (fun h => return ty == (← typeOfIneqProof h))
  let (comps, maxVar, _) ← Mathlib.Tactic.Linarith.getLinearCombinations cfg hypSet
  -- The `computeOptimalBound` function creates a dummy hypothesis of the form `e < 1`.
  -- The `cancelDenoms` preprocessor transforms this into `k*e < k`, which is then
  -- normalized to `k*e - k < 0`. Linarith's parser treats the constant `-k`
  -- as the coefficient of a special variable with index 0.
  -- We extract this coefficient and negate it to recover the scaling factor `k`.
  let goalComp := comps.getLast!
  let scalingFactor := - goalComp.coeffs.zfind 0
  return (comps, maxVar, scalingFactor)

end Preprocessing


section MatrixPreprocessing

def preprocessLinearOptim (matType : ℕ → ℕ → Type) [UsableInSimplexAlgorithm matType]
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


end MatrixPreprocessing

section BoundComputation

/-- Compute the optimal bound (upper bound for maximization, lower bound for minimization).
Returns the optimal bound as a rational number. -/
def computeOptimalBound (e_exp : Expr) (isMaximize : Bool) (g : MVarId) : MetaM ℚ := do
  let ⟨u, ty, e_exp⟩ ← inferTypeQ' e_exp
  let _i ← synthInstanceQ q(PartialOrder $ty)
  let _i ← synthInstanceQ q(Ring $ty) -- Use Ring to ensure negation is available
  assumeInstancesCommute
  -- To find max(e), we run the pipeline on `e`.
  -- To find min(e), we run the pipeline on `-e` and use the identity min(e) = -max(-e).
  let target_exp := if isMaximize then e_exp else q(-$e_exp)
  -- The dummy hypothesis is always `< 1` to ensure the scaling factor `k` is positive
  -- and that the Comp object represents `k*E - k`.
  let H := q(show $target_exp < 1 from sorry)
  let (comps, maxVar, scalingFactor) ← parseLinarithStructure ty H g
  let rH :: rr := comps.reverse | failure
  let A := preprocessLinearOptim DenseMatrix rH rr maxVar
  let r_opt ← Linarith.SimplexAlgorithm.simplexOptimalBound A
  let k_q : ℚ := scalingFactor
  -- This derivation is based on the solver pipeline.
  -- The pipeline takes a Comp for `k*E - k` and returns `r_opt = min(-(k*E - k))`.
  -- This can be solved to show that `max(E) = (k - r_opt) / k`.
  let max_of_target := (k_q - r_opt) / k_q
  if isMaximize then
    -- The target was `e`, so we have found `max(e)`.
    return max_of_target
  else
    -- The target was `-e`. We found `max(-e)`.
    -- So we return `-max(-e)` to get `min(e)`.
    return -max_of_target


end BoundComputation


section TacticImplementation


/-- The `maximize` tactic finds an upper bound for a linear expression. -/
elab "maximize" e_stx:term h_stx:(withArg)? : tactic => do
  let e_exp : Expr ← Elab.Tactic.elabTerm e_stx none
  -- Wrap the bound computation in try-catch
  let bound ← try
    computeOptimalBound e_exp true (← getMainGoal)
  catch _ =>
    throwError "maximize: an upper bound cannot be produced for {e_stx}.\n    \
      The constraints may be inconsistent or the expression may be unbounded."
  -- Create the tactic syntax with explicit formatting
  let tacticStx ← match h_stx with
  | some h_stx =>
    let v : TSyntax `ident := ⟨← getWithArg h_stx⟩
    `(tactic| have $v : $e_stx ≤ $(quote bound) := by linarith)
  | none => `(tactic| have : $e_stx ≤ $(quote bound) := by linarith)
  -- Add suggestion using getRef for current tactic position
  Lean.Meta.Tactic.TryThis.addSuggestion (← getRef) tacticStx
  -- Execute the tactic
  Elab.Tactic.evalTactic tacticStx

/-- The `minimize` tactic finds a lower bound for a linear expression. -/
elab "minimize" e_stx:term h_stx:(withArg)? : tactic => do
  let e_exp : Expr ← Elab.Tactic.elabTerm e_stx none
  -- Wrap the bound computation in try-catch
  let bound ← try
    computeOptimalBound e_exp false (← getMainGoal)
  catch _ =>
    throwError "minimize: a lower bound cannot be produced for {e_stx}.
    The constraints may be inconsistent or the expression may be unbounded."
  -- Create the tactic syntax with explicit formatting
  let tacticStx ← match h_stx with
  | some h_stx =>
    let v : TSyntax `ident := ⟨← getWithArg h_stx⟩
    `(tactic| have $v : $(quote bound) ≤ $e_stx := by linarith)
  | none => `(tactic| have : $(quote bound) ≤ $e_stx := by linarith)
  -- Add suggestion using getRef for current tactic position
  Lean.Meta.Tactic.TryThis.addSuggestion (← getRef) tacticStx
  -- Execute the tactic
  Elab.Tactic.evalTactic tacticStx

end TacticImplementation

end Mathlib.Tactic.LinearOptim
