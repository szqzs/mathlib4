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
* `parseLinarithStructure` - Parses linear constraints into matrix form
* `preprocessLinearOptim` - Converts constraints to matrix for simplex
* `computeOptimalBound` - Core function computing optimal bounds

## Implementation

The `maximize` and `minimize` tactics work by:
1. Parsing the linear constraints and target expression using `parseLinarithStructure`
2. Converting them to matrix form suitable for the simplex algorithm via `preprocessLinearOptim`
3. Finding the optimal solution using `computeOptimalBound` which calls `simplexOptimalBound`
4. Suggesting a `have` statement with the computed bound that can be proved with `linarith`

The tactics handle the duality between maximization and minimization by transforming
`minimize e` into `maximize -e` and then negating the result. The implementation uses
a dummy variable trick to extract scaling factors introduced by the preprocessing pipeline.
-/

open Lean Lean.Elab Lean.Elab.Tactic Lean.Meta
open Mathlib.Tactic.Linarith Mathlib.Tactic.Linarith.SimplexAlgorithm
open Mathlib.Tactic (getWithArg)
open Qq

namespace Mathlib.Tactic.LinearOptim

section Preprocessing

/-- Parse the linarith structure by turning hypotheses and goal into a matrix.

This function processes linear constraints through the linarith pipeline and extracts
the scaling factor introduced by the `cancelDenoms` preprocessor. It creates a dummy
hypothesis `e < z` (where `z` is a fresh variable) to capture how the expression `e`
is transformed. The preprocessor scales this to `k*e < k*z`, which becomes `k*e - k*z < 0`.
The coefficient `-k` of the dummy variable `z` gives us the scaling factor.

Returns `(comps, maxVar, goalScalingFactor) : List Comp × ℕ × ℤ` where:
- `comps` are the processed constraints with dummy terms removed
- `maxVar` is the maximum variable index (adjusted for dummy removal)
- `goalScalingFactor` is the extracted scaling factor `k` -/
partial def parseLinarithStructure (ty H : Expr)
    (cfg : TransparencyMode := .reducible) : MetaM (List Comp × ℕ × ℤ) := do
  let hyps := H :: (← getLocalHyps).toList
  let es ← Linarith.preprocessSimple Linarith.defaultLinearOptimPreprocessors hyps
  let hypSet ← es.filterM (fun h => return ty == (← typeOfIneqProof h))
  let (comps, maxVar, _) ← Mathlib.Tactic.Linarith.getLinearCombinations cfg hypSet
  -- The `computeOptimalBound` function creates a dummy variable `z`
  -- and dummy hypothesis of the form `e < z`.
  -- The `cancelDenoms` preprocessor transforms this into `k*e < k * z`, which is then
  -- normalized to `k*e - k * z < 0`. Linarith's parser treats the constant `-k`
  -- as the coefficient of a special variable with the largest index encountered.
  -- We extract this coefficient and negate it to recover the scaling factor `k`.
  -- We also strip out all the dummy `z`-terms (there should only be one, in `k*e - k * z`)
  let goalComp := comps.getLast!
  let (dummyVar, negScalingFactor) := goalComp.coeffs.head!
  let comps' := comps.map fun c ↦
    { c with coeffs := c.coeffs.filter (fun p ↦ p.1 != dummyVar) }
  return (comps', maxVar - 1, -negScalingFactor)

end Preprocessing


section MatrixPreprocessing

/-- Converts linear constraints into a matrix suitable for the simplex algorithm.

This function takes the parsed constraints from `parseLinarithStructure` and builds
a matrix for `simplexOptimalBound`. The matrix has dimensions `(maxVar + 1) × (rr.length + 1)`.

The function reorders and transforms coefficients:
- The objective function `rH` goes to the last column with negated coefficients
- The second-to-last constraint from `rr` is moved to the first column
- Other constraints maintain their relative positions

This specific ordering prepares the matrix for the simplex algorithm's expected format. -/
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

This function implements the core optimization logic, using the duality principle:
- For maximization: directly find max(e) using the simplex algorithm
- For minimization: find min(e) by computing max(-e) and negating the result

The function creates a dummy variable `z` and hypothesis `target < z` to capture
scaling factors from preprocessing. After running the simplex algorithm, it adjusts
the result by the scaling factor to get the actual bound.

The duality transformation `min(e) = -max(-e)` allows us to handle both maximize
and minimize with a single simplex implementation.

Returns the optimal bound as a rational number, or an error if the problem is
unbounded or infeasible. -/
def computeOptimalBound (e_exp : Expr) (isMaximize : Bool) (g : MVarId) :
    MetaM (Except SimplexAlgorithmException Rat) := g.withContext do
  let ⟨u, ty, e_exp⟩ ← inferTypeQ' e_exp
  let _i ← synthInstanceQ q(PartialOrder $ty)
  let _i ← synthInstanceQ q(Ring $ty) -- Use Ring to ensure negation is available
  assumeInstancesCommute
  -- To find max(e), we run the pipeline on `e`.
  -- To find min(e), we run the pipeline on `-e` and use the identity min(e) = -max(-e).
  let target_exp := if isMaximize then e_exp else q(-$e_exp)
  -- The dummy hypothesis is always `< z` (for a new dummy variable `z`) to ensure the scaling
  -- factor `k` is positive and that the Comp object represents `k*E`.
  withLocalDecl .anonymous .default ty fun (z : Q($ty)) ↦ do
  let H := q(show $target_exp < $z from sorry)
  let (comps, maxVar, scalingFactor) ← parseLinarithStructure ty H
  let rH :: rr := comps.reverse | failure
  let A := preprocessLinearOptim DenseMatrix rH rr maxVar
  match ← Linarith.SimplexAlgorithm.simplexOptimalBound A with
  | .ok r_opt =>
    let k_q : ℚ := scalingFactor
    -- This derivation is based on the solver pipeline.
    -- The pipeline takes a Comp for `k*E` and returns `r_opt = min(-(k*E))`.
    -- This can be solved to show that `max(E) = (- r_opt) / k`.
    let max_of_target := (- r_opt) / k_q
    if isMaximize then
      -- The target was `e`, so we have found `max(e)`.
      return Except.ok max_of_target
    else
      -- The target was `-e`. We found `max(-e)`.
      -- So we return `-max(-e)` to get `min(e)`.
      return Except.ok (-max_of_target)
  | .error e => return Except.error e


end BoundComputation


section TacticImplementation


/-- The `maximize` tactic finds an upper bound for a linear expression given linear constraints.

## Syntax

```lean
maximize <expression>
maximize <expression> with <identifier>
```

The first form creates an anonymous hypothesis with the computed bound.
The second form creates a hypothesis with the given identifier.

## Description

`maximize` uses the simplex algorithm to find an optimal upper bound for the given
linear expression based on the linear constraints in the local context. It generates
a `have` statement with the computed bound that is proved using `linarith`.

## Examples

### Success cases

```lean
example (x y : ℚ) (h1 : 3 * x + y < 4) (h2 : x < 2) : True := by
  maximize 4 * x + y with H
  -- Creates: have H : 4 * x + y ≤ 6 := by linarith
  trivial
```

```lean
example (x : ℚ) (h : x < 10) : True := by
  maximize x
  -- Creates: have : x ≤ 10 := by linarith
  trivial
```

### Failure cases

**Unbounded expression:**
```lean
example (x : ℚ) (h : x > 0) : True := by
  maximize x
  -- Error: maximize: an upper bound cannot be produced for x.
  --        The expression may be unbounded.
```

**Inconsistent constraints:**
```lean
example (x : ℚ) (h1 : x > 0) (h2 : x < -5) : True := by
  maximize x
  -- Error: maximize: an upper bound cannot be produced for x.
  --        The constraints may be inconsistent.
```

## See also

* `minimize` - finds a lower bound for a linear expression
-/
elab "maximize" e_stx:term h_stx:(withArg)? : tactic => do
  let e_exp : Expr ← Elab.Tactic.elabTerm e_stx none
  -- Compute the bound, handling exceptions explicitly
  match ← computeOptimalBound e_exp true (← getMainGoal) with
  | .error SimplexAlgorithmException.infeasible =>
    throwError "maximize: an upper bound cannot be produced for {e_stx}.
    The constraints may be inconsistent."
  | .error SimplexAlgorithmException.unbounded =>
    throwError "maximize: an upper bound cannot be produced for {e_stx}.
    The expression may be unbounded."
  | .ok bound =>
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

/-- The `minimize` tactic finds a lower bound for a linear expression given linear constraints.

## Syntax

```lean
minimize <expression>
minimize <expression> with <identifier>
```

The first form creates an anonymous hypothesis with the computed bound.
The second form creates a hypothesis with the given identifier.

## Description

`minimize` uses the simplex algorithm to find an optimal lower bound for the given
linear expression based on the linear constraints in the local context. It generates
a `have` statement with the computed bound that is proved using `linarith`.

## Examples

### Success cases

```lean
example (x y : ℚ) (h1 : 3 * x + y > -4) (h2 : x > -2) : True := by
  minimize 4 * x + y with H
  -- Creates: have H : -6 ≤ 4 * x + y := by linarith
  trivial
```

```lean
example (x : ℚ) (h : x > 5) : True := by
  minimize x
  -- Creates: have : 5 ≤ x := by linarith
  trivial
```

### Failure cases

**Unbounded expression:**
```lean
example (x : ℚ) (h : x < 0) : True := by
  minimize x
  -- Error: minimize: a lower bound cannot be produced for x.
  --        The expression may be unbounded.
```

**Inconsistent constraints:**
```lean
example (x : ℚ) (h1 : x < 0) (h2 : x > 5) : True := by
  minimize x
  -- Error: minimize: a lower bound cannot be produced for x.
  --        The constraints may be inconsistent.
```

## See also

* `maximize` - finds an upper bound for a linear expression
-/
elab "minimize" e_stx:term h_stx:(withArg)? : tactic => do
  let e_exp : Expr ← Elab.Tactic.elabTerm e_stx none
  -- Compute the bound, handling exceptions explicitly
  match ← computeOptimalBound e_exp false (← getMainGoal) with
  | .error SimplexAlgorithmException.infeasible =>
    throwError "minimize: a lower bound cannot be produced for {e_stx}.
    The constraints may be inconsistent."
  | .error SimplexAlgorithmException.unbounded =>
    throwError "minimize: a lower bound cannot be produced for {e_stx}.
    The expression may be unbounded."
  | .ok bound =>
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
