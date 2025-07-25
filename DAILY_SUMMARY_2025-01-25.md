# Daily Summary - January 25, 2025

## Branch: maxmin -> maxminfix (Dual Bug Fix: Constraint Ordering + Division Scaling)

### Problems Identified

#### Problem 1: Constraint Ordering Sensitivity
- **Core Issue**: LinearOptim tactic exhibited constraint ordering sensitivity - identical mathematical constraints in different orders produced different results
- **Specific Failure**: `(h1 : x > 0) (h2 : x < 10)` would fail completely, while `(h1 : x < 10) (h2 : x > 0)` worked fine
- **Root Cause**: Gaussian elimination algorithm in `Gauss.lean` used column-wise processing that forced suboptimal pivot choices, leading to infeasible basic variables

#### Problem 2: Division Scaling Bug
- **Core Issue**: LinearOptim tactics returned incorrect bounds for expressions involving division
- **Root Cause**: CancelDenoms preprocessing scales goal expressions by common factors to eliminate denominators, but LinearOptim didn't unscale results
- **Examples of Wrong Behavior**:
  - `x/2` with `x < 10` returned `x/2 ≤ 10` instead of correct `x/2 ≤ 5`
  - `ε/2 + ε/3` with `ε < 6` returned `ε/2 + ε/3 ≤ 30` instead of correct `ε/2 + ε/3 ≤ 5`

### Deep Technical Analysis

#### For Constraint Ordering Bug:
1. **Tableau Construction Investigation**: Discovered that the same constraints in different orders created different initial tableaux
2. **Pivot Selection Problem**: Column-wise approach (`col` then find `row`) forced algorithm to use suboptimal pivots
3. **Feasibility Issues**: Poor pivot choices led to negative basic variable values, causing `checkSuccess` to fail in feasibility check
4. **RHS Value Interpretation**: Found that matrix stores `-1 * actual RHS`, requiring `rhs = -mat[i,lastCol]` for correct basic variable values

#### For Division Scaling Bug:
1. **CancelDenoms Investigation**: Found that `CancelDenoms.derive` function scales expressions by LCM of denominators
   - For `x/2`: scaling factor = 2, transforms to `2*(x/2) = x`
   - For `ε/2 + ε/3`: scaling factor = LCM(2,3) = 6, transforms to `6*(ε/2 + ε/3) = 5ε`
2. **Preprocessing Pipeline Analysis**: Traced how scaled expressions flow through:
   - `CancelDenoms.derive` → `mkSingleCompZeroOf` → Simplex algorithm → Result
   - Simplex returns optimal value for scaled problem, but LinearOptim returned this directly without unscaling

### Major Implementation Changes

#### Core Files Modified:
- **`Mathlib/Tactic/Linarith/Oracle/SimplexAlgorithm/Gauss.lean`**: Complete rewrite of Gaussian elimination logic
- **`Mathlib/Tactic/LinearOptim/Main.lean`**: Major scaling factor tracking + minor debugging improvements

#### Fix 1: Constraint Ordering (Gauss.lean Changes):

1. **Row-wise Processing**: Complete shift from column-wise to row-wise approach
   ```lean
   -- OLD: for each column, find a row
   while row < n && col < m do
     match ← findNonzeroRow row col with...
   
   -- NEW: for each row, find the best available column  
   while currentRow < n && !availableCols.isEmpty do
     match ← findBestPivotColumn currentRow availableCols with...
   ```

2. **Smart Pivot Selection**: Added `findBestPivotColumn` function
   ```lean
   def findBestPivotColumn (row : Nat) (availableCols : Array Nat) : GaussM n m matType <| Option Nat := do
     -- Chooses column that gives most feasible basic variable value (rhs/pivot >= 0)
     -- Prefers feasible over infeasible pivots
     -- Among feasible, prefers higher values (more slack)
   ```

3. **Enhanced `findNonzeroRow`**: Upgraded to prefer feasible pivots
   ```lean
   -- Now checks basic variable feasibility: rhs/pivot >= 0
   -- Falls back to first available if no good pivot found
   ```

4. **Correct RHS Handling**: Fixed interpretation throughout
   ```lean
   let rhs := -mat[(i, lastCol)]!  -- Matrix stores -1 * actual RHS
   let basicVarValue := rhs / pivot
   ```

#### Fix 2: Division Scaling (Main.lean Changes):

1. **Added CancelDenoms Import**: 
   ```lean
   import Mathlib.Tactic.CancelDenoms.Core
   ```

2. **Added `extractGoalScalingFactor` function**:
   ```lean
   def extractGoalScalingFactor (H : Expr) : MetaM ℕ := do
     -- Extracts scaling factor from CancelDenoms.derive before preprocessing
     -- Returns 1 if no scaling needed, otherwise LCM of denominators
   ```

3. **Modified `parseLinarithStructure`**:
   ```lean
   -- OLD: returns (List Comp × ℕ)
   -- NEW: returns (List Comp × ℕ × ℕ) -- third component is scaling factor
   let goalScalingFactor ← extractGoalScalingFactor H
   return (comps, maxVar, goalScalingFactor)
   ```

4. **Updated `bestUpperBound` and `bestLowerBound`**:
   ```lean
   def bestUpperBound (rH : Linarith.Comp) (rr : List Linarith.Comp) (n : ℕ) (scalingFactor : ℕ) :=
     let r ← findPositiveVector A strictIndexes
     -- Divide by scaling factor to get correct bound for original (unscaled) goal
     let scaledR := if scalingFactor == 1 then r else r / scalingFactor
     return quote (-scaledR)
   ```

5. **Modified tactic implementations**:
   ```lean
   -- Both maximize and minimize now extract and use scaling factors
   let (r, n, scalingFactor) ← parseLinarithStructure ty H (← getMainGoal)
   let bound ← bestUpperBound rH rr n scalingFactor  -- Pass scaling factor
   ```

#### Additional LinearOptim Improvements:
- Improved `checkSuccess` function with better variable naming and structure
- Added iteration counter in `runSimplexAlgorithm` for debugging
- Minor code style improvements

### Algorithm Impact

#### Before (Column-wise):
- Process columns sequentially, forced to use first available row
- No consideration of basic variable feasibility
- Constraint order determines which pivots are available
- `(x > 0, x < 10)` → poor initial pivots → infeasible basic variables → failure

#### After (Row-wise with Smart Selection):
- Process rows sequentially, choose best available column for each row
- Actively prefer pivots that create feasible basic variables
- Constraint order doesn't affect pivot quality
- Both `(x > 0, x < 10)` and `(x < 10, x > 0)` → optimal pivots → feasible solution

### Testing Results

#### Fix 1: Constraint Ordering Bug Resolved:
- ✅ `(h1 : x > 0) (h2 : x < 10)`: Now works (previously failed completely)
- ✅ `(h1 : x < 10) (h2 : x > 0)`: Still works (maintains compatibility)  
- ✅ Both orderings now produce identical bounds
- ✅ No regression in bound quality - algorithm finds same optimal values

#### Fix 2: Division Scaling Bug Resolved:
- ✅ `x/2` with `x < 10` now correctly returns `x/2 ≤ 5` (was `x/2 ≤ 10`)
- ✅ `ε/2 + ε/3` with `ε < 6` now correctly returns `ε/2 + ε/3 ≤ 5` (was `ε/2 + ε/3 ≤ 30`)
- ✅ `0.5 * x` with `x < 10` now correctly returns `0.5 * x ≤ 5`
- ✅ Complex division: `x/2` with `x + y < 10, y > 4` correctly returns `x/2 ≤ 3`
- ✅ Both `maximize` and `minimize` tactics work correctly with division expressions

#### Combined Impact:
- ✅ Division expressions now work with both constraint orderings
- ✅ Mathematically correct bounds for all division cases
- ✅ No regressions in existing integer-coefficient cases

### Mathematical Correctness
- **Gaussian Elimination**: Algorithm now chooses mathematically optimal pivots regardless of input order
- **Feasibility Preservation**: Smart pivot selection maintains basic variable feasibility throughout elimination
- **Optimal Bounds**: Row-wise approach with feasibility preference finds same tight bounds as working constraint orders

### Test Suite Impact
- Many tests that expected failures due to constraint ordering now pass
- Tests expecting specific bounds remain correct (no change in mathematical optimality)
- Constraint-ordering-sensitive tests now work in both directions

### Performance & Robustness
- **Robustness**: Eliminates a major source of tactic failures (constraint ordering sensitivity)
- **Performance**: Minimal impact - same computational complexity, just better pivot choices
- **Reliability**: Users no longer need to worry about constraint input order

### Status: COMPLETE ✅
- Constraint ordering sensitivity completely eliminated
- Algorithm maintains mathematical correctness and bound optimality  
- No regressions in existing functionality
- Both maximize and minimize tactics benefit from improved robustness

### Impact
These dual fixes resolve two major issues in LinearOptim tactics:

1. **Constraint Ordering Fix**: Eliminates a critical usability issue where constraint input order determined success/failure. Users can now write constraints in natural order without worrying about internal algorithm limitations.

2. **Division Scaling Fix**: Resolves a fundamental correctness issue where division bounds were mathematically incorrect. Users can now trust that expressions involving fractions return accurate bounds.

Together, these fixes make LinearOptim tactics significantly more robust, reliable, and mathematically sound. The tactics now handle both ordering sensitivity and division expressions correctly, making them suitable for real-world use cases involving fractional linear programming problems.