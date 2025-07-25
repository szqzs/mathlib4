/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Mathlib.Tactic.Linarith.Oracle.SimplexAlgorithm.Datatypes

/-!
# Gaussian Elimination algorithm

The first step of `Linarith.SimplexAlgorithm.findPositiveVector` is finding initial feasible
solution which is done by standard Gaussian Elimination algorithm implemented in this file.
-/

namespace Mathlib.Tactic.Linarith.SimplexAlgorithm.Gauss

/-- The monad for the Gaussian Elimination algorithm. -/
abbrev GaussM (n m : Nat) (matType : Nat → Nat → Type) := StateT (matType n m) Lean.CoreM

variable {n m : Nat} {matType : Nat → Nat → Type} [UsableInSimplexAlgorithm matType]

/-- Finds the best row starting from the `rowStart` with nonzero element in the column `col`.
Smart pivot selection: prefer pivots that lead to positive basic variables for better feasibility. -/
def findNonzeroRow (rowStart col : Nat) : GaussM n m matType <| Option Nat := do
  let mat ← get
  let lastCol := m - 1  -- RHS column
  
  -- Collect all candidate rows with nonzero elements
  let mut candidates : Array Nat := #[]
  for i in [rowStart:n] do
    if mat[(i, col)]! != 0 then
      candidates := candidates.push i
  
  if candidates.isEmpty then
    return .none
  
  -- Smart selection: prefer pivots that lead to non-negative basic variables (rhs/pivot ≥ 0)
  for i in candidates do
    let pivot := mat[(i, col)]!
    let rhs := -mat[(i, lastCol)]!  -- Matrix stores -1 * actual RHS
    -- Check if basic variable value (rhs/pivot) would be non-negative
    let basicVarValue := rhs / pivot
    if basicVarValue >= 0 then
      return i
  
  -- If no "good" pivot found, fall back to first available (original behavior)
  return candidates[0]!

/-- Find the best available column to use as pivot for the given row.
    Returns the column that gives the most feasible basic variable value. -/
def findBestPivotColumn (row : Nat) (availableCols : Array Nat) : GaussM n m matType <| Option Nat := do
  let mat ← get
  let lastCol := m - 1  -- RHS column
  let mut bestCol : Option Nat := .none
  let mut bestFeasibility : Option Rat := .none
  
  for col in availableCols do
    if col < lastCol && mat[(row, col)]! != 0 then  -- Don't use RHS as pivot, and must be non-zero
      let pivot := mat[(row, col)]!  
      let rhs := -mat[(row, lastCol)]!  -- Matrix stores -1 * actual RHS
      let basicVarValue := rhs / pivot
      
      match bestCol with
      | .none => 
        bestCol := .some col
        bestFeasibility := .some basicVarValue
      | .some _ =>
        let currentBest := bestFeasibility.get!
        -- Prefer feasible (>= 0) over infeasible
        if basicVarValue >= 0 && currentBest < 0 then
          bestCol := .some col
          bestFeasibility := .some basicVarValue
        -- Among feasible, prefer higher values (more slack)
        else if basicVarValue >= 0 && currentBest >= 0 && basicVarValue > currentBest then
          bestCol := .some col
          bestFeasibility := .some basicVarValue
        -- Keep current choice if it's feasible and new one isn't
  
  return bestCol

/-- Implementation of `getTableau` in `GaussM` monad. -/
def getTableauImp : GaussM n m matType <| Tableau matType := do
  let mut free : Array Nat := #[]
  let mut basic : Array Nat := #[]
  
  -- Row-wise approach: for each row, find the best available column to use as pivot
  let mut availableCols : Array Nat := Array.range (m - 1)  -- All columns except RHS
  let mut currentRow : Nat := 0

  while currentRow < n && !availableCols.isEmpty do
    Lean.Core.checkSystem decl_name%.toString
    
    match ← findBestPivotColumn currentRow availableCols with
    | .none =>
      -- No valid pivot for this row, skip it
      currentRow := currentRow + 1
      continue
    | .some pivotCol =>
      -- Remove this column from available columns
      availableCols := availableCols.filter (· != pivotCol)
      basic := basic.push pivotCol
      
      -- Find a row >= currentRow that has non-zero entry in pivotCol for swapping
      let mut pivotRowToSwap : Nat := currentRow
      for i in [currentRow:n] do
        if (← get)[(i, pivotCol)]! != 0 then
          pivotRowToSwap := i
          break
      
      -- Swap rows if needed
      if pivotRowToSwap != currentRow then
        modify fun mat => swapRows mat currentRow pivotRowToSwap
      
      let mat ← get  
      let pivotVal := mat[(currentRow, pivotCol)]!

      -- Normalize the pivot row
      modify fun mat => divideRow mat currentRow pivotVal

      -- Eliminate all other rows
      for i in [:n] do
        if i != currentRow then
          let coef := (← get)[(i, pivotCol)]!
          if coef != 0 then
            modify fun mat => subtractRow mat currentRow i coef
      
      currentRow := currentRow + 1

  -- Add remaining available columns to free
  for col in availableCols do
    free := free.push col
  -- Add RHS column as the last free variable
  free := free.push (m - 1)

  let ansMatrix : matType basic.size free.size := ← do
    let vals := getValues (← get) |>.filterMap fun (i, j, v) =>
      if j == basic[i]! then
        .none
      else
        let freeIdx := free.findIdx? (· == j) |>.get!
        .some (i, freeIdx, -v)
    
    return ofValues vals

  return ⟨basic, free, ansMatrix⟩

/--
Given matrix `A`, solves the linear equation `A x = 0` and returns the solution as a tableau where
some variables are free and others (basic) variable are expressed as linear combinations of the free
ones.
-/
def getTableau (A : matType n m) : Lean.CoreM (Tableau matType) := do
  return (← getTableauImp.run A).fst

end Mathlib.Tactic.Linarith.SimplexAlgorithm.Gauss
