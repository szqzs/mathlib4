/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Mathlib.Tactic.Linarith.Oracle.SimplexAlgorithm.Common

/-!
# Simplex Algorithm for Linarith

This module implements the specific parts of the simplex algorithm used by the linarith oracle.
The core pivot operations and variable selection logic are shared with linear optimization tactics
via the `Common` module.

To obtain required vector in `Linarith.SimplexAlgorithm.findPositiveVector` we run the Simplex
Algorithm. We use Bland's rule for pivoting, which guarantees that the algorithm terminates.
-/

namespace Mathlib.Tactic.Linarith.SimplexAlgorithm

-- Use shared types and functions from Common module
open Mathlib.Tactic.Linarith.SimplexAlgorithm (SimplexAlgorithmException SimplexAlgorithmM)
open Mathlib.Tactic.Linarith.SimplexAlgorithm (doPivotOperation chooseEnteringVar chooseExitingVar choosePivots)

variable {matType : Nat → Nat → Type} [UsableInSimplexAlgorithm matType]

/--
Check if the solution is found: the objective function is positive and all basic variables are
nonnegative.
-/
def checkSuccess : SimplexAlgorithmM matType Bool := do
  let lastIdx := (← get).free.size - 1
  return (← get).mat[(0, lastIdx)]! > 0 &&
    (← (← get).basic.size.allM (fun i _ => do return (← get).mat[(i, lastIdx)]! ≥ 0))


/--
Runs the Simplex Algorithm inside the `SimplexAlgorithmM`. It always terminates, finding solution if
such exists.
-/
def runSimplexAlgorithm : SimplexAlgorithmM matType Unit := do
  while !(← checkSuccess) do
    Lean.Core.checkSystem decl_name%.toString
    let ⟨exitIdx, enterIdx⟩ ← choosePivots
    doPivotOperation exitIdx enterIdx

end Mathlib.Tactic.Linarith.SimplexAlgorithm
