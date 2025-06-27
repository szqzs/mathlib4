import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Maximize.Parsing
import Mathlib.Tactic.Maximize.PositiveVectors
import Mathlib.Tactic.Maximize.SimplexAlgorithm
import Mathlib.Tactic.Polyrith
import Mathlib.Data.Ineq

open Mathlib
open Mathlib.Tactic
open Lean
open Meta
open Qq
open Parser.Category
open Elab
open Tactic

open Mathlib.Tactic.Linarith.SimplexAlgorithm
open Mathlib.Tactic.Linarith
open Mathlib.Tactic.Maximize

def preprocessS (matType : ℕ → ℕ → Type) [UsableInSimplexAlgorithm matType] (rH : Linarith.Comp)
    (rr : List Linarith.Comp) (maxVar : ℕ) : matType (maxVar + 1) (rr.length + 1) × List Nat :=
  dbg_trace "rH length is {rr.length}"
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
  dbg_trace values
  (ofValues (values), strictIndexes)


def bestBound (rH : Linarith.Comp) (rr : List Linarith.Comp) (n : ℕ) :
    MetaM (TSyntax `term) := do
  trace[debug] "there are {n} atoms"
  trace[debug] "maximizing {rH}, hypotheses are {rr}"
  let (A, strictIndexes) := preprocessS DenseMatrix rH rr n
  let r ← findPositiveVectorS A strictIndexes
  return quote (-r)

elab "maximize" e_stx:term "as" h_stx:ident : tactic => do
  let e_exp : Expr ← Elab.Tactic.elabTerm e_stx none
  let ⟨u, ty, e_exp⟩ ← inferTypeQ' e_exp -- `ty : Q(Type u)`, `e_exp : Q($ty)`
  -- let ty ← inferType e_exp -- `ty : Expr`
  let i ← synthInstanceQ q(PartialOrder $ty)
  let i ← synthInstanceQ q(Semiring $ty)
  assumeInstancesCommute
  have H : Q($e_exp < 0) := q(sorry)
  -- This step turns both the hypotheses and goal into a matrix r and a number n for atoms
  let (r, n) ← Mathlib.Tactic.Maximize.parseLinarithStructure ty H (← getMainGoal)
  -- This step splits off the goal vector rH from the matrix r and leave the hypothesis matrix rr
  let rH :: rr := r.reverse | failure
  let bound ← bestBound rH rr n
  let stx ← `(tactic | have $h_stx : $e_stx ≤ $bound := by linarith)
  Lean.Meta.Tactic.TryThis.addSuggestion .missing stx
  -- now it works but it is not clickable in the goal

set_option trace.debug true

example {x y : ℚ} (h1 : 3 * x + y < 4) (h2 : x < 2) : True := by
  maximize 4 * x + y as H
  sorry

example {x y : ℚ} (h1 : 4 * x + 2 * y < 4) (h2 : x + y < 2) : True := by
  maximize 5 * x + 3 * y as H
  -- should have < 6
  sorry

example {x y : ℚ} (h1 : 3 * x + y ≤ 7) (h2 : x < 6) : True := by
  maximize 5 * x + 3 * y as H
  -- in this case should be unable to produce an upper bound,
  -- should give an error explaining this to the user
  sorry

example {x y z : ℚ} (h1 : x + y < 7) (h2 : 3 * y + 4 * z < 2) (h3 : x - y + z < 1)
  : True := by
  maximize x - y + z as H
  -- should have < 1
  sorry

example {x y z : ℚ} (h1 : x + y + z < 7)(h2 : x + 3 * y + 4 * z < 2)(h3 : x + 10 * y + z < 1)
  : True := by
  maximize x + 5 * y + 2 * z as H
  -- should have < 28 / 9
  sorry

example {x y z : ℚ} (h1 : - x - 5 * y - 2 * z > 7) (h2 : x + 3 * y + 4 * z > 2)
  (h3 : x + 10 * y + z > 1) : True := by
  maximize - x - 5 * y - 2 * z as T
  -- should have < - 18 /5
  sorry

example {x y z w : ℚ} (h : x < 1) : True := by
  maximize x as F
  -- should have < 1
  sorry

example {x y : ℚ} (h1 : x + y < 10) (h2 : x + 11 * y < 9) : True := by
  maximize x + 7 * y as H
  -- should have < 47 / 5
  sorry
