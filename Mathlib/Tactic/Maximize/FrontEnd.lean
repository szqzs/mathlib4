import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Maximize.Parsing
-- import Mathlib
open Mathlib.Tactic

open Lean
open Meta
open Qq
open Parser.Category

def bestBound (rH : Linarith.Comp) (rr : List Linarith.Comp) (n : ℕ) : MetaM (TSyntax `term) := do
  trace[debug] "there are {n} atoms"
  trace[debug] "maximizing {rH}, hypotheses are {rr}"
  `(7)

open Elab Tactic
elab "maximize" e_stx:term "as" h_stx:ident : tactic => do
  let e_exp : Expr ← Elab.Tactic.elabTerm e_stx none
  let ⟨u, ty, e_exp⟩ ← inferTypeQ' e_exp -- `ty : Q(Type u)`, `e_exp : Q($ty)`
  -- let ty ← inferType e_exp -- `ty : Expr`
  let i ← synthInstanceQ q(PartialOrder $ty)
  let i ← synthInstanceQ q(Semiring $ty)
  assumeInstancesCommute
  have H : Q($e_exp < 0) := q(sorry)

  let (r, n) ← Mathlib.Tactic.Maximize.parseLinarithStructure ty H (← getMainGoal)
  let rH :: rr := r.reverse | failure
  let bound ← bestBound rH rr n

  let stx ← `(tactic | have $h_stx : $e_stx ≤ $bound := by linarith)
  Lean.Meta.Tactic.TryThis.addSuggestion .missing stx
  -- now it works but it is not clickable in the goal

set_option trace.debug true

/--
info: Try this: have H : 4 * x + y ≤ 7 := by linarith
---
warning: declaration uses 'sorry'
---
warning: 'maximize 4 * x + y as H' tactic does nothing
note: this linter can be disabled with `set_option linter.unusedTactic false`
-/
-- #guard_msgs in
example {x y : ℚ} (h1 : 3 * x + y < 4) (h2 : x < 2) : True := by
  maximize 4 * x + y as H
  sorry

example {x y : ℚ} (h1 : 4 * x + 2 * y < 4) (h2 : x + y < 2) : True := by
  maximize 5 * x + 3 * y as H
  -- should have < 6
  sorry

example {x y : ℚ} (h1 : 3 * x + y < 7) (h2 : x < 6) : True := by
  maximize 5 * x + 3 * y as H
  -- in this case should be unable to produce an upper bound, should give an error explaining this to the user
  sorry

--example {x y : ℚ} (h1 : 3 * x + 3 * y < 7)
