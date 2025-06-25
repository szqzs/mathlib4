import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Maximize.Parsing
-- import Mathlib
open Mathlib.Tactic

open Lean
open Meta
open Parser.Category

open Elab Tactic
elab "maximize" e_stx:term "as" h_stx:ident : tactic => do
  let e_exp : Expr ← Elab.Tactic.elabTerm e_stx none
  let ty ← inferType e_exp
  let r ← Mathlib.Tactic.Maximize.parseLinarithStructure ty (← getMainGoal)

  let stx ← `(tactic | have $h_stx : $e_stx ≤ 7 := by linarith)
  Lean.Meta.Tactic.TryThis.addSuggestion .missing stx
  -- now it works but it is not clickable in the goal


/--
info: Try this: have H : 4 * x + y ≤ 6 := by linarith
---
error: failed to infer type of example
-/
#guard_msgs in
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
