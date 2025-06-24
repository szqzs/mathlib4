import Mathlib.Tactic.Linarith

-- import Mathlib
open Mathlib.Tactic

open Lean
open Parser.Category

open Elab Tactic
elab "maximize" e:term "as" h:ident : tactic => do
  let stx ← `(tactic | have $h : $e ≤ 7 := by linarith)
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
