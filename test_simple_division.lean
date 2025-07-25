import Mathlib.Tactic.LinearOptim.Main

-- Simple division test
example (x y : ℚ) (h1 : x + y < 10) (h2 : y > 4) : x / 2 ≤ 3 := by
  set_option trace.debug true in
  maximize x / 2 with H
  exact H