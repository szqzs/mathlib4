import Mathlib.Tactic.Linarith

-- Test a very simple case first
example (x y : ℚ) (h1 : x + y < 10) (h2 : y > 4) : x < 6 := by
  linarith