import Mathlib.Tactic.Linarith

-- Very basic test
example (x : ℚ) (h : x > 5) : x > 4 := by
  linarith