import Mathlib.Tactic.Linarith

-- Test the case from line 132-133 which might cause infinite loop
example (x y z : ℤ) (h1 : 2 * x < 3 * y) (h2 : -4 * x + 2 * z < 0) (h3 : 12 * y - 4 * z < 0) : False := by
  linarith