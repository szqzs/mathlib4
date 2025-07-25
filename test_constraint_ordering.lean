import Mathlib.Tactic.LinearOptim.Main

-- Test constraint ordering independence
-- Case 1: Lower bound first, then upper bound (previously failed)
example (x : ℚ) (h1 : x > 0) (h2 : x < 10) : x ≤ 10 := by
  maximize x with H
  exact H

-- Case 2: Upper bound first, then lower bound (previously worked)  
example (x : ℚ) (h1 : x < 10) (h2 : x > 0) : x ≤ 10 := by
  maximize x with H
  exact H

-- More complex constraint ordering test
example (x y : ℚ) (h1 : x > 0) (h2 : x + y < 10) (h3 : y > 4) : x ≤ 6 := by
  maximize x with H
  exact H

example (x y : ℚ) (h1 : x + y < 10) (h2 : y > 4) (h3 : x > 0) : x ≤ 6 := by
  maximize x with H  
  exact H