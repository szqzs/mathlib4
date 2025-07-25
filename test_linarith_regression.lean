import Mathlib.Tactic.Linarith

-- Test basic linarith functionality after Gaussian elimination rewrite

example (x y : ℚ) (h1 : x + y < 10) (h2 : y > 4) : x < 6 := by
  linarith

example (x : ℚ) (h1 : x > 0) (h2 : x < 10) : x ≠ 15 := by
  linarith

example (a b c : ℚ) (h1 : a + b + c = 0) (h2 : a ≥ 0) (h3 : b ≥ 0) : c ≤ 0 := by
  linarith

-- Simple equality test
example (x y : ℚ) (h1 : x + y = 10) (h2 : x = 3) : y = 7 := by
  linarith

-- Test with division (should work with linarith since it uses CancelDenoms)  
example (x : ℚ) (h : x < 10) : x / 2 < 5 := by
  linarith

example (ε : ℚ) (h : ε < 6) : ε / 2 + ε / 3 < 5 := by
  linarith

-- Test constraint ordering issue that we fixed
example (x : ℚ) (h1 : x > 0) (h2 : x < 10) : x < 11 := by
  linarith

example (x : ℚ) (h1 : x < 10) (h2 : x > 0) : x < 11 := by
  linarith