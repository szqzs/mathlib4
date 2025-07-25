import Mathlib.Tactic.LinearOptim.Main

-- Test cases that should work
example (x y : ℚ) (h1 : x + y < 10) (h2 : y > 4) : x ≤ 6 := by
  maximize x with H
  exact H

example (x y : ℚ) (h1 : x + y < 10) (h2 : y > 4) : x / 2 ≤ 3 := by
  maximize x / 2 with H
  exact H

example (ε : ℚ) (h1 : 0 < ε) (h2 : ε < 6) : ε / 2 + ε / 3 ≤ 5 := by
  maximize ε / 2 + ε / 3 with H
  exact H

-- Constraint ordering tests
example (x : ℚ) (h1 : x > 0) (h2 : x < 10) : x / 2 ≤ 5 := by
  maximize x / 2 with H
  exact H

example (x : ℚ) (h1 : x < 10) (h2 : x > 0) : x / 2 ≤ 5 := by
  maximize x / 2 with H
  exact H