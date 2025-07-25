import Mathlib.Tactic.LinearOptim.Main

-- Test unbounded case
example (x : ℚ) (h1 : x > 0) : x ≤ 10 := by
  maximize x with H
  exact H