import Mathlib.Tactic.LinearOptim.Main

example (x : ℚ) (h : x < 10) : ∃ M, x / 2 ≤ M := by
  -- This should return M = 5, not M = 10 
  maximize (x / 2) with h_bound
  exact ⟨5, h_bound⟩