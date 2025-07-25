import Mathlib.Tactic.LinearOptim.Main

-- Test minimize with division
example (x : ℚ) (h : x > 10) : ∃ M, M ≤ x / 2 := by
  minimize (x / 2) with h_bound
  exact ⟨5, h_bound⟩