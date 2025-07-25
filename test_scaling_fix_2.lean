import Mathlib.Tactic.LinearOptim.Main

-- Test case 1: Simple division by 2
example (x : ℚ) (h : x < 10) : ∃ M, x / 2 ≤ M := by
  maximize (x / 2) with h_bound
  exact ⟨5, h_bound⟩

-- Test case 2: Complex division with LCM
example (ε : ℚ) (h : ε < 6) : ∃ M, ε / 2 + ε / 3 ≤ M := by
  maximize (ε / 2 + ε / 3) with h_bound
  exact ⟨5, h_bound⟩

-- Test case 3: No division (should work as before)
example (x : ℚ) (h : x < 10) : ∃ M, x ≤ M := by
  maximize x with h_bound
  exact ⟨10, h_bound⟩