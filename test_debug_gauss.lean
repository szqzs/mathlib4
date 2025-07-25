import Mathlib.Tactic.Linarith.Oracle.SimplexAlgorithm.Gauss

-- Test Gaussian elimination directly
#check Mathlib.Tactic.Linarith.SimplexAlgorithm.Gauss.getTableau

-- Test simple case that might cause issue
example (x y z : ℤ) (h1 : 2 * x < 3 * y) (h2 : -4 * x + 2 * z < 0) (h3 : 12 * y - 4 * z < 0) : False := by
  linarith

-- Test multiple constraint variations  
example (x y z : ℤ) (h1 : x < y) (h2 : y < z) (h3 : z < x) : False := by
  linarith