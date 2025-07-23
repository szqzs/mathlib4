/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuli Chen, Robert Y. Lewis, Heather Macbeth, Siqing Zhang, Runtian Zhou
-/
import Mathlib.Tactic.LinearOptim.Main

/-!
# Tests for Linear Optimization Tactics

This file contains test cases for the `maximize` and `minimize` tactics
implemented in `Mathlib.Tactic.LinearOptim`.
-/

-- set_option trace.debug true
set_option linter.unusedVariables false

section MaximizeTests

example {x y : ℚ} (h1 : 3 * x + y < 4) (h2 : x < 2) : True := by
  maximize 4 * x + y with H
  -- should have 6
  trivial

example {x y : ℚ} (h1 : 4 * x + 2 * y < 4) (h2 : x + y < 2) : True := by
  maximize 5 * x + 3 * y with H
  -- should have 6
  trivial

example {x y : ℚ} (h1 : 3 * x + y ≤ 7) (h2 : x < 6) : True := by
  maximize 5 * x + 3 * y with H
  -- in this case should be unable to produce an upper bound,
  -- should give an error explaining this to the user
  sorry

example {x y z : ℚ} (h1 : x + y < 7) (h2 : 3 * y + 4 * z < 2) (h3 : x - y + z < 1)
  : True := by
  maximize x - y + z with H
  -- should have 1
  trivial

example {x y z : ℚ} (h1 : x + y + z < 7) (h2 : x + 3 * y + 4 * z < 2) (h3 : x + 10 * y + z < 1)
  : True := by
  maximize x + 5 * y + 2 * z with H
  -- should have 28 / 9
  trivial

example {x y z : ℚ} (h1 : x + y + 2 * z > 7) (h2 : x + 3 * y + 4 * z > 2)
  (h3 : x + 10 * y + z > 1) : True := by
  maximize - x - 5 * y - 2 * z with T
  -- should have - 18 /5
  trivial

example {x y z w : ℚ} (h : x < 1) : True := by
  maximize x with F
  -- should have 1
  trivial

example {x y : ℚ} (h1 : x + y < 10) (h2 : x + 11 * y < 9) : True := by
  maximize x + 7 * y with H
  -- should have 47 / 5
  trivial

example {x y : ℚ} (h1 : -2 * x - y < 10) (h2 : -x - 11 * y < 9) : True := by
  maximize - x - 7 * y with H
  -- should have 157 / 21
  trivial

example {x y : ℚ} (h1 : -2 * x - y < 10) (h2 : -x - 11 * y < 9) :
  ∃ z : ℚ, (z < 157 / 20) ∧ (- x - 7 * y ≤ z) := by
  maximize -x - 7 * y with H
  exact ⟨157 / 21, by linarith, H⟩

end MaximizeTests

section MinimizeTests

-- Same constraints as maximize tests, but negate the objective function
example {x y : ℚ} (h1 : 3 * x + y < 4) (h2 : x < 2) : True := by
  minimize (-4 * x - y) with H
  -- should have -6 (negation of maximize result)
  trivial

example {x y : ℚ} (h1 : 4 * x + 2 * y < 4) (h2 : x + y < 2) : True := by
  minimize (-5 * x - 3 * y) with H
  -- should have -6 (negation of maximize result)
  trivial

example {x y : ℚ} (h1 : x + y < 10) (h2 : x + 11 * y < 9) : True := by
  minimize (-x - 7 * y) with H
  -- should have -47 / 5 (negation of maximize result)
  trivial

-- Original minimize tests (not derived from maximize tests)
example {x y : ℚ} (h1 : x > 1) (h2 : y > 2) : True := by
  minimize x + y with H
  -- Simple lower bound minimization
  trivial

example {x y z : ℚ} (h1 : x + y + z > 1) (h2 : x - y + 2 * z > 0) (h3 : 2 * x + y - z > -1) : True := by
  minimize 3 * x + y + z with H
  -- Multi-variable minimization with mixed constraints
  trivial

example {x y : ℚ} (h1 : x > 0) (h2 : y > 1) : True := by
  minimize 2 * x + 3 * y with H
  -- Test with different coefficient patterns
  trivial

example {a b c : ℚ} (h1 : a + b + c > 6) (h2 : a - b > 1) (h3 : b + 2 * c > 4) : True := by
  minimize a + b + 2 * c with H
  -- Test with variables named differently
  trivial

example {x : ℚ} (h1 : x > -5) : True := by
  minimize 2 * x + 1 with H
  -- Single variable minimization
  trivial

example {x y : ℚ} (h1 : -x - y < 10) (h2 : x - 3 * y < 8) : True := by
  minimize x + y with H
  -- Test with negative coefficients in constraints (bounded region)
  trivial

end MinimizeTests