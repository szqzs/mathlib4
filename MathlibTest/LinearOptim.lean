import Mathlib.Tactic.LinearOptim.Main

set_option linter.unusedVariables false
set_option autoImplicit false

/-- info: Try this: have H : 4 * x + y ≤ 6 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : 3 * x + y < 4) (h2 : x < 2) : True := by
  maximize 4 * x + y with H
  trivial

/-- info: Try this: have H : 5 * x + 3 * y ≤ 6 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : 4 * x + 2 * y < 4) (h2 : x + y < 2) : True := by
  maximize 5 * x + 3 * y with H
  trivial

/-- info: Try this: have H : x - y + z ≤ 1 := by linarith -/
#guard_msgs in
example (x y z : ℚ) (h1 : x + y < 7) (h2 : 3 * y + 4 * z < 2) (h3 : x - y + z < 1) :
    True := by
  maximize x - y + z with H
  trivial

/-- info: Try this: have H : x + 5 * y + 2 * z ≤ 28 / 9 := by linarith -/
#guard_msgs in
example (x y z : ℚ) (h1 : x + y + z < 7) (h2 : x + 3 * y + 4 * z < 2)
    (h3 : x + 10 * y + z < 1) : True := by
  maximize x + 5 * y + 2 * z with H
  trivial

/-- info: Try this: have T : -x - 5 * y - 2 * z ≤ -18 / 5 := by linarith -/
#guard_msgs in
example (x y z : ℚ) (h1 : x + y + 2 * z > 7) (h2 : x + 3 * y + 4 * z > 2)
    (h3 : x + 10 * y + z > 1) : True := by
  maximize -x - 5 * y - 2 * z with T
  trivial

/-- info: Try this: have F : x ≤ 1 := by linarith -/
#guard_msgs in
example (x : ℚ) (h : x < 1) : True := by
  maximize x with F
  trivial

/-- info: Try this: have H : x + 7 * y ≤ 47 / 5 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : x + y < 10) (h2 : x + 11 * y < 9) : True := by
  maximize x + 7 * y with H
  trivial

/-- info: Try this: have H : -x - 7 * y ≤ 157 / 21 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : -2 * x - y < 10) (h2 : -x - 11 * y < 9) : True := by
  maximize -x - 7 * y with H
  trivial

/-- info: Try this: have H : -x - 7 * y ≤ 157 / 21 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : -2 * x - y < 10) (h2 : -x - 11 * y < 9) :
    ∃ z : ℚ, z < 157 / 20 ∧ -x - 7 * y ≤ z := by
  maximize -x - 7 * y with H
  exact ⟨157 / 21, by linarith, H⟩

/-- info: Try this: have H : -6 ≤ 4 * x + y := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : 3 * x + y > -4) (h2 : x > -2) : True := by
  minimize 4 * x + y with H
  trivial

/-- info: Try this: have H : -6 ≤ 5 * x + 3 * y := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : 4 * x + 2 * y > -4) (h2 : x + y > -2) : True := by
  minimize 5 * x + 3 * y with H
  trivial

/-- info: Try this: have H : -1 ≤ x - y + z := by linarith -/
#guard_msgs in
example (x y z : ℚ) (h1 : x + y > -7) (h2 : 3 * y + 4 * z > -2) (h3 : x - y + z > -1) :
    True := by
  minimize x - y + z with H
  trivial

/-- info: Try this: have H : -47 / 5 ≤ x + 7 * y := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : x + y > -10) (h2 : x + 11 * y > -9) : True := by
  minimize x + 7 * y with H
  trivial

/-- info: Try this: have H : -157 / 21 ≤ -x - 7 * y := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : -2 * x - y > -10) (h2 : -x - 11 * y > -9) : True := by
  minimize -x - 7 * y with H
  trivial

/-- info: Try this: have H : -157 / 21 ≤ -x - 7 * y := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : -2 * x - y > -10) (h2 : -x - 11 * y > -9) :
    ∃ z : ℚ, z > -157 / 20 ∧ z ≤ -x - 7 * y := by
  minimize -x - 7 * y with H
  exact ⟨-157 / 21, by linarith, H⟩

-- Tests with different types similar to linarith
/-- info: Try this: have H : x + y ≤ 5 := by linarith -/
#guard_msgs in
example {α} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
    (x y : α) (h1 : x + y < 5) (h2 : x < 3) : True := by
  maximize x + y with H
  trivial

/-- info: Try this: have H : 2 * x + 3 * y ≤ 12 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : 2 * x + 3 * y < 12) (h2 : x - y < 4) : True := by
  maximize 2 * x + 3 * y with H
  trivial

-- Edge case: simple bound
/-- info: Try this: have H : a ≤ 3 := by linarith -/
#guard_msgs in
example (a : ℚ) (ha : a ≤ 3) : True := by
  maximize a with H
  trivial

-- Test with negation
/-- info: Try this: have H : x - y ≤ 0 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h : x < y) : True := by
  maximize x - y with H
  trivial

-- Tests with division
/-- info: Try this: have H : x / 2 ≤ 5 := by linarith -/
#guard_msgs in
example (x : ℚ) (h1 : 0 < x) (h2 : x < 10) : True := by
  maximize x / 2 with H
  trivial

/-- info: Try this: have H : ε / 2 + ε / 3 ≤ 5 := by linarith -/
#guard_msgs in
example (ε : ℚ) (h1 : 0 < ε) (h2 : ε < 6) : True := by
  maximize ε / 2 + ε / 3 with H
  trivial

-- Test rational coefficient expressions
/-- info: Try this: have H : (1 / 2) * x ≤ 5 := by linarith -/
#guard_msgs in
example (x : ℚ) (h1 : 0 < x) (h2 : x < 10) : True := by
  maximize (1 / 2) * x with H
  trivial

/-- info: Try this: have H : (1 / 2) * ε + (1 / 3) * ε ≤ 5 := by linarith -/
#guard_msgs in
example (ε : ℚ) (h1 : 0 < ε) (h2 : ε < 6) : True := by
  maximize (1 / 2) * ε + (1 / 3) * ε with H
  trivial

-- Test with simpler rational coefficients
/-- info: Try this: have H : (1 / 1) * x ≤ 10 := by linarith -/
#guard_msgs in
example (x : ℚ) (h1 : 0 < x) (h2 : x < 10) : True := by
  maximize (1 / 1) * x with H
  trivial

-- Test with decimal representation
/-- info: Try this: have H : 0.5 * x ≤ 5 := by linarith -/
#guard_msgs in
example (x : ℚ) (h1 : 0 < x) (h2 : x < 10) : True := by
  maximize 0.5 * x with H
  trivial

-- Test with strict inequality
/-- info: Try this: have H : 1 * x ≤ 10 := by linarith -/
#guard_msgs in
example (x : ℚ) (h1 : 0 < x) (h2 : x < 10) : True := by
  maximize 1 * x with H
  trivial

/-- info: Try this: have H : x ≤ 10 := by linarith -/
#guard_msgs in
example (x : ℚ) (h1 : 0 < x) (h2 : x < 10) : True := by
  maximize x with H
  trivial

-- Test with non-strict inequality
/-- info: Try this: have H : x ≤ 10 := by linarith -/
#guard_msgs in
example (x : ℚ) (h1 : 0 < x) (h2 : x ≤ 10) : True := by
  maximize x with H
  trivial

/-- info: Try this: have H : x / 2 ≤ 5 := by linarith -/
#guard_msgs in
example (x : ℚ) (h1 : 0 < x) (h2 : x ≤ 10) : True := by
  maximize x / 2 with H
  trivial

-- Test with multiple interacting constraints
/-- info: Try this: have H : x ≤ 6 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : x + y < 10) (h2 : y > 4) : True := by
  maximize x with H
  trivial

-- Test division with interacting constraints
/-- info: Try this: have H : x / 2 ≤ 3 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : x + y < 10) (h2 : y > 4) : True := by
  maximize x / 2 with H
  trivial

-- Test that should fail: unbounded maximize
/-- error: maximize: an upper bound cannot be produced for x.
    The constraints may be inconsistent or the expression may be unbounded. -/
#guard_msgs in
example (x : ℚ) (h1 : x > 0) : True := by
  maximize x with H
  trivial

-- Test that should fail: unbounded minimize
/-- error: minimize: a lower bound cannot be produced for x.
    The constraints may be inconsistent or the expression may be unbounded. -/
#guard_msgs in
example (x : ℚ) (h1 : x < 0) : True := by
  minimize x with H
  trivial

-- Test that should fail: inconsistent constraints
/-- error: maximize: an upper bound cannot be produced for x.
    The constraints may be inconsistent or the expression may be unbounded. -/
#guard_msgs in
example (x : ℚ) (h1 : x > 5) (h2 : x < 3) : True := by
  maximize x with H
  trivial

-- Test that should fail: unbounded expression
/-- error: maximize: an upper bound cannot be produced for 5 * x + 3 * y.
    The constraints may be inconsistent or the expression may be unbounded. -/
#guard_msgs in
example (x y : ℚ) (h1 : 3 * x + y ≤ 7) (h2 : x < 6) : True := by
  maximize 5 * x + 3 * y with H
  trivial

-- Test with non-strict inequalities
/-- info: Try this: have H : x + y ≤ 5 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : x + y ≤ 5) (h2 : x ≤ 3) : True := by
  maximize x + y with H
  trivial

-- Test combining strict and non-strict
/-- info: Try this: have H : x + y ≤ 5 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : x + y < 5) (h2 : x ≤ 3) : True := by
  maximize x + y with H
  trivial

-- CONSTRAINT ORDER DEPENDENCY TESTS
-- Case 1: Lower bound first, then upper bound
/-- info: Try this: have H : x ≤ 10 := by linarith -/
#guard_msgs in
example (x : ℚ) (h1 : x > 0) (h2 : x < 10) : True := by
  maximize x with H
  trivial

-- Case 2: Upper bound first, then lower bound
/-- info: Try this: have H : x ≤ 10 := by linarith -/
#guard_msgs in
example (x : ℚ) (h1 : x < 10) (h2 : x > 0) : True := by
  maximize x with H
  trivial

-- Case 3: Upper, lower, upper again
/-- info: Try this: have H : x ≤ 6 := by linarith -/
#guard_msgs in
example (x : ℚ) (h1 : x < 10) (h2 : x > 0) (h3 : x < 6) : True := by
  maximize x with H
  trivial

-- Case 4: Lower, upper, lower again
/-- info: Try this: have H : x ≤ 10 := by linarith -/
#guard_msgs in
example (x : ℚ) (h1 : x > 0) (h2 : x < 10) (h3 : x > -5) : True := by
  maximize x with H
  trivial

-- Test with division and constraint order
-- Case 1: Lower bound first, then upper bound with division
/-- info: Try this: have H : x / 2 ≤ 5 := by linarith -/
#guard_msgs in
example (x : ℚ) (h1 : x > 0) (h2 : x < 10) : True := by
  maximize x / 2 with H
  trivial

-- Case 2: Upper bound first, then lower bound with division
/-- info: Try this: have H : x / 2 ≤ 5 := by linarith -/
#guard_msgs in
example (x : ℚ) (h1 : x < 10) (h2 : x > 0) : True := by
  maximize x / 2 with H
  trivial
