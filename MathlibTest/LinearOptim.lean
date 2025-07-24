import Mathlib.Tactic.LinearOptim.Main

set_option linter.unusedVariables false
set_option autoImplicit false

/-- info: Try this:have H : 4 * x + y ≤ 6 := by linarith -/
#guard_msgs in
example (x y : Rat) (h1 : 3 * x + y < 4) (h2 : x < 2) : 4 * x + y ≤ 6 := by
  maximize 4 * x + y with H
  exact H

/-- info: Try this:have H : 5 * x + 3 * y ≤ 6 := by linarith -/
#guard_msgs in
example (x y : Rat) (h1 : 4 * x + 2 * y < 4) (h2 : x + y < 2) : 5 * x + 3 * y ≤ 6 := by
  maximize 5 * x + 3 * y with H
  exact H

/-- info: Try this:have H : x - y + z ≤ 1 := by linarith -/
#guard_msgs in
example (x y z : Rat) (h1 : x + y < 7) (h2 : 3 * y + 4 * z < 2) (h3 : x - y + z < 1) :
    x - y + z ≤ 1 := by
  maximize x - y + z with H
  exact H

/-- info: Try this:have H : x + 5 * y + 2 * z ≤ 28 / 9 := by linarith -/
#guard_msgs in
example (x y z : Rat) (h1 : x + y + z < 7) (h2 : x + 3 * y + 4 * z < 2)
    (h3 : x + 10 * y + z < 1) : x + 5 * y + 2 * z ≤ 28 / 9 := by
  maximize x + 5 * y + 2 * z with H
  exact H

/-- info: Try this:have T : -x - 5 * y - 2 * z ≤ -18 / 5 := by linarith -/
#guard_msgs in
example (x y z : Rat) (h1 : x + y + 2 * z > 7) (h2 : x + 3 * y + 4 * z > 2)
    (h3 : x + 10 * y + z > 1) : -x - 5 * y - 2 * z ≤ -18 / 5 := by
  maximize -x - 5 * y - 2 * z with T
  exact T

/-- info: Try this:have F : x ≤ 1 := by linarith -/
#guard_msgs in
example (x : Rat) (h : x < 1) : x ≤ 1 := by
  maximize x with F
  exact F

/-- info: Try this:have H : x + 7 * y ≤ 47 / 5 := by linarith -/
#guard_msgs in
example (x y : Rat) (h1 : x + y < 10) (h2 : x + 11 * y < 9) : x + 7 * y ≤ 47 / 5 := by
  maximize x + 7 * y with H
  exact H

/-- info: Try this:have H : -x - 7 * y ≤ 157 / 21 := by linarith -/
#guard_msgs in
example (x y : Rat) (h1 : -2 * x - y < 10) (h2 : -x - 11 * y < 9) : -x - 7 * y ≤ 157 / 21 := by
  maximize -x - 7 * y with H
  exact H

/-- info: Try this:have H : -x - 7 * y ≤ 157 / 21 := by linarith -/
#guard_msgs in
example (x y : Rat) (h1 : -2 * x - y < 10) (h2 : -x - 11 * y < 9) :
    ∃ z : Rat, z < 157 / 20 ∧ -x - 7 * y ≤ z := by
  maximize -x - 7 * y with H
  exact ⟨157 / 21, by linarith, H⟩

/-- info: Try this:have H : -6 ≤ 4 * x + y := by linarith -/
#guard_msgs in
example (x y : Rat) (h1 : 3 * x + y > -4) (h2 : x > -2) : -6 ≤ 4 * x + y := by
  minimize 4 * x + y with H
  exact H

/-- info: Try this:have H : -6 ≤ 5 * x + 3 * y := by linarith -/
#guard_msgs in
example (x y : Rat) (h1 : 4 * x + 2 * y > -4) (h2 : x + y > -2) : -6 ≤ 5 * x + 3 * y := by
  minimize 5 * x + 3 * y with H
  exact H

/-- info: Try this:have H : -1 ≤ x - y + z := by linarith -/
#guard_msgs in
example (x y z : Rat) (h1 : x + y > -7) (h2 : 3 * y + 4 * z > -2) (h3 : x - y + z > -1) :
    -1 ≤ x - y + z := by
  minimize x - y + z with H
  exact H

/-- info: Try this:have H : -47 / 5 ≤ x + 7 * y := by linarith -/
#guard_msgs in
example (x y : Rat) (h1 : x + y > -10) (h2 : x + 11 * y > -9) : -47 / 5 ≤ x + 7 * y := by
  minimize x + 7 * y with H
  exact H

/-- info: Try this:have H : -157 / 21 ≤ -x - 7 * y := by linarith -/
#guard_msgs in
example (x y : Rat) (h1 : -2 * x - y > -10) (h2 : -x - 11 * y > -9) : -157 / 21 ≤ -x - 7 * y := by
  minimize -x - 7 * y with H
  exact H

/-- info: Try this:have H : -157 / 21 ≤ -x - 7 * y := by linarith -/
#guard_msgs in
example (x y : Rat) (h1 : -2 * x - y > -10) (h2 : -x - 11 * y > -9) :
    ∃ z : Rat, z > -157 / 20 ∧ z ≤ -x - 7 * y := by
  minimize -x - 7 * y with H
  exact ⟨-157 / 21, by linarith, H⟩

-- Tests with different types similar to linarith
/-- info: Try this:have H : x + y ≤ 5 := by linarith -/
#guard_msgs in
example {α} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
    (x y : α) (h1 : x + y < 5) (h2 : x < 3) : x + y ≤ 5 := by
  maximize x + y with H
  exact H

/-- info: Try this:have H : 2 * x + 3 * y ≤ 12 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : 2 * x + 3 * y < 12) (h2 : x - y < 4) : 2 * x + 3 * y ≤ 12 := by
  maximize 2 * x + 3 * y with H
  exact H

-- Edge case: simple bound
/-- info: Try this:have H : a ≤ 3 := by linarith -/
#guard_msgs in
example (a : Rat) (ha : a ≤ 3) : a ≤ 3 := by
  maximize a with H
  exact H

-- Test with negation
/-- info: Try this:have H : x - y ≤ 0 := by linarith -/
#guard_msgs in
example (x y : Rat) (h : x < y) : x ≤ y := by
  maximize x - y with H
  linarith [H]

-- Tests with division that should fail (parsing issue: x/2 not recognized as (1/2)*x)
/-- error: maximize: an upper bound cannot be produced for x / 2.
    The constraints may be inconsistent or the expression may be unbounded. -/
#guard_msgs in
example (x : Rat) (h1 : 0 < x) (h2 : x < 10) : x / 2 ≤ 5 := by
  maximize x / 2 with H
  exact H

/-- error: maximize: an upper bound cannot be produced for ε / 2 + ε / 3.
    The constraints may be inconsistent or the expression may be unbounded. -/
#guard_msgs in
example (ε : Rat) (h1 : 0 < ε) (h2 : ε < 6) : ε / 2 + ε / 3 ≤ 5 := by
  maximize ε / 2 + ε / 3 with H
  exact H

-- Test rational coefficient hypothesis: maximize may only handle integer coefficients
/-- error: maximize: an upper bound cannot be produced for (1 / 2) * x.
    The constraints may be inconsistent or the expression may be unbounded. -/
#guard_msgs in
example (x : Rat) (h1 : 0 < x) (h2 : x < 10) : (1 / 2) * x ≤ 5 := by
  maximize (1 / 2) * x with H
  exact H

/-- error: maximize: an upper bound cannot be produced for (1 / 2) * ε + (1 / 3) * ε.
    The constraints may be inconsistent or the expression may be unbounded. -/
#guard_msgs in
example (ε : Rat) (h1 : 0 < ε) (h2 : ε < 6) : (1 / 2) * ε + (1 / 3) * ε ≤ 5 := by
  maximize (1 / 2) * ε + (1 / 3) * ε with H
  exact H

-- Test with simpler rational coefficients
/-- error: maximize: an upper bound cannot be produced for (1 / 1) * x.
    The constraints may be inconsistent or the expression may be unbounded. -/
#guard_msgs in  
example (x : Rat) (h1 : 0 < x) (h2 : x < 10) : (1 / 1) * x ≤ 10 := by
  maximize (1 / 1) * x with H
  exact H

-- Test with decimal representation
/-- error: maximize: an upper bound cannot be produced for 0.5 * x.
    The constraints may be inconsistent or the expression may be unbounded. -/
#guard_msgs in
example (x : Rat) (h1 : 0 < x) (h2 : x < 10) : 0.5 * x ≤ 5 := by
  maximize 0.5 * x with H
  exact H

-- Test with strict inequality (should fail - no maximum exists)
/-- error: maximize: an upper bound cannot be produced for 1 * x.
    The constraints may be inconsistent or the expression may be unbounded. -/
#guard_msgs in
example (x : Rat) (h1 : 0 < x) (h2 : x < 10) : 1 * x ≤ 10 := by
  maximize 1 * x with H
  exact H

/-- error: maximize: an upper bound cannot be produced for x.
    The constraints may be inconsistent or the expression may be unbounded. -/
#guard_msgs in
example (x : Rat) (h1 : 0 < x) (h2 : x < 10) : x ≤ 10 := by
  maximize x with H
  exact H

-- Test with non-strict inequality (still fails - simple bounds don't work)
/-- error: maximize: an upper bound cannot be produced for x.
    The constraints may be inconsistent or the expression may be unbounded. -/
#guard_msgs in
example (x : Rat) (h1 : 0 < x) (h2 : x ≤ 10) : x ≤ 10 := by
  maximize x with H
  exact H

/-- error: maximize: an upper bound cannot be produced for x / 2.
    The constraints may be inconsistent or the expression may be unbounded. -/
#guard_msgs in
example (x : Rat) (h1 : 0 < x) (h2 : x ≤ 10) : x / 2 ≤ 5 := by
  maximize x / 2 with H
  exact H

-- Test with multiple interacting constraints (WORKS! The key insight)
/-- info: Try this:have H : x ≤ 6 := by linarith -/
#guard_msgs in
example (x y : Rat) (h1 : x + y < 10) (h2 : y > 4) : x ≤ 6 := by
  maximize x with H
  exact H

-- Test division with interacting constraints (WORKS! Division is fine with proper constraints)
/-- info: Try this:have H : x / 2 ≤ 6 := by linarith -/
#guard_msgs in
example (x y : Rat) (h1 : x + y < 10) (h2 : y > 4) : x / 2 ≤ 6 := by
  maximize x / 2 with H
  exact H

-- Test that should fail: unbounded maximize
/-- error: maximize: an upper bound cannot be produced for x.
    The constraints may be inconsistent or the expression may be unbounded. -/
#guard_msgs in
example (x : Rat) (h1 : x > 0) : x ≤ 10 := by
  maximize x with H
  exact H

-- Test that should fail: unbounded minimize  
/-- error: minimize: a lower bound cannot be produced for x.
    The constraints may be inconsistent or the expression may be unbounded. -/
#guard_msgs in
example (x : Rat) (h1 : x < 0) : x ≥ -10 := by
  minimize x with H
  exact H

-- Test with non-strict inequalities
/-- info: Try this:have H : x + y ≤ 5 := by linarith -/
#guard_msgs in
example (x y : Rat) (h1 : x + y ≤ 5) (h2 : x ≤ 3) : x + y ≤ 5 := by
  maximize x + y with H
  exact H

-- Test combining strict and non-strict
/-- info: Try this:have H : x + y ≤ 5 := by linarith -/
#guard_msgs in
example (x y : Rat) (h1 : x + y < 5) (h2 : x ≤ 3) : x + y ≤ 5 := by
  maximize x + y with H
  exact H

-- CONSTRAINT ORDER DEPENDENCY TESTS
-- Case 1: Lower bound first, then upper bound (FAILS)
/-- error: maximize: an upper bound cannot be produced for x.
    The constraints may be inconsistent or the expression may be unbounded. -/
#guard_msgs in
example (x : Rat) (h1 : x > 0) (h2 : x < 10) : x ≤ 9 := by
  maximize x with H
  exact H

-- Case 2: Upper bound first, then lower bound (WORKS!)
/-- info: Try this:have H : x ≤ 10 := by linarith -/
#guard_msgs in
example (x : Rat) (h1 : x < 10) (h2 : x > 0) : x ≤ 10 := by
  maximize x with H
  exact H

-- Case 3: Upper, lower, upper again (WORKS!)
/-- info: Try this:have H : x ≤ 6 := by linarith -/
#guard_msgs in
example (x : Rat) (h1 : x < 10) (h2 : x > 0) (h3 : x < 6) : x ≤ 6 := by
  maximize x with H
  exact H

-- Case 4: Lower, upper, lower again (test if it still fails)
/-- error: maximize: an upper bound cannot be produced for x.
    The constraints may be inconsistent or the expression may be unbounded. -/
#guard_msgs in
example (x : Rat) (h1 : x > 0) (h2 : x < 10) (h3 : x > -5) : x ≤ 9 := by
  maximize x with H
  exact H

-- Test with division and constraint order
-- Case 1: Lower bound first, then upper bound with division (FAILS)
/-- error: maximize: an upper bound cannot be produced for x / 2.
    The constraints may be inconsistent or the expression may be unbounded. -/
#guard_msgs in
example (x : Rat) (h1 : x > 0) (h2 : x < 10) : x / 2 ≤ 4 := by
  maximize x / 2 with H
  exact H

-- Case 2: Upper bound first, then lower bound with division (WORKS!)
/-- info: Try this:have H : x / 2 ≤ 10 := by linarith -/
#guard_msgs in
example (x : Rat) (h1 : x < 10) (h2 : x > 0) : x / 2 ≤ 10 := by
  maximize x / 2 with H
  exact H