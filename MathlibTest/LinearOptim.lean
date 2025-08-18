import Mathlib.Tactic.LinearOptim.Main

set_option linter.unusedVariables false
set_option autoImplicit false

/-- info: Try this: have H : 4 * x + y < 6 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : 3 * x + y < 4) (h2 : x < 2) : True := by
  maximize 4 * x + y with H
  trivial

/-- info: Try this: have H : 5 * x + 3 * y < 6 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : 4 * x + 2 * y < 4) (h2 : x + y < 2) : True := by
  maximize 5 * x + 3 * y with H
  trivial

/-- info: Try this: have H : x - y + z < 1 := by linarith -/
#guard_msgs in
example (x y z : ℚ) (h1 : x + y < 7) (h2 : 3 * y + 4 * z < 2) (h3 : x - y + z < 1) :
    True := by
  maximize x - y + z with H
  trivial

/-- info: Try this: have H : x + 5 * y + 2 * z < 28 / 9 := by linarith -/
#guard_msgs in
example (x y z : ℚ) (h1 : x + y + z < 7) (h2 : x + 3 * y + 4 * z < 2)
    (h3 : x + 10 * y + z < 1) : True := by
  maximize x + 5 * y + 2 * z with H
  trivial

/-- info: Try this: have T : -x - 5 * y - 2 * z < -18 / 5 := by linarith -/
#guard_msgs in
example (x y z : ℚ) (h1 : x + y + 2 * z > 7) (h2 : x + 3 * y + 4 * z > 2)
    (h3 : x + 10 * y + z > 1) : True := by
  maximize -x - 5 * y - 2 * z with T
  trivial

/-- info: Try this: have F : x < 1 := by linarith -/
#guard_msgs in
example (x : ℚ) (h : x < 1) : True := by
  maximize x with F
  trivial

/-- info: Try this: have H : x + 7 * y < 47 / 5 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : x + y < 10) (h2 : x + 11 * y < 9) : True := by
  maximize x + 7 * y with H
  trivial

/-- info: Try this: have H : -x - 7 * y < 157 / 21 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : -2 * x - y < 10) (h2 : -x - 11 * y < 9) : True := by
  maximize -x - 7 * y with H
  trivial

/-- info: Try this: have H : -x - 7 * y < 157 / 21 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : -2 * x - y < 10) (h2 : -x - 11 * y < 9) :
    ∃ z : ℚ, z < 157 / 20 ∧ -x - 7 * y ≤ z := by
  maximize -x - 7 * y with H
  exact ⟨157 / 21, by linarith, by linarith [H]⟩

/-- info: Try this: have H : -6 < 4 * x + y := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : 3 * x + y > -4) (h2 : x > -2) : True := by
  minimize 4 * x + y with H
  trivial

/-- info: Try this: have H : -6 < 5 * x + 3 * y := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : 4 * x + 2 * y > -4) (h2 : x + y > -2) : True := by
  minimize 5 * x + 3 * y with H
  trivial

/-- info: Try this: have H : -1 < x - y + z := by linarith -/
#guard_msgs in
example (x y z : ℚ) (h1 : x + y > -7) (h2 : 3 * y + 4 * z > -2) (h3 : x - y + z > -1) :
    True := by
  minimize x - y + z with H
  trivial

/-- info: Try this: have H : -28 / 9 < x + 5 * y + 2 * z := by linarith -/
#guard_msgs in
example (x y z : ℚ) (h1 : x + y + z > -7) (h2 : x + 3 * y + 4 * z > -2)
    (h3 : x + 10 * y + z > -1) : True := by
  minimize x + 5 * y + 2 * z with H
  trivial

/-- info: Try this: have T : 18 / 5 < -x - 5 * y - 2 * z := by linarith -/
#guard_msgs in
example (x y z : ℚ) (h1 : x + y + 2 * z < -7) (h2 : x + 3 * y + 4 * z < -2)
    (h3 : x + 10 * y + z < -1) : True := by
  minimize -x - 5 * y - 2 * z with T
  trivial

/-- info: Try this: have F : -1 < x := by linarith -/
#guard_msgs in
example (x : ℚ) (h : x > -1) : True := by
  minimize x with F
  trivial

/-- info: Try this: have H : -47 / 5 < x + 7 * y := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : x + y > -10) (h2 : x + 11 * y > -9) : True := by
  minimize x + 7 * y with H
  trivial

/-- info: Try this: have H : -157 / 21 < -x - 7 * y := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : -2 * x - y > -10) (h2 : -x - 11 * y > -9) : True := by
  minimize -x - 7 * y with H
  trivial

/-- info: Try this: have H : -157 / 21 < -x - 7 * y := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : -2 * x - y > -10) (h2 : -x - 11 * y > -9) :
    ∃ z : ℚ, z > -157 / 20 ∧ z ≤ -x - 7 * y := by
  minimize -x - 7 * y with H
  exact ⟨-157 / 21, by linarith, by linarith [H]⟩

-- Tests with different types similar to linarith
/-- info: Try this: have H : x + y < 5 := by linarith -/
#guard_msgs in
example {α} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
    (x y : α) (h1 : x + y < 5) (h2 : x < 3) : True := by
  maximize x + y with H
  trivial

/-- info: Try this: have H : 2 * x + 3 * y < 12 := by linarith -/
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
/-- info: Try this: have H : x - y < 0 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h : x < y) : True := by
  maximize x - y with H
  trivial

-- Tests with division
/-- info: Try this: have H : x / 2 < 5 := by linarith -/
#guard_msgs in
example (x : ℚ) (h1 : 0 < x) (h2 : x < 10) : True := by
  maximize x / 2 with H
  trivial

/-- info: Try this: have H : ε / 2 + ε / 3 < 5 := by linarith -/
#guard_msgs in
example (ε : ℚ) (h1 : 0 < ε) (h2 : ε < 6) : True := by
  maximize ε / 2 + ε / 3 with H
  trivial

-- Test rational coefficient expressions
/-- info: Try this: have H : (1 / 2) * x < 5 := by linarith -/
#guard_msgs in
example (x : ℚ) (h1 : 0 < x) (h2 : x < 10) : True := by
  maximize (1 / 2) * x with H
  trivial

/-- info: Try this: have H : (1 / 2) * ε + (1 / 3) * ε < 5 := by linarith -/
#guard_msgs in
example (ε : ℚ) (h1 : 0 < ε) (h2 : ε < 6) : True := by
  maximize (1 / 2) * ε + (1 / 3) * ε with H
  trivial

-- Test with simpler rational coefficients
/-- info: Try this: have H : (1 / 1) * x < 10 := by linarith -/
#guard_msgs in
example (x : ℚ) (h1 : 0 < x) (h2 : x < 10) : True := by
  maximize (1 / 1) * x with H
  trivial

-- Test with decimal representation
/-- info: Try this: have H : 0.5 * x < 5 := by linarith -/
#guard_msgs in
example (x : ℚ) (h1 : 0 < x) (h2 : x < 10) : True := by
  maximize 0.5 * x with H
  trivial

-- Test with strict inequality
/-- info: Try this: have H : 1 * x < 10 := by linarith -/
#guard_msgs in
example (x : ℚ) (h1 : 0 < x) (h2 : x < 10) : True := by
  maximize 1 * x with H
  trivial

/-- info: Try this: have H : x < 10 := by linarith -/
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
/-- info: Try this: have H : x < 6 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : x + y < 10) (h2 : y > 4) : True := by
  maximize x with H
  trivial

-- Test division with interacting constraints
/-- info: Try this: have H : x / 2 < 3 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : x + y < 10) (h2 : y > 4) : True := by
  maximize x / 2 with H
  trivial

/-! ### Tests with a numeric additive constant in the maximization expression -/
section

/-- info: Try this: have H : 4 * x + y + 1 < 7 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : 3 * x + y < 4) (h2 : x < 2) : True := by
  maximize 4 * x + y + 1 with H
  trivial

/-- info: Try this: have H : -5 < 4 * x + y + 1 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : 3 * x + y > -4) (h2 : x > -2) : True := by
  minimize 4 * x + y + 1 with H
  trivial

/-- info: Try this: have H : x / 2 + 1 < 4 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : x + y < 10) (h2 : y > 4) : True := by
  maximize x / 2 + 1 with H
  trivial

end

-- Test that should fail: unbounded maximize
/-- error: maximize: an upper bound cannot be produced for x.
    The expression may be unbounded. -/
#guard_msgs in
example (x : ℚ) (h1 : x > 0) : True := by
  maximize x with H
  trivial

-- Test that should fail: unbounded minimize
/-- error: minimize: a lower bound cannot be produced for x.
    The expression may be unbounded. -/
#guard_msgs in
example (x : ℚ) (h1 : x < 0) : True := by
  minimize x with H
  trivial



-- Test that should fail: unbounded expression
/-- error: maximize: an upper bound cannot be produced for 5 * x + 3 * y.
    The expression may be unbounded. -/
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
/-- info: Try this: have H : x + y < 5 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : x + y < 5) (h2 : x ≤ 3) : True := by
  maximize x + y with H
  trivial

-- CONSTRAINT ORDER DEPENDENCY TESTS
-- Case 1: Lower bound first, then upper bound
/-- info: Try this: have H : x < 10 := by linarith -/
#guard_msgs in
example (x : ℚ) (h1 : x > 0) (h2 : x < 10) : True := by
  maximize x with H
  trivial

-- Case 2: Upper bound first, then lower bound
/-- info: Try this: have H : x < 10 := by linarith -/
#guard_msgs in
example (x : ℚ) (h1 : x < 10) (h2 : x > 0) : True := by
  maximize x with H
  trivial

-- Case 3: Upper, lower, upper again
/-- info: Try this: have H : x < 6 := by linarith -/
#guard_msgs in
example (x : ℚ) (h1 : x < 10) (h2 : x > 0) (h3 : x < 6) : True := by
  maximize x with H
  trivial

-- Case 4: Lower, upper, lower again
/-- info: Try this: have H : x < 10 := by linarith -/
#guard_msgs in
example (x : ℚ) (h1 : x > 0) (h2 : x < 10) (h3 : x > -5) : True := by
  maximize x with H
  trivial

-- Test with division and constraint order
-- Case 1: Lower bound first, then upper bound with division
/-- info: Try this: have H : x / 2 < 5 := by linarith -/
#guard_msgs in
example (x : ℚ) (h1 : x > 0) (h2 : x < 10) : True := by
  maximize x / 2 with H
  trivial

-- Case 2: Upper bound first, then lower bound with division
/-- info: Try this: have H : x / 2 < 5 := by linarith -/
#guard_msgs in
example (x : ℚ) (h1 : x < 10) (h2 : x > 0) : True := by
  maximize x / 2 with H
  trivial



-- Test that should fail: unbounded expression
/-- error: maximize: an upper bound cannot be produced for x.
    The expression may be unbounded. -/
#guard_msgs in
example (x : ℚ) (h2 : x > 0) :  True := by
  maximize x with H
  trivial



-- Test that should succeed: bounded expression
/-- info: Try this: have H : x < -5 := by linarith -/
#guard_msgs in
example (x : ℚ) (h2 : x < -5) :  True := by
  maximize x with H
  trivial

-- Test that should fail: inconsistent constraints minimize
/-- error: maximize: an upper bound cannot be produced for x.
    The constraints may be inconsistent. -/
#guard_msgs in
example (x : ℚ) (h2 : x > 0) (h1 : x < -5):  True := by
  maximize x with H
  trivial

-- Test that should fail: inconsistent constraints minimize
/-- error: minimize: a lower bound cannot be produced for x.
    The constraints may be inconsistent. -/
#guard_msgs in
example (x : ℚ) (h2 : x < 0) (h1 : x > 5):  True := by
  minimize x with H
  trivial

 -- Test that should fail: inconsistent constraints and unbounded expressions maximize
 -- Because there is hypotehsis h3 that involves y, the algorithm won't detect unboundedness from
 -- the lack of contrainst on y first. Thus it detects inconsistent constraints first thus the error
 -- message should say that.
/-- error: maximize: an upper bound cannot be produced for y + x.
    The constraints may be inconsistent. -/
#guard_msgs in
example (x y : ℚ) (h2 : x < 0) (h1 : x > 5) (h3 : y > 10):  True := by
  maximize y + x with H
  trivial

 -- Test that should fail: inconsistent constraints and unbounded expressions maximize
/-- error: maximize: an upper bound cannot be produced for x + y.
    The constraints may be inconsistent. -/
#guard_msgs in
example (x y : ℚ) (h2 : x < 0) (h1 : x > 5) (h3 : y > 10):  True := by
  maximize x + y with H
  trivial

 -- Test that should fail: unbounded expressions maximize
/-- error: maximize: an upper bound cannot be produced for y + x.
    The expression may be unbounded. -/
#guard_msgs in
example (x y : ℚ) (h1 : x > 5) (h3 : y > 10):  True := by
  maximize y + x with H
  trivial

 -- Test that should fail: unbounded expressions maximize
/-- error: maximize: an upper bound cannot be produced for x + y.
    The expression may be unbounded. -/
#guard_msgs in
example (x y z : ℚ) (h1 : x > 5) (h3 : y > 10):  True := by
  maximize x + y with H
  trivial

 -- Test that should fail: inconsistent constraints and unbounded expressions minimize
 -- In this case, the algorithm detects inconsistent constraints first thus the error message should
 -- say that.
/-- error: minimize: a lower bound cannot be produced for y + x.
    The constraints may be inconsistent. -/
#guard_msgs in
example (x y : ℚ) (h2 : x < 0) (h1 : x > 5) (h3 : y < 10):  True := by
  minimize y + x with H
  trivial

 -- Test that should fail: inconsistent constraints and unbounded expressions minimize
/-- error: minimize: a lower bound cannot be produced for x + y.
    The constraints may be inconsistent. -/
#guard_msgs in
example (x y : ℚ) (h2 : x < 0) (h1 : x > 5) (h3 : y < 10):  True := by
  minimize x + y with H
  trivial

 -- Test that should fail: inconsistent constraints and unbounded expressions
 -- In this case, because there is hypothesis involving y, the algorithm detects unbounded
 -- expressions first.
/-- error: maximize: an upper bound cannot be produced for y.
    The expression may be unbounded. -/
#guard_msgs in
example (x y : ℚ) (h2 : x > 0) (h1 : y >= 7):  True := by
  maximize y with H
  trivial

 -- Test that should fail: inconsistent constraints and unbounded expressions
/-- error: maximize: an upper bound cannot be produced for y.
    The expression may be unbounded. -/
#guard_msgs in
example (x y : ℚ) (h2 : x < 0) (h1 : x > 7):  True := by
  maximize y with H
  trivial

 -- Test that should fail: inconsistent constraints and unbounded expressions
/-- error: maximize: an upper bound cannot be produced for -y.
    The expression may be unbounded. -/
#guard_msgs in
example (x y : ℚ) (h2 : x < 0) (h1 : x > 7):  True := by
  maximize -y with H
  trivial

 -- Test that should fail: inconsistent constraints and unbounded expressions
/-- error: maximize: an upper bound cannot be produced for x.
    The expression may be unbounded. -/
#guard_msgs in
example (x y : ℚ) (h2 : y < 0) (h1 : y > 7):  True := by
  maximize x with H
  trivial

 -- Test that should fail: inconsistent constraints
/-- error: maximize: an upper bound cannot be produced for y.
    The expression may be unbounded. -/
#guard_msgs in
example (x y : ℚ) (h2 : x < 0):  True := by
  maximize y with H
  trivial

 -- Test that should fail: inconsistent constraints
/-- error: maximize: an upper bound cannot be produced for x + y.
    The expression may be unbounded. -/
#guard_msgs in
example (x y z : ℚ) (h2 : y > 5) :  True := by
  maximize x + y
  trivial

 -- Test that should fail: inconsistent constraints
/-- error: maximize: an upper bound cannot be produced for x + y.
    The expression may be unbounded. -/
#guard_msgs in
example (x y : ℚ) (h1 : x > 0) (h2 : y <= 5) (h3: y > 9):  True := by
  maximize x + y
  trivial

-- TESTS FOR OPTIONAL WITH CLAUSE

-- Test maximize without with clause
/-- info: Try this: have : 4 * x + y < 6 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : 3 * x + y < 4) (h2 : x < 2) : True := by
  maximize 4 * x + y
  trivial

-- Test minimize without with clause
/-- info: Try this: have : -6 < 4 * x + y := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : 3 * x + y > -4) (h2 : x > -2) : True := by
  minimize 4 * x + y
  trivial

-- Test mixed usage: with and without with clause in same proof
/-- info: Try this: have : x + y < 5 := by linarith
---
info: Try this: have H : 2 * x + y < 8 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : x + y < 5) (h2 : x < 3) : True := by
  maximize x + y  -- anonymous
  maximize 2 * x + y with H  -- named
  trivial

-- Test complex expression without with clause
/-- info: Try this: have : x + 5 * y + 2 * z < 28 / 9 := by linarith -/
#guard_msgs in
example (x y z : ℚ) (h1 : x + y + z < 7) (h2 : x + 3 * y + 4 * z < 2)
    (h3 : x + 10 * y + z < 1) : True := by
  maximize x + 5 * y + 2 * z
  trivial

-- COMPREHENSIVE TESTS FOR OPTIONAL WITH CLAUSE FEATURE

-- Test 1: Basic maximize without with clause
/-- info: Try this: have : x < 10 := by linarith -/
#guard_msgs in
example (x : ℚ) (h : x < 10) : True := by
  maximize x
  trivial

-- Test 2: Basic minimize without with clause
/-- info: Try this: have : 5 < x := by linarith -/
#guard_msgs in
example (x : ℚ) (h : x > 5) : True := by
  minimize x
  trivial

-- Test 3: Complex expression maximize without with clause
/-- info: Try this: have : 3 * x + 2 * y < 21 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : x < 5) (h2 : y < 3) : True := by
  maximize 3 * x + 2 * y
  trivial

-- Test 4: Complex expression minimize without with clause
/-- info: Try this: have : -10 < 2 * x - y := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : x > -2) (h2 : y < 6) : True := by
  minimize 2 * x - y
  trivial

-- Test 5: Verify backward compatibility - old syntax still works
/-- info: Try this: have old_bound : x + y < 12 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : x < 7) (h2 : y < 5) : True := by
  maximize x + y with old_bound
  trivial

-- Test 6: Multiple anonymous calls in sequence
/-- info: Try this: have : x < 5 := by linarith
---
info: Try this: have : y < 3 := by linarith
---
info: Try this: have : x + y < 8 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : x < 5) (h2 : y < 3) : True := by
  maximize x
  maximize y
  maximize x + y
  trivial

-- Test 7: Multiple named calls in sequence
/-- info: Try this: have bound_x : x < 5 := by linarith
---
info: Try this: have bound_y : y < 3 := by linarith
---
info: Try this: have bound_sum : x + y < 8 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : x < 5) (h2 : y < 3) : True := by
  maximize x with bound_x
  maximize y with bound_y
  maximize x + y with bound_sum
  trivial

-- Test 8: Mixed named and anonymous in complex proof
/-- info: Try this: have : x < 10 := by linarith
---
info: Try this: have y_bound : y < 5 := by linarith
---
info: Try this: have : x + y < 15 := by linarith
---
info: Try this: have z_bound : z < 2 := by linarith -/
#guard_msgs in
example (x y z : ℚ) (h1 : x < 10) (h2 : y < 5) (h3 : z < 2) : True := by
  maximize x                    -- anonymous
  maximize y with y_bound       -- named
  maximize x + y                -- anonymous
  maximize z with z_bound       -- named
  trivial

-- Test 9: Anonymous bounds used in subsequent reasoning
/-- info: Try this: have : x + y < 8 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : x < 5) (h2 : y < 3) : x + y < 10 := by
  maximize x + y
  linarith

-- Test 10: Named bounds used in subsequent reasoning
/-- info: Try this: have max_bound : x + y < 8 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : x < 5) (h2 : y < 3) : x + y ≤ 9 := by
  maximize x + y with max_bound
  linarith [max_bound]

-- Test 11: Minimize without with clause in complex constraints
/-- info: Try this: have : -15 < 3 * x + 2 * y := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : x > -5) (h2 : y > 0) : True := by
  minimize 3 * x + 2 * y
  trivial

-- Test 12: Multiple minimize calls without with clause
/-- info: Try this: have : 2 < x := by linarith
---
info: Try this: have : -3 < y := by linarith
---
info: Try this: have : -1 < x + y := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : x > 2) (h2 : y > -3) : True := by
  minimize x
  minimize y
  minimize x + y
  trivial

-- Test 13: Mixed maximize and minimize without with clause
/-- info: Try this: have : x < 10 := by linarith
---
info: Try this: have : 5 < y := by linarith
---
info: Try this: have : 8 < x + y := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : x < 10) (h2 : y > 5) (h3 : x > 3) : True := by
  maximize x        -- anonymous maximize
  minimize y        -- anonymous minimize
  minimize x + y    -- anonymous minimize (now has proper lower bound)
  trivial

-- Test 14: Complex mixed usage with both syntaxes
/-- info: Try this: have : x < 8 := by linarith
---
info: Try this: have min_y : 3 < y := by linarith
---
info: Try this: have min_sum : 5 < x + y := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : x < 8) (h2 : y > 3) (h3 : x > 2) : True := by
  maximize x                      -- anonymous
  minimize y with min_y           -- named
  minimize x + y with min_sum     -- named (now has proper lower bound)
  trivial

-- Test 15: Fractional expressions without with clause
/-- info: Try this: have : x / 3 + y / 2 < 7 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : x < 12) (h2 : y < 6) : True := by
  maximize x / 3 + y / 2
  trivial

-- Test 16: Verify different identifier names work with optional syntax
/-- info: Try this: have upper_bound : x * 2 + y * 3 < 25 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : x < 5) (h2 : y < 5) : True := by
  maximize x * 2 + y * 3 with upper_bound
  trivial

-- Test 17: Single variable cases - both syntaxes
/-- info: Try this: have : a < 100 := by linarith
---
info: Try this: have single_var_bound : b < 50 := by linarith -/
#guard_msgs in
example (a b : ℚ) (h1 : a < 100) (h2 : b < 50) : True := by
  maximize a                        -- anonymous single var
  maximize b with single_var_bound  -- named single var
  trivial

-- Test 18: Error cases - unbounded expressions (should still work for both syntaxes)
/-- error: maximize: an upper bound cannot be produced for x.
    The expression may be unbounded. -/
#guard_msgs in
example (x : ℚ) (h : x > 0) : True := by
  maximize x  -- Should fail - unbounded without with clause
  trivial

/-- error: maximize: an upper bound cannot be produced for x.
    The expression may be unbounded. -/
#guard_msgs in
example (x : ℚ) (h : x > 0) : True := by
  maximize x with H  -- Should fail - unbounded with with clause
  trivial

-- Test 19: Verify minimize error cases work with both syntaxes
/-- error: minimize: a lower bound cannot be produced for x.
    The expression may be unbounded. -/
#guard_msgs in
example (x : ℚ) (h : x < 0) : True := by
  minimize x  -- Should fail - unbounded minimize without with clause
  trivial

/-- error: minimize: a lower bound cannot be produced for x.
    The expression may be unbounded. -/
#guard_msgs in
example (x : ℚ) (h : x < 0) : True := by
  minimize x with H  -- Should fail - unbounded minimize with with clause
  trivial

-- Test 20: Large expressions without with clause
/-- info: Try this: have : a + 2 * b + 3 * c + 4 * d < 30 := by linarith -/
#guard_msgs in
example (a b c d : ℚ) (h1 : a < 5) (h2 : b < 4) (h3 : c < 3) (h4 : d < 2) : True := by
  maximize a + 2 * b + 3 * c + 4 * d
  trivial

/-! ### Explicit tests for strict vs non-strict inequality behavior

These tests verify that maximize/minimize tactics:
1. Prefer strict inequalities when all constraints are strict
2. Fall back to non-strict inequalities when any constraint is non-strict
3. Work correctly with the anonymous syntax (without 'with' clause)
-/

section StrictVsNonStrict

-- Verify strict inequality is used when all constraints are strict
/-- info: Try this: have H : x + 2 * y < 7 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : x < 3) (h2 : y < 2) : True := by
  maximize x + 2 * y with H
  trivial

-- Verify non-strict inequality is used when bound is non-strict
/-- info: Try this: have H : x + 2 * y ≤ 7 := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : x ≤ 3) (h2 : y ≤ 2) : True := by
  maximize x + 2 * y with H
  trivial

-- Same test for minimize with strict
/-- info: Try this: have H : -1 < x + 2 * y := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : x > -3) (h2 : y > 1) : True := by
  minimize x + 2 * y with H
  trivial

-- Same test for minimize with non-strict
/-- info: Try this: have H : -1 ≤ x + 2 * y := by linarith -/
#guard_msgs in
example (x y : ℚ) (h1 : x ≥ -3) (h2 : y ≥ 1) : True := by
  minimize x + 2 * y with H
  trivial

-- Verify anonymous syntax also respects strict/non-strict
/-- info: Try this: have : 2 * x < 10 := by linarith -/
#guard_msgs in
example (x : ℚ) (h : x < 5) : True := by
  maximize 2 * x
  trivial

/-- info: Try this: have : 2 * x ≤ 10 := by linarith -/
#guard_msgs in
example (x : ℚ) (h : x ≤ 5) : True := by
  maximize 2 * x
  trivial

end StrictVsNonStrict
