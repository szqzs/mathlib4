import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linarith.Oracle.FourierMotzkin
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Order.Interval.Finset.Nat

private axiom test_sorry : ∀ {α}, α
set_option linter.unusedVariables false
set_option autoImplicit false

open Lean.Elab.Tactic in
def testSorryTac : TacticM Unit := do
  let e ← getMainTarget
  let t ← `(test_sorry)
  closeMainGoalUsing `sorry fun _ _ => elabTerm t e

-- Testing first ~25 examples to see if early examples cause timeout
-- Will incrementally narrow down the range

example {α} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
    {a b : α} (h : a < b) (w : b < a) : False := by
  linarith

example {α : Type} (_inst : (a : Prop) → Decidable a)
    [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
    {a b c : α}
    (ha : a < 0)
    (hb : ¬b = 0)
    (hc' : c = 0)
    (h : (1 - a) * (b * b) ≤ 0)
    (hc : 0 ≤ 0)
    (w : -(a * -b * -b + b * -b + 0) = (1 - a) * (b * b))
    (h : (1 - a) * (b * b) ≤ 0) :
    0 < 1 - a := by
  linarith

example (e b c a v0 v1 : Rat) (h1 : v0 = 5 * a) (h2 : v1 = 3 * b) (h3 : v0 + v1 + c = 10) :
    v0 + 5 + (v1 - 3) + (c - 2) = 10 := by
  linarith

example {α} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
    (e b c a v0 v1 : α) (h1 : v0 = 5 * a) (h2 : v1 = 3 * b)
    (h3 : v0 + v1 + c = 10) : v0 + 5 + (v1 - 3) + (c - 2) = 10 := by
  linarith

example (h : (1 : ℤ) < 0) (g : ¬ (37 : ℤ) < 42) (_k : True) (l : (-7 : ℤ) < 5): (3 : ℤ) < 7 := by
  linarith [(rfl : 0 = 0)]

example (u v r s t : Rat) (h : 0 < u * (t * v + t * r + s)) : 0 < (t * (r + v) + s) * 3 * u := by
  linarith

example (A B : Rat) (h : 0 < A * B) : 0 < 8*A*B := by
  linarith

-- Test a few more early ones
example (h : False) : False := by linarith

example (h : ¬ False) : 1 = 1 := by linarith [Nat.succ_ne_zero 0]

example (a b c d : ℤ) (h1 : a = b) (h2 : b = c) : a * c = b * b := by linarith