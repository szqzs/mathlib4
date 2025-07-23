/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Mathlib.Tactic.Linarith.Datatypes

/-!
# Type Utilities for Linarith

This file contains shared type checking and validation utilities used across the linarith tactic.
These utilities help identify mathematical expressions suitable for linear arithmetic reasoning.
-/

open Lean
open Elab Tactic Meta

namespace Mathlib.Tactic.Linarith

/-! ### Type Checking Utilities -/

/--
`isArithmeticType tp` returns true if `tp` is a type suitable for linear arithmetic,
such as `ℕ`, `ℤ`, `ℚ`, or `ℝ`.
-/
def isArithmeticType (tp : Expr) : Bool :=
  match tp.getAppFn with
  | .const ``Nat [] => true
  | .const ``Int [] => true
  | .const ``Rat [] => true
  | _ => false

/--
`typeOfComparisonExpr e` extracts the type of the terms being compared in an expression `e`
that represents an inequality or equality.
-/
def typeOfComparisonExpr (e : Expr) : MetaM (Option Expr) := do
  try
    let (_, tp, _, _) ← e.ineq?
    return some tp
  catch _ =>
    try
      let some (tp, _, _) := e.ne?' | return none
      return some tp
    catch _ => return none

/--
`isLinearComparisonType e` checks if `e` is a comparison expression over a type
suitable for linear arithmetic.
-/
def isLinearComparisonType (e : Expr) : MetaM Bool := do
  match ← typeOfComparisonExpr e with
  | some tp => return isArithmeticType tp
  | none => return false

/--
`validateLinearExpr e` performs basic validation that an expression `e` is suitable
for linear arithmetic reasoning.
-/
def validateLinearExpr (e : Expr) : MetaM Bool := do
  -- Check if it's a comparison
  if ← isLinearComparisonType e then
    return true
  -- Check if the expression involves arithmetic types
  try
    let tp ← inferType e
    return isArithmeticType tp
  catch _ => return false

/-! ### Expression Classification -/

/--
`classifyMathematicalExpr e` classifies an expression as one of:
- `comparison`: An inequality or equality suitable for linarith
- `arithmetic`: An arithmetic expression that might be usable
- `other`: Not suitable for linear arithmetic
-/
inductive ExprClass
  | comparison
  | arithmetic
  | other

/--
Classify an expression for linarith processing.
-/
def classifyMathematicalExpr (e : Expr) : MetaM ExprClass := do
  if ← isLinearComparisonType e then
    return .comparison
  else if ← validateLinearExpr e then
    return .arithmetic
  else
    return .other

end Mathlib.Tactic.Linarith