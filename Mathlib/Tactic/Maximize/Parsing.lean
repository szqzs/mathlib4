/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Mathlib.Control.Basic
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.Maximize.MoreParsing
import Mathlib.Tactic.Ring.Basic


open Lean Elab Parser Tactic Meta
open Batteries


namespace Mathlib.Tactic.Maximize
open Mathlib.Tactic.Linarith



section

-- The default preprocessor throws away non-linear-inequality hypothesis, push negations, turn
-- inequality into ≤, move terms to the left hand side, cancel denominators
def defaultPreprocessors : List Preprocessor := [filterComparisons, removeNegations,
  strengthenStrictInt, compWithZero, cancelDenoms]

/--
`preprocess pps l` takes a list `l` of proofs of propositions.
It maps each preprocessor `pp ∈ pps` over this list.
The preprocessors are run sequentially: each receives the output of the previous one.
Note that a preprocessor may produce multiple or no expressions from each input expression,
so the size of the list may change.
-/
def preprocess' (pps : List Preprocessor) (l : List Expr) :
    MetaM (List Expr) := do
  let zz ← pps.foldlM (init := l) fun ls pp => pp.globalize.transform ls
  return (zz)

end



-- This step extract the type of the terms in the hypothesis
def extractByType (ty : Expr) : List Expr → MetaM (List Expr)
  | [] => return []
  | h :: l => do
    let l' ← extractByType ty l
    if (ty == (← typeOfIneqProof h)) then
      return h :: l'
    else
      return l'

-- This step turns the hypothesis and goal into a matrix
partial def parseLinarithStructure (ty H : Expr) (g : MVarId)
    (cfg : TransparencyMode := .reducible) : MetaM (List Comp × ℕ) := g.withContext do
  let hyps := H :: (← getLocalHyps).toList
  let es ← preprocess' defaultPreprocessors hyps
  let hyp_set ← extractByType ty es
-- This getCoeffs is the key function in this def
  let r ← getCoeffs cfg g hyp_set
  return r



end Maximize


end Mathlib.Tactic
