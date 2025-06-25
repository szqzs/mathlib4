/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/

import Mathlib.Tactic.Linarith.Verification
import Mathlib.Util.Qq

/-!
# Deriving a proof of false

`linarith` uses an untrusted oracle to produce a certificate of unsatisfiability.
It needs to do some proof reconstruction work to turn this into a proof term.
This file implements the reconstruction.

## Main declarations

The public facing declaration in this file is `proveFalseByLinarith`.
-/

open Lean Elab Tactic Meta

namespace Qq

variable {u : Level}



end Qq

namespace Mathlib.Tactic.Linarith

open Ineq
open Qq







/-! #### The main method -/

/--
`proveFalseByLinarith` is the main workhorse of `linarith`.
Given a list `l` of proofs of `tᵢ Rᵢ 0`,
it tries to derive a contradiction from `l` and use this to produce a proof of `False`.

`oracle : CertificateOracle` is used to search for a certificate of unsatisfiability.

The returned certificate is a map `m` from hypothesis indices to natural number coefficients.
If our set of hypotheses has the form `{tᵢ Rᵢ 0}`,
then the elimination process should have guaranteed that
1.\ `∑ (m i)*tᵢ = 0`,
with at least one `i` such that `m i > 0` and `Rᵢ` is `<`.

We have also that
2.\ `∑ (m i)*tᵢ < 0`,
since for each `i`, `(m i)*tᵢ ≤ 0` and at least one is strictly negative.
So we conclude a contradiction `0 < 0`.

It remains to produce proofs of (1) and (2). (1) is verified by calling the provided `discharger`
tactic, which is typically `ring`. We prove (2) by folding over the set of hypotheses.

`transparency : TransparencyMode` controls the transparency level with which atoms are identified.
-/
def getCoeffs (transparency : TransparencyMode) : MVarId → List Expr → MetaM (List Comp × ℕ)
  | _, [] => throwError "no args to linarith"
  | _, l@(h::_) => do
      Lean.Core.checkSystem decl_name%.toString
      -- for the elimination to work properly, we must add a proof of `-1 < 0` to the list,
      -- along with negated equality proofs.
      let l' ← addNegEqProofs l
      let inputs := (← mkNegOneLtZeroProof (← typeOfIneqProof h))::l'.reverse
      trace[linarith.detail] "inputs:{indentD <| toMessageData (← inputs.mapM inferType)}"
      let (comps, max_var) ←
        linearFormsAndMaxVar transparency inputs
      trace[linarith.detail] "comps:{indentD <| toMessageData comps}"
      return (comps, max_var)

end Mathlib.Tactic.Linarith
