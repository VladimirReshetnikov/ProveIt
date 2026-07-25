import ZFCinPA.LocalStepTransfer

/-!
# Audit for the local-step transfer under the enlarged certificate

Three things must stay visible.

* **The positive answer.**  `localStepLaws_step` is a *theorem*: at an
  arbitrary previous level `L` — in particular any interpretation of the
  two source placeholders — the enlarged certificate's laws carry the
  whole `localStep` field to the closure level over `L`.  This is the
  statement whose five-field version `LocalStepDerivation`'s
  `exclusivity_not_step_transferable` refutes relative to `Con(𝗭𝗙𝗖)`.
* **The exact antecedent.**  Read the signature of `localStepLaws_step`:
  besides the previous field (`hprev`) and the enlarged laws (`hL`), it
  consumes the code-induction hypothesis (`hind`) — the honest cost
  recorded in `EnlargedFields`' header — **and** `hb : mem b (omegaV H)`.
  The latter is a *newly identified* obligation: nothing in the seven-field
  certificate pins the numeral placeholder inside `ω`, and every rank
  lemma the transfer consumes needs it.  A source sentence for this field
  must therefore carry both as antecedents, discharged after translation.
* **Non-vacuity.**  `localStepLaws_levelSat` discharges `LocalStepLaws`
  for goal 2's actual hierarchy at every level, and
  `localStepLaws_step_levelSat` instantiates the transfer there, so the
  abstraction is a genuine generalization of goal 2's own laws.

The `#print axioms` lines must show only Lean's three standard classical
axioms.
-/

namespace LeanProofs.ZFCinPA.LocalStepTransferAudit

open LeanProofs.ZFCinPA
open LeanProofs.ZFCinPA.LocalStepTransfer

/-! ## The abstract field and its transfer -/

#check @LocalStepLaws
#check @botNotSigma_step
#check @localStepLaws_step

/-! ## The transfer's inputs, as they appear one module down -/

#check @EnlargedFields.LevelLaws
#check @EnlargedFields.CodeInduction
#check @EnlargedFields.StepGood
#check @EnlargedFields.exclusivity_step

/-! ## Soundness -/

#check @localStepLaws_levelSat
#check @localStepLaws_step_levelSat

/-! ## Assumption audit -/

#print axioms LocalStepLaws
#print axioms botNotSigma_step
#print axioms localStepLaws_step
#print axioms localStepLaws_levelSat
#print axioms localStepLaws_step_levelSat

end LeanProofs.ZFCinPA.LocalStepTransferAudit
