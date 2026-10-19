import ZFCinPA.ValidatorConsistencyEquivalence
import BusyBeaver.ZFC.ArithmeticL2Endpoint254

set_option autoImplicit false
noncomputable section

/-!
# `𝗣𝗔 ⊢ Con(𝗭𝗙𝗖) ↔ the represented Rotation240 interpreter never halts`

The register half of the PA endpoint for the 240-state machine, as fixed
arithmetic sentences:

* `rotationHaltsSentence`: the represented Rotation240 control interpreter
  `ArithmeticControlTable.controlRun ControlBisimRotation240.tableR` reaches the
  absorbing `0` from the seed state `liveValue 1 (enc seed)` (seed record
  `np = 3`, `p1 = 3`, all other registers zero; physical fields
  `[0,0,0,3,0,0,3,0,0]`, spelled as nested Cantor pairs);
* `isigma1_proves_accepted_iff_rotation_halts`: `𝗜𝚺₁` proves that it is
  equivalent to the validator accepting a proof of falsity
  (`ArithmeticL2.accepted_iff_rotation_halts`, the W4/W5 chain);
* `iSigma2_proves_con_ZFC_iff_not_rotation_halts` and its `𝗣𝗔` corollary: hence,
  with `ValidatorConsistencyEquivalence` (in `𝗜𝚺₂`), `𝗜𝚺₂` (so `𝗣𝗔`) proves `Con(𝗭𝗙𝗖)` iff the
  interpreter never halts; likewise for `Con(𝗭𝗙)`.

The binary half (W6: blank240 halts iff this interpreter halts, in every
model of `𝗜𝚺₁`) is not used here.
-/

namespace LeanProofs.ZFCinPA.RotationInterpreterConsistency240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ValidatorConsistencyForward254
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCantor (cantor)
open scoped LO.FirstOrder.Arithmetic

/-- The represented Rotation240 interpreter halts from the seed state. -/
def rotationHaltsSentence : ArithmeticSentence :=
  “∃ p7, !ArithmeticCantor.pairDef p7 0 0 ∧
    ∃ p6, !ArithmeticCantor.pairDef p6 3 p7 ∧
    ∃ p5, !ArithmeticCantor.pairDef p5 0 p6 ∧
    ∃ p4, !ArithmeticCantor.pairDef p4 0 p5 ∧
    ∃ p3, !ArithmeticCantor.pairDef p3 3 p4 ∧
    ∃ p2, !ArithmeticCantor.pairDef p2 0 p3 ∧
    ∃ p1, !ArithmeticCantor.pairDef p1 0 p2 ∧
    ∃ f, !ArithmeticCantor.pairDef f 0 p1 ∧
    ∃ x, !ArithmeticControlFile.liveDef x 1 f ∧
    ∃ k, !(ArithmeticControlTable.controlRunDef ControlBisimRotation240.tableR) 0 k x”

section Model

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The seed record as nested pairs, in the physical order of `enc`. -/
theorem enc_seed : ArithmeticL2.enc (⟨3, 0, 0, 0, 3, 0, 0, 0, 0⟩ : ArithmeticL2.AS V) =
    cantor 0 (cantor 0 (cantor 0 (cantor 3 (cantor 0 (cantor 0 (cantor 3 (cantor 0 0))))))) :=
  rfl

theorem rotationHaltsSentence_eval :
    rotationHaltsSentence.Evalb (M := V) ![] ↔
      ∃ k : V, ArithmeticControlTable.controlRun ControlBisimRotation240.tableR k
        (ArithmeticControlFile.liveValue 1
          (ArithmeticL2.enc (⟨3, 0, 0, 0, 3, 0, 0, 0, 0⟩ : ArithmeticL2.AS V))) = 0 := by
  rw [enc_seed]
  simp only [rotationHaltsSentence]
  simp
  constructor <;> rintro ⟨x, hx⟩ <;> exact ⟨x, hx.symm⟩

end Model

attribute [local irreducible] rotationHaltsSentence

/-- **`𝗜𝚺₁ ⊢` the validator accepts a proof of falsity `↔` the represented
Rotation240 interpreter halts from the seed.** -/
theorem isigma1_proves_accepted_iff_rotation_halts :
    𝗜𝚺₁ ⊢ acceptedFalsitySentence 🡘 rotationHaltsSentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  have h := ArithmeticL2.accepted_iff_rotation_halts (V := M)
  have ha : M↓[ℒₒᵣ] ⊧ acceptedFalsitySentence ↔
      ∃ code : M, ArithmeticHistory254.value code = 2 := by
    rw [models_iff]
    simp only [acceptedFalsitySentence]
    simp
    constructor <;> rintro ⟨x, hx⟩ <;> exact ⟨x, hx.symm⟩
  have hr := (models_iff (M := M) (σ := rotationHaltsSentence)).trans
    (rotationHaltsSentence_eval (V := M))
  simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply]
  rw [ha, hr]
  exact ⟨h.mp, h.mpr⟩

/-- Combine a validator calibration with the interpreter equivalence. -/
theorem combine {M : Type} [ORingStructure M] {C : ArithmeticSentence}
    (hv : M↓[ℒₒᵣ] ⊧ (C 🡘 validatorConsistencySentence))
    (hr : M↓[ℒₒᵣ] ⊧ (acceptedFalsitySentence 🡘 rotationHaltsSentence)) :
    M↓[ℒₒᵣ] ⊧ (C 🡘 ∼rotationHaltsSentence) := by
  simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply,
    validatorConsistencySentence, Semantics.Not.models_not] at hv hr ⊢
  tauto

/-- **`𝗜𝚺₂ ⊢ Con(𝗭𝗙𝗖) ↔` the represented Rotation240 interpreter never halts
from the seed.** -/
theorem iSigma2_proves_con_ZFC_iff_not_rotation_halts :
    𝗜𝚺 2 ⊢ ((𝗭𝗙𝗖 : SetTheory).consistent : ArithmeticSentence) 🡘 ∼rotationHaltsSentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} (𝗜𝚺 2) _
  intro M _ hM
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 2 := hM
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := mod_ISigma_of_le (show 1 ≤ 2 by norm_num)
  exact combine
    (models_of_provable hM ValidatorConsistencyEquivalence.iSigma2_proves_con_ZFC_iff_validator)
    (models_of_provable (inferInstance : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁)
      isigma1_proves_accepted_iff_rotation_halts)

/-- **`𝗜𝚺₂ ⊢ Con(𝗭𝗙) ↔` the represented Rotation240 interpreter never halts
from the seed.** -/
theorem iSigma2_proves_con_ZF_iff_not_rotation_halts :
    𝗜𝚺 2 ⊢ ((𝗭𝗙 : SetTheory).consistent : ArithmeticSentence) 🡘 ∼rotationHaltsSentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} (𝗜𝚺 2) _
  intro M _ hM
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 2 := hM
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := mod_ISigma_of_le (show 1 ≤ 2 by norm_num)
  exact combine
    (models_of_provable hM ValidatorConsistencyEquivalence.iSigma2_proves_con_ZF_iff_validator)
    (models_of_provable (inferInstance : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁)
      isigma1_proves_accepted_iff_rotation_halts)

/-- **`𝗣𝗔 ⊢ Con(𝗭𝗙𝗖) ↔` the represented Rotation240 interpreter never halts
from the seed.** -/
theorem peano_proves_con_ZFC_iff_not_rotation_halts :
    𝗣𝗔 ⊢ ((𝗭𝗙𝗖 : SetTheory).consistent : ArithmeticSentence) 🡘 ∼rotationHaltsSentence :=
  Entailment.weakening (inferInstance : 𝗜𝚺 2 ⪯ 𝗣𝗔) iSigma2_proves_con_ZFC_iff_not_rotation_halts

/-- **`𝗣𝗔 ⊢ Con(𝗭𝗙) ↔` the represented Rotation240 interpreter never halts
from the seed.** -/
theorem peano_proves_con_ZF_iff_not_rotation_halts :
    𝗣𝗔 ⊢ ((𝗭𝗙 : SetTheory).consistent : ArithmeticSentence) 🡘 ∼rotationHaltsSentence :=
  Entailment.weakening (inferInstance : 𝗜𝚺 2 ⪯ 𝗣𝗔) iSigma2_proves_con_ZF_iff_not_rotation_halts

end LeanProofs.ZFCinPA.RotationInterpreterConsistency240
