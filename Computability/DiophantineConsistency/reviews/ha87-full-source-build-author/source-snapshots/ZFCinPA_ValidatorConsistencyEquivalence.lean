import ZFCinPA.R2Native
import ZFCinPA.LSchema
import ZFCinPA.ValidatorConsistencyForward254

set_option autoImplicit false
noncomputable section

/-!
# `𝗣𝗔 ⊢ Con(𝗭𝗙) ↔ validator consistency ↔ Con(𝗭𝗙𝗖)`

The literal numerical validator `ArithmeticHistory254` accepts no proof of
falsity (`validatorConsistencySentence`: no `code` has value `2`) exactly when
`𝗭𝗙` is consistent, and this equivalence is a theorem of `𝗜𝚺₂`, hence of `𝗣𝗔`.

* forward (`ValidatorConsistencyForward254`, in `𝗜𝚺₁`): an accepted falsity row
  decodes to an internal `𝗭𝗙`-refutation;
* reverse (`R2Native`, in `𝗜𝚺₂`): an internal `𝗭𝗙`-refutation becomes an internal
  refutation in the native set theory (`R3`, `NativeSchema`) and then a
  validator proof of falsity (`R2`);
* `𝗭𝗙𝗖` joins the cycle through the internal Gödel-`L` interpretation
  (`LSchema`).
-/

namespace LeanProofs.ZFCinPA.ValidatorConsistencyEquivalence

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ValidatorConsistencyForward254
open scoped LO.FirstOrder.Arithmetic

/-- **`𝗜𝚺₂ ⊢ Con(𝗭𝗙) ↔ the validator accepts no proof of falsity`.** -/
theorem iSigma2_proves_con_ZF_iff_validator :
    𝗜𝚺 2 ⊢ ((𝗭𝗙 : SetTheory).consistent : ArithmeticSentence) 🡘 validatorConsistencySentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} (𝗜𝚺 2) _
  intro M _ hM
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 2 := hM
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := mod_ISigma_of_le (show 1 ≤ 2 by norm_num)
  have hf := zfForwardSentence_true (V := M)
  simp only [zfForwardSentence, LogicalConnective.HomClass.map_imply,
    LogicalConnective.Prop.arrow_eq] at hf
  simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa [models_iff] using hf (by simpa [models_iff] using h)
  · have h' : ¬∃ code : M, _root_.SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.value code = 2 := by
      simpa [models_iff, validatorConsistencySentence_eval] using h
    simpa [models_iff] using R2Native.consistent_ZF_of_validator h'

/-- **`𝗣𝗔 ⊢ Con(𝗭𝗙) ↔ the validator accepts no proof of falsity`.** -/
theorem peano_proves_con_ZF_iff_validator :
    𝗣𝗔 ⊢ ((𝗭𝗙 : SetTheory).consistent : ArithmeticSentence) 🡘 validatorConsistencySentence :=
  Entailment.weakening (inferInstance : 𝗜𝚺 2 ⪯ 𝗣𝗔) iSigma2_proves_con_ZF_iff_validator

/-- **`𝗜𝚺₂ ⊢ Con(𝗭𝗙𝗖) ↔ the validator accepts no proof of falsity`.** -/
theorem iSigma2_proves_con_ZFC_iff_validator :
    𝗜𝚺 2 ⊢ ((𝗭𝗙𝗖 : SetTheory).consistent : ArithmeticSentence) 🡘 validatorConsistencySentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} (𝗜𝚺 2) _
  intro M _ hM
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 2 := hM
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := mod_ISigma_of_le (show 1 ≤ 2 by norm_num)
  have hf := zfcForwardSentence_true (V := M)
  simp only [zfcForwardSentence, LogicalConnective.HomClass.map_imply,
    LogicalConnective.Prop.arrow_eq] at hf
  simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa [models_iff] using hf (by simpa [models_iff] using h)
  · have h' : ¬∃ code : M, _root_.SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.value code = 2 := by
      simpa [models_iff, validatorConsistencySentence_eval] using h
    simpa [models_iff] using LSchema.consistent_ZFC_of_ZF (R2Native.consistent_ZF_of_validator h')

/-- **`𝗣𝗔 ⊢ Con(𝗭𝗙𝗖) ↔ the validator accepts no proof of falsity`.** -/
theorem peano_proves_con_ZFC_iff_validator :
    𝗣𝗔 ⊢ ((𝗭𝗙𝗖 : SetTheory).consistent : ArithmeticSentence) 🡘 validatorConsistencySentence :=
  Entailment.weakening (inferInstance : 𝗜𝚺 2 ⪯ 𝗣𝗔) iSigma2_proves_con_ZFC_iff_validator

end LeanProofs.ZFCinPA.ValidatorConsistencyEquivalence
