import ZFCinPA.ValidatorConsistencyForward254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ValidatorConsistencyForward254
open _root_.SetTheory.BusyBeaver.ZFC
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
#print axioms LeanProofs.ZFCinPA.ValidatorConsistencyForward254.zfc_provable_of_zf
#print axioms LeanProofs.ZFCinPA.ValidatorConsistencyForward254.validatorConsistencySentence_eval
#print axioms LeanProofs.ZFCinPA.ValidatorConsistencyForward254.zfForwardSentence_true
#print axioms LeanProofs.ZFCinPA.ValidatorConsistencyForward254.zfcForwardSentence_true
#print axioms LeanProofs.ZFCinPA.ValidatorConsistencyForward254.isigma1_proves_zf_forward
#print axioms LeanProofs.ZFCinPA.ValidatorConsistencyForward254.peano_proves_zf_forward
#print axioms LeanProofs.ZFCinPA.ValidatorConsistencyForward254.isigma1_proves_zfc_forward
#print axioms LeanProofs.ZFCinPA.ValidatorConsistencyForward254.peano_proves_zfc_forward
example (p : V) (h : Provable (𝗭𝗙 : SetTheory) p) : Provable (𝗭𝗙𝗖 : SetTheory) p :=
  zfc_provable_of_zf h
example : validatorConsistencySentence.Evalb (M := V) ![] ↔
    ¬∃ code : V, ArithmeticHistory254.value code = 2 := validatorConsistencySentence_eval
example : zfForwardSentence.Evalb (M := V) ![] := zfForwardSentence_true
example : zfcForwardSentence.Evalb (M := V) ![] := zfcForwardSentence_true
example : 𝗜𝚺₁ ⊢ zfForwardSentence := isigma1_proves_zf_forward
example : Peano ⊢ zfForwardSentence := peano_proves_zf_forward
example : 𝗜𝚺₁ ⊢ zfcForwardSentence := isigma1_proves_zfc_forward
example : Peano ⊢ zfcForwardSentence := peano_proves_zfc_forward
example (h : (𝗭𝗙 : SetTheory).Consistent V) :
    ¬∃ code : V, ArithmeticHistory254.value code = 2 := by
  have ht := zfForwardSentence_true (V := V)
  simp only [zfForwardSentence, LogicalConnective.HomClass.map_imply,
    LogicalConnective.Prop.arrow_eq, consistent.defined,
    validatorConsistencySentence_eval] at ht
  exact ht h
example (h : (𝗭𝗙𝗖 : SetTheory).Consistent V) :
    ¬∃ code : V, ArithmeticHistory254.value code = 2 := by
  have ht := zfcForwardSentence_true (V := V)
  simp only [zfcForwardSentence, LogicalConnective.HomClass.map_imply,
    LogicalConnective.Prop.arrow_eq, consistent.defined,
    validatorConsistencySentence_eval] at ht
  exact ht h
