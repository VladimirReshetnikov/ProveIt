import ZFCinPA.ModelCodedDecoderAccepted254
import Foundation.FirstOrder.Incompleteness.Consistency

set_option autoImplicit false
noncomputable section

/-!
Fixed arithmetic implications from Foundation ZF/ZFC consistency to absence
of an accepted falsity proof in the literal numerical validator. These use
the all-internal accepted-row theorem before applying arithmetic completeness.
The converse and the actual binary-runtime connection are separate.
-/
namespace LeanProofs.ZFCinPA.ValidatorConsistencyForward254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ModelCodedDecoderAccepted254
open LeanProofs.ZFCinPA.ModelCodedRenamingAxioms
open _root_.SetTheory.BusyBeaver.ZFC
open scoped LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The same internal derivation code remains valid under the actual union
recognizer ZFC = ZF ∪ AC, including nonstandard axiom instances. -/
theorem zfc_provable_of_zf {p : V} (h : Provable (𝗭𝗙 : SetTheory) p) :
    Provable (𝗭𝗙𝗖 : SetTheory) p := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d, hd.1, Derivation.of_ss ?_ hd.2⟩
  intro q hq
  change q ∈ ((𝗭𝗙 : SetTheory) ∪ 𝗔𝗖).Δ₁Class
  exact (union_class_iff (𝗭𝗙 : SetTheory) 𝗔𝗖 q).mpr (Or.inl hq)

def acceptedFalsitySentence : ArithmeticSentence :=
  “∃ code, !ArithmeticHistory254.valueDef 2 code”

def validatorConsistencySentence : ArithmeticSentence := ∼acceptedFalsitySentence

noncomputable def zfForwardSentence : ArithmeticSentence :=
  ((𝗭𝗙 : SetTheory).consistent : ArithmeticSentence) 🡒 validatorConsistencySentence

noncomputable def zfcForwardSentence : ArithmeticSentence :=
  ((𝗭𝗙𝗖 : SetTheory).consistent : ArithmeticSentence) 🡒 validatorConsistencySentence

theorem validatorConsistencySentence_eval :
    validatorConsistencySentence.Evalb (M := V) ![] ↔
      ¬∃ code : V, ArithmeticHistory254.value code = 2 := by
  simp [validatorConsistencySentence, acceptedFalsitySentence, eq_comm]

theorem zfForwardSentence_true : zfForwardSentence.Evalb (M := V) ![] := by
  simp only [zfForwardSentence, LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq, consistent.defined,
    validatorConsistencySentence_eval]
  intro hc ⟨code, hv⟩
  have hb := accepted_falsity_provable_bottom code hv
  apply hc
  simpa [Sentence.quote_def, Semiformula.quote_def] using hb

theorem zfcForwardSentence_true : zfcForwardSentence.Evalb (M := V) ![] := by
  simp only [zfcForwardSentence, LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq, consistent.defined,
    validatorConsistencySentence_eval]
  intro hc ⟨code, hv⟩
  have hb := zfc_provable_of_zf (accepted_falsity_provable_bottom code hv)
  apply hc
  simpa [Sentence.quote_def, Semiformula.quote_def] using hb

theorem isigma1_proves_zf_forward : 𝗜𝚺₁ ⊢ zfForwardSentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  simpa [models_iff] using (zfForwardSentence_true (V := M))

theorem peano_proves_zf_forward : Peano ⊢ zfForwardSentence :=
  Entailment.weakening (inferInstance : 𝗜𝚺₁ ⪯ Peano) isigma1_proves_zf_forward

theorem isigma1_proves_zfc_forward : 𝗜𝚺₁ ⊢ zfcForwardSentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  simpa [models_iff] using (zfcForwardSentence_true (V := M))

theorem peano_proves_zfc_forward : Peano ⊢ zfcForwardSentence :=
  Entailment.weakening (inferInstance : 𝗜𝚺₁ ⪯ Peano) isigma1_proves_zfc_forward

end LeanProofs.ZFCinPA.ValidatorConsistencyForward254
