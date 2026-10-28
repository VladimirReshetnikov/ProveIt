import ZFCinPA.ModelCodedDecoderAccepted222
import ZFCinPA.ValidatorConsistencyLower222
import ZFCinPA.ValidatorConsistencyForward254

set_option autoImplicit false
noncomputable section

/-!
# `𝗣𝗔 ⊢ Con(𝗭𝗙𝗖) ↔ the actual C222 checker accepts no refutation`

Both directions hold in every model of `𝗜𝚺₁`, at arbitrary internal codes:

* upper (`ModelCodedDecoderAccepted222`): an accepted C222 refutation decodes
  to an internal `𝗭𝗙`-refutation, hence an internal `𝗭𝗙𝗖`-refutation;
* lower (`ValidatorConsistencyLower222`): an internal `𝗭𝗙𝗖`-refutation becomes
  an internal `𝗭𝗙`-refutation (the constructible interpretation), a refutation
  of the quotient-interface theory (the well-founded quotient), a refutation
  of the concrete C222 seed theory (the moving-marker tagged interpretation),
  and finally an actual C222 History222 value-two witness.

Completeness over all Type0 models of `𝗜𝚺₁` gives the closed `𝗜𝚺₁` theorem;
the `𝗜𝚺₂` and PA versions follow by weakening.
-/

namespace LeanProofs.ZFCinPA.ValidatorConsistency222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open scoped LO.FirstOrder.Arithmetic

/-- The C222 checker accepts a proof of the falsity code `1`. -/
def refutation222Sentence : ArithmeticSentence :=
  “∃ code, !_root_.SetTheory.BusyBeaver.ZFC.ArithmeticHistory222.checkDef code 1”

def consistency222Sentence : ArithmeticSentence := ∼refutation222Sentence

section Models

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem refutation222Sentence_eval :
    refutation222Sentence.Evalb (M := V) ![] ↔
      ∃ code : V, _root_.SetTheory.BusyBeaver.ZFC.ArithmeticHistory222.value code = 2 := by
  simp [refutation222Sentence, one_add_one_eq_two]

/-- **Upper direction**: an accepted C222 refutation is an internal ZFC refutation. -/
theorem zfc_refutation_of_222 {code : V}
    (h : _root_.SetTheory.BusyBeaver.ZFC.ArithmeticHistory222.value code = 2) :
    Bootstrapping.Provable (𝗭𝗙𝗖 : SetTheory) (^⊥ : V) :=
  ValidatorConsistencyForward254.zfc_provable_of_zf
    (ModelCodedDecoderAccepted222.accepted_falsity_provable_bottom code h)

theorem not_consistent_of_222 {code : V}
    (h : _root_.SetTheory.BusyBeaver.ZFC.ArithmeticHistory222.value code = 2) :
    ¬ ((𝗭𝗙𝗖 : SetTheory).consistent : ArithmeticSentence).Evalb (M := V) ![] := by
  simp only [consistent.defined]
  intro hc
  apply hc
  simpa [Sentence.quote_def, Semiformula.quote_def] using zfc_refutation_of_222 h

end Models

/-- **The two-sided equivalence in every model of `𝗜𝚺₁`.** -/
theorem consistent_iff_no_refutation222 {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    ((𝗭𝗙𝗖 : SetTheory).consistent : ArithmeticSentence).Evalb (M := V) ![] ↔
      ¬ ∃ code : V, _root_.SetTheory.BusyBeaver.ZFC.ArithmeticHistory222.value code = 2 := by
  constructor
  · rintro hc ⟨code, hv⟩
    exact not_consistent_of_222 hv hc
  · intro hn
    by_contra hc
    exact hn (ValidatorConsistencyLower222.refutation222_of_not_consistent hc)

theorem iSigma1_proves_con_ZFC_iff_222 :
    𝗜𝚺₁ ⊢ ((𝗭𝗙𝗖 : SetTheory).consistent : ArithmeticSentence) 🡘 consistency222Sentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  have h := consistent_iff_no_refutation222 (V := M)
  have h' : consistency222Sentence.Evalb (M := M) ![] ↔
      ¬ ∃ code : M, _root_.SetTheory.BusyBeaver.ZFC.ArithmeticHistory222.value code = 2 := by
    simp only [consistency222Sentence, LogicalConnective.HomClass.map_neg,
      LogicalConnective.Prop.neg_eq]
    exact not_congr refutation222Sentence_eval
  simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply,
    models_iff]
  exact ⟨fun hc => h'.2 (h.1 hc), fun hn => h.2 (h'.1 hn)⟩

theorem iSigma2_proves_con_ZFC_iff_222 :
    𝗜𝚺 2 ⊢ ((𝗭𝗙𝗖 : SetTheory).consistent : ArithmeticSentence) 🡘 consistency222Sentence :=
  Entailment.weakening (ISigma_weakerThan_of_le (by decide) : 𝗜𝚺₁ ⪯ 𝗜𝚺 2)
    iSigma1_proves_con_ZFC_iff_222

theorem peano_proves_con_ZFC_iff_222 :
    𝗣𝗔 ⊢ ((𝗭𝗙𝗖 : SetTheory).consistent : ArithmeticSentence) 🡘 consistency222Sentence :=
  Entailment.weakening (inferInstance : 𝗜𝚺₁ ⪯ 𝗣𝗔) iSigma1_proves_con_ZFC_iff_222

end LeanProofs.ZFCinPA.ValidatorConsistency222
