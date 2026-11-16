import IPRABridge.FoundationToConcise
import IPRABridge.ConciseToFoundation
import IPRABridge.ReferenceAxiomImages
import IPRABridge.ConciseAxiomImages
import IPRABridge.OrderRoundtrip
import DiophantineConsistency.IPRAReferenceInductionConversion
import DiophantineConsistency.IPRAReferenceInductionImage
import DiophantineConsistency.IPRAReferenceTheoryTransfer
import DiophantineConsistency.IPRAStandardTheory

/-! Object-theory proof transport between the standard Foundation iPRA used in
Busy Beaver and the ordinary ConciseIPRA natural-deduction calculus. -/

set_option autoImplicit false

namespace IPRABridge

open LO LO.FirstOrder LO.Entailment LeanProofs.ConciseIPRA
open scoped LO.FirstOrder
open DiophantineConsistency
open IPRAOrderErasure (embed erase)
open IPRANativeTheory (nativeTheory)
open IPRAStandardTheory (standardTheory)
open IPRAEqualityOnlyReference (referenceTheory ReferenceAxiom)

private theorem referenceAxiomInNative (φ : Sentenceᵢ IPRAEqualityOnlyReference.language)
    (h : ReferenceAxiom φ) : nativeTheory ⊢ embed φ := by
  cases h with
  | equality he => exact ⟨Axiomatized.prfAxm (IPRAReferenceEqualityImages.equality_images he)⟩
  | defining hd =>
    exact ⟨Axiomatized.prfAxm (IPRAReferenceImages.defining_images hd)⟩
  | successorNonzero =>
    rw [IPRAReferenceEqualityImages.embed_successorNonzero]
    exact ⟨Axiomatized.prfAxm (IPRANativeTheory.NativeAxiom.basic .succNonzero)⟩
  | induction φ hφ =>
    rw [IPRAReferenceInductionImage.embed_inductionAxiom]
    exact ⟨IPRASuccessorInduction.successorInduction (embed φ) (IPRAReferenceRew.embed_preserves_open φ hφ)⟩

/-- Every equality-only reference axiom has a proof of its image in standard iPRA. -/
theorem referenceAxiomInStandard (φ : Sentenceᵢ IPRAEqualityOnlyReference.language)
    (h : ReferenceAxiom φ) : standardTheory ⊢ embed φ :=
  (IPRAStandardTheory.provable_iff _).2 (referenceAxiomInNative φ h)

/-- Erase the order relation from a closed standard iPRA theorem. -/
theorem standardToReference {φ : Sentenceᵢ PRALanguage.language}
    (h : standardTheory ⊢ φ) : referenceTheory ⊢ erase φ :=
  IPRAReferenceInductionConversion.nativeToReference ((IPRAStandardTheory.provable_iff φ).1 h)

/-- Embed a closed equality-only reference theorem in standard iPRA. -/
theorem referenceToStandard {φ : Sentenceᵢ IPRAEqualityOnlyReference.language}
    (h : referenceTheory ⊢ φ) : standardTheory ⊢ embed φ :=
  (IPRAStandardTheory.provable_iff _).2
    (IPRAReferenceTheoryTransfer.transfer_provable referenceAxiomInNative h)

/-- Read a Foundation iPRA sentence in ordinary ConciseIPRA. Native less-than
is expressed by the primitive-recursive comparison function. -/
def toConciseSentence (φ : Sentenceᵢ PRALanguage.language) : Fm PTm 0 :=
  toConciseClosed (erase φ)

/-- Eliminating the order symbol gives a provably equivalent Foundation sentence. -/
theorem standardOrderRoundtrip (φ : Sentenceᵢ PRALanguage.language) :
    standardTheory ⊢ φ 🡘 embed (erase φ) :=
  (IPRAStandardTheory.provable_iff _).2 (nativeOrderRoundtrip φ)

/-- Translate a closed theorem of the Foundation iPRA used in Busy Beaver. -/
theorem standardToConcise {φ : Sentenceᵢ PRALanguage.language}
    (h : standardTheory ⊢ φ) : Prf PRAAx [] (toConciseSentence φ) :=
  theoryToConcise referenceTheory referenceAxiomImage (standardToReference h)

/-- Read a closed ConciseIPRA formula in the standard Foundation language. -/
def toStandardSentence (φ : Fm PTm 0) : Sentenceᵢ PRALanguage.language :=
  embed (toFoundation φ)

/-- Translate a closed ConciseIPRA theorem into the Foundation iPRA used in Busy Beaver. -/
theorem conciseToStandard {φ : Fm PTm 0} (h : Prf PRAAx [] φ) :
    standardTheory ⊢ toStandardSentence φ :=
  referenceToStandard (toFoundation_closed_of_axioms (fun hAx => concise_axiom_image hAx) h)

@[simp] theorem conciseSentence_roundtrip (φ : Fm PTm 0) :
    toConciseSentence (toStandardSentence φ) = φ := by
  simp only [toConciseSentence, toStandardSentence, IPRAOrderErasure.erase_embed, toConciseClosed]
  have hb : (Fin.elim0 : Fin 0 → PTm 0) = PTm.var := funext (fun i => Fin.elim0 i)
  simpa only [hb] using formula_roundtrip φ

/-- Provability of a closed ConciseIPRA formula is equivalent to provability of
its Foundation image. -/
theorem conciseProvable_iff (φ : Fm PTm 0) :
    Prf PRAAx [] φ ↔ standardTheory ⊢ toStandardSentence φ :=
  ⟨conciseToStandard, fun h => by simpa only [conciseSentence_roundtrip] using standardToConcise h⟩

end IPRABridge
