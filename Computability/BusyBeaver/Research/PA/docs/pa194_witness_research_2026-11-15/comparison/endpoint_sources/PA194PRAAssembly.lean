import PA194Endpoint
import PA194ForwardGG
import PA196PACertificateComplete

/-! Transfer the two classical PRA machine-specific reductions to the exact
PA194 iPRA endpoint, reusing the machine-independent PA witness certificate.
Neither machine-specific reduction is proved in this file. -/
set_option autoImplicit false
noncomputable section
namespace PA194PRAAssembly
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRATheory DiophantineConsistency.IPRANativeTheory
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open DiophantineConsistency.IPRANativeFormula DiophantineConsistency.IPRANativeForwardTheory
open PA194ForwardGG

theorem reverse_of_classical_pra
    (h : PRA ⊢ haltClassical 🡒 mappedPARefutation) :
    standardTheory ⊢ PA194Bounded.haltSentence 🡒 ∼∼nativePARefutation := by
  have hgg : nativeTheory ⊢ haltClassicalᴺ 🡒 mappedPARefutationᴺ :=
    DiophantineConsistency.IPRAImpGG.unpack_imp_image nativeTheory _ _
      (DiophantineConsistency.IPRAFullGGTransfer.from_classical h)
  have hf : nativeTheory ⊢! PA194Bounded.haltSentence 🡒 haltClassicalᴺ := by
    simpa only [haltClassical, haltMatrix, native, PA194Bounded.haltSentence] using
      theoryNativeForward haltClassical
  have hnative : nativeTheory ⊢! PA194Bounded.haltSentence 🡒 ∼∼nativePARefutation :=
    Entailment.C_trans hf (Entailment.C_trans (Classical.choice hgg)
      (PA196ReverseGG.refutation_backward PA196PACertificateComplete.certificate))
  exact (DiophantineConsistency.IPRAStandardTheory.provable_iff _).2 ⟨hnative⟩

/-- The two hypotheses are the outstanding PA194 machine reductions. -/
theorem consistency_iff_nonhalting_of_classical_pra
    (forward : PRA ⊢ mappedPARefutation 🡒 haltClassical)
    (reverse : PRA ⊢ haltClassical 🡒 mappedPARefutation) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼PA194Bounded.haltSentence :=
  ⟨PA194Endpoint.consistency_iff_nonhalting
    (Classical.choice (PA194ForwardGG.forward_of_classical_pra forward))
    (Classical.choice (reverse_of_classical_pra reverse))⟩

#print axioms reverse_of_classical_pra
#print axioms consistency_iff_nonhalting_of_classical_pra
end PA194PRAAssembly
