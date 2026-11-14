import PA195Endpoint
import PA195ForwardGG
import PA196PACertificateComplete

/-! Transfer the two classical PRA machine-specific reductions to the exact
PA195 iPRA endpoint, reusing the machine-independent PA witness certificate.
Neither machine-specific reduction is proved in this file. -/
set_option autoImplicit false
noncomputable section
namespace PA195PRAAssembly
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRATheory DiophantineConsistency.IPRANativeTheory
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open DiophantineConsistency.IPRANativeFormula DiophantineConsistency.IPRANativeForwardTheory
open PA195ForwardGG

theorem reverse_of_classical_pra
    (h : PRA ⊢ haltClassical 🡒 mappedPARefutation) :
    standardTheory ⊢ PA195Bounded.haltSentence 🡒 ∼∼nativePARefutation := by
  have hgg : nativeTheory ⊢ haltClassicalᴺ 🡒 mappedPARefutationᴺ :=
    DiophantineConsistency.IPRAImpGG.unpack_imp_image nativeTheory _ _
      (DiophantineConsistency.IPRAFullGGTransfer.from_classical h)
  have hf : nativeTheory ⊢! PA195Bounded.haltSentence 🡒 haltClassicalᴺ := by
    simpa only [haltClassical, haltMatrix, native, PA195Bounded.haltSentence] using
      theoryNativeForward haltClassical
  have hnative : nativeTheory ⊢! PA195Bounded.haltSentence 🡒 ∼∼nativePARefutation :=
    Entailment.C_trans hf (Entailment.C_trans (Classical.choice hgg)
      (PA196ReverseGG.refutation_backward PA196PACertificateComplete.certificate))
  exact (DiophantineConsistency.IPRAStandardTheory.provable_iff _).2 ⟨hnative⟩

/-- The two hypotheses are the outstanding PA195 machine reductions. -/
theorem consistency_iff_nonhalting_of_classical_pra
    (forward : PRA ⊢ mappedPARefutation 🡒 haltClassical)
    (reverse : PRA ⊢ haltClassical 🡒 mappedPARefutation) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼PA195Bounded.haltSentence :=
  ⟨PA195Endpoint.consistency_iff_nonhalting
    (Classical.choice (PA195ForwardGG.forward_of_classical_pra forward))
    (Classical.choice (reverse_of_classical_pra reverse))⟩

#print axioms reverse_of_classical_pra
#print axioms consistency_iff_nonhalting_of_classical_pra
end PA195PRAAssembly
