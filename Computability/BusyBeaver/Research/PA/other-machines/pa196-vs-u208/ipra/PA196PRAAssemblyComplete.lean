import PA196PRAAssembly
import PA196PACertificateComplete

/-! The iPRA PA196 endpoint with its exact witness-bound certificate
unconditionally discharged; both machine/refutation reductions remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace PA196PRAAssemblyComplete
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRATheory DiophantineConsistency.IPRAStandardTheory
open DiophantineConsistency.IPRAPA196Consistency
open PA196ForwardGG

theorem consistency_iff_nonhalting_of_classical_pra
    (forward : PRA ⊢ mappedPARefutation 🡒 haltClassical)
    (reverse : PRA ⊢ haltClassical 🡒 mappedPARefutation) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼PA196Bounded.haltSentence :=
  PA196PRAAssembly.consistency_iff_nonhalting_of_classical_pra
    forward reverse PA196PACertificateComplete.certificate

#print axioms consistency_iff_nonhalting_of_classical_pra
end PA196PRAAssemblyComplete
