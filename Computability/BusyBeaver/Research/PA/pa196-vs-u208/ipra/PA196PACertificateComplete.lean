import PA196PACoreBound
import PA196PACoreComplete

/-! The exact PA-refutation witness-bound certificate is unconditional.
The machine-to-refutation reduction remains an explicit separate hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace PA196PACertificateComplete
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.PRATheory DiophantineConsistency.IPRANativeTheory
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open PA196ForwardGG

theorem certificate : PA196ReverseGG.BoundCertificate :=
  PA196PACoreBound.boundCertificate_of_core
    (fun _ _ _ _ _ => PA196PACoreComplete.wb_core_sigma)
    (fun _ _ _ _ _ => PA196PACoreComplete.wb_core_neg_pi)

theorem reverse_of_classical_pra
    (h : PRA ⊢ haltClassical 🡒 mappedPARefutation) :
    standardTheory ⊢ PA196Bounded.haltSentence 🡒 ∼∼nativePARefutation :=
  PA196ReverseGG.reverse_of_classical_pra h certificate

#print axioms certificate
#print axioms reverse_of_classical_pra
end PA196PACertificateComplete
