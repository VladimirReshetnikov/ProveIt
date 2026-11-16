import PA196Endpoint
import PA196ForwardGG
import PA196ReverseGG

/-! # Conditional iPRA consistency/nonhalting theorem from classical PRA

The hypotheses are actual classical PRA derivations for both directions,
and the fixed bounded-witness certificate for Foundation's PA refutation
predicate. None of the three hypotheses is established here. -/
set_option autoImplicit false
noncomputable section
namespace PA196PRAAssembly
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRATheory DiophantineConsistency.IPRAStandardTheory
open DiophantineConsistency.IPRAPA196Consistency
open PA196ForwardGG PA196ReverseGG

/-- The requested negative equivalence follows from the three explicit
classical-PRA obligations; this theorem does not discharge those obligations. -/
theorem consistency_iff_nonhalting_of_classical_pra
    (forward : PRA ⊢ mappedPARefutation 🡒 haltClassical)
    (reverse : PRA ⊢ haltClassical 🡒 mappedPARefutation)
    (bound : BoundCertificate) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼PA196Bounded.haltSentence := by
  exact ⟨PA196Endpoint.consistency_iff_nonhalting_of_double_negated_reductions
    (Classical.choice (forward_of_classical_pra forward))
    (Classical.choice (reverse_of_classical_pra reverse bound))⟩

#print axioms consistency_iff_nonhalting_of_classical_pra
end PA196PRAAssembly
