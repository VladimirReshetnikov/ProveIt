import PA196Bounded
import DiophantineConsistency.IPRAPA196Consistency

/-! # Conditional iPRA endpoint for the exact PA196 halting sentence

The bounded term in `PA196Bounded.haltSentence` has been tied to the imported
literal machine over the standard natural numbers. The consistency side is the
intuitionistic negation of the native reading of Foundation's PA refutation
predicate. The two machine-specific internal implications below remain explicit
hypotheses; this is not an unconditional iPRA consistency theorem. -/
set_option autoImplicit false
noncomputable section
namespace PA196Endpoint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.IPRAStandardTheory
open DiophantineConsistency.IPRAPA196Consistency

/-- If the two required reductions are derived in standard iPRA, the exact
    constructed PA196 halting sentence has the requested negative equivalence. -/
def consistency_iff_nonhalting
    (refutation_implies_halt : standardTheory ⊢! nativePARefutation 🡒 PA196Bounded.haltSentence)
    (halt_implies_not_not_refutation : standardTheory ⊢! PA196Bounded.haltSentence 🡒 ∼∼nativePARefutation) :
    standardTheory ⊢! nativePAConsistency 🡘 ∼PA196Bounded.haltSentence :=
  consistency_iff_nonhalting_of_reductions PA196Bounded.haltSentence
    refutation_implies_halt halt_implies_not_not_refutation

#print axioms consistency_iff_nonhalting
end PA196Endpoint
