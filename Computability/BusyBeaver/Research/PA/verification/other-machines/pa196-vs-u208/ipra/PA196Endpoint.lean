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

/-- Both reductions may instead have double-negated conclusions; no
    double-negation elimination is needed for the negative equivalence. -/
def consistency_iff_nonhalting_of_double_negated_reductions
    (refutation_implies_not_not_halt :
      standardTheory ⊢! nativePARefutation 🡒 ∼∼PA196Bounded.haltSentence)
    (halt_implies_not_not_refutation :
      standardTheory ⊢! PA196Bounded.haltSentence 🡒 ∼∼nativePARefutation) :
    standardTheory ⊢! nativePAConsistency 🡘 ∼PA196Bounded.haltSentence := by
  unfold nativePAConsistency
  exact Entailment.K_intro
    (Entailment.C_trans Entailment.dni (Entailment.contra halt_implies_not_not_refutation))
    (Entailment.C_trans Entailment.dni (Entailment.contra refutation_implies_not_not_halt))

#print axioms consistency_iff_nonhalting
#print axioms consistency_iff_nonhalting_of_double_negated_reductions
end PA196Endpoint
