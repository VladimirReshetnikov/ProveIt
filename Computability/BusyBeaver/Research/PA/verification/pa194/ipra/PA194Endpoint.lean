import PA194Bounded
import DiophantineConsistency.IPRAPA196Consistency

/-! Conditional iPRA endpoint for the pinned PA194 machine. Both
machine-specific implications remain explicit hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace PA194Endpoint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.IPRAStandardTheory
open DiophantineConsistency.IPRAPA196Consistency

/-- The exact desired negative equivalence follows from these two reductions;
    neither hypothesis is proved here. -/
def consistency_iff_nonhalting
    (refutation_implies_not_not_halt :
      standardTheory ⊢! nativePARefutation 🡒 ∼∼PA194Bounded.haltSentence)
    (halt_implies_not_not_refutation :
      standardTheory ⊢! PA194Bounded.haltSentence 🡒 ∼∼nativePARefutation) :
    standardTheory ⊢! nativePAConsistency 🡘 ∼PA194Bounded.haltSentence := by
  unfold nativePAConsistency
  exact Entailment.K_intro
    (Entailment.C_trans Entailment.dni (Entailment.contra halt_implies_not_not_refutation))
    (Entailment.C_trans Entailment.dni (Entailment.contra refutation_implies_not_not_halt))

#print axioms consistency_iff_nonhalting
end PA194Endpoint
