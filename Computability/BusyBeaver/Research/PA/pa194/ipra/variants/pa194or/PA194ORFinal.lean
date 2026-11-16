import PA194ORNonhalt
import PA194NativeLiteralFinal

set_option autoImplicit false

namespace PA194ORFinal
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency

/-- Standard iPRA proves the consistency equivalence for the literal OR table. -/
theorem consistency_iff_literal_nonhalt :
    standardTheory ⊢ nativePAConsistency 🡘 ∼PA194ORNonhalt.haltSentence := by
  have hp := Classical.choice PA194NativeLiteralFinal.consistency_iff_literal_nonhalt
  have hv := Classical.choice PA194ORNonhalt.nonhalt_iff
  exact ⟨K_intro (C_trans (K_left hp) (K_left hv)) (C_trans (K_right hv) (K_right hp))⟩

#print axioms consistency_iff_literal_nonhalt
end PA194ORFinal
