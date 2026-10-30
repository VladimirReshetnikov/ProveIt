import DiophantineConsistency.AdaptiveFactor87HA
import DiophantineConsistency.ParsonsISigmaZeroComparison

/-! Candidate-PRA proof of the equivalence between the two adaptive equations. -/
set_option autoImplicit false
namespace DiophantineConsistency.AdaptiveFactor87PRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory AdaptiveFactor87HA

/-- Candidate PRA proves the mapped equivalence of the parent and 87-gate
no-zero sentences. No consistency equivalence is assumed or concluded. -/
theorem candidate_proves_equivalence :
    PRA ⊢ Semiformula.lMap embedding (source 🡘 reduced) :=
  ParsonsISigmaZeroComparison.comparison isigma0_proves_equivalence
end DiophantineConsistency.AdaptiveFactor87PRA
