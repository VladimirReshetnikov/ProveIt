import DiophantineConsistency.PRAOneInductionCandidateTransfer
set_option autoImplicit false
namespace DiophantineConsistency.PRAOneInductionCandidateTransferChecks
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAStageCodedInduction PRAOneInductionCandidateTransfer
example (pred : Code (0+3)) (θ : Semiproposition language 1) (hθ : θ.Open)
    (p : (PRA ∪ { (inductionFormula pred).univCl }) ⊢ (∃⁰ θ).univCl) :
    PRA ⊢ (∃⁰ θ).univCl := PRA_proves_goal_of_candidate_plus_one pred θ hθ p
#print axioms universal_proves_candidate_plus
#print axioms PRA_proves_goal_of_candidate_plus_one
end DiophantineConsistency.PRAOneInductionCandidateTransferChecks
