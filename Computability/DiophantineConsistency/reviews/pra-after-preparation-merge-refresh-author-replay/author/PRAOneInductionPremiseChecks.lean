import DiophantineConsistency.PRAOneInductionPremise
set_option autoImplicit false
namespace DiophantineConsistency.PRAOneInductionPremiseChecks
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAUniversalCandidate PRAStageCodedInduction PRAOneInductionPremise
example (pred : Code (0+3)) (θ : Semiproposition language 1) (hθ : θ.Open)
    (p : (UniversalAxiom ∪ { (inductionFormula pred).univCl }) ⊢ (∃⁰ θ).univCl) :
    PRA ⊢ (∃⁰ θ).univCl := PRA_proves_goal_of_one_axiom pred θ hθ p
#print axioms closedInduction_eval_independent
#print axioms universal_disjunction_of_one_axiom
#print axioms universal_proves_premise
#print axioms PRA_proves_goal_of_one_axiom
end DiophantineConsistency.PRAOneInductionPremiseChecks
