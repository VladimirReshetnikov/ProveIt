import DiophantineConsistency.PRATwoParameterFreeInduction
set_option autoImplicit false
namespace DiophantineConsistency.PRATwoParameterFreeInductionChecks
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAStageCodedInduction PRATwoInductionTagCodes PRATwoParameterFreeInduction
example (first second : Code 2) (θ : Semiproposition language 1) (hθ : θ.Open)
    (p : ((PRA ∪ {(inductionFormula (liftTwo first)).univCl}) ∪
      {(inductionFormula (liftTwo second)).univCl}) ⊢ (∃⁰ θ).univCl) :
    PRA ⊢ (∃⁰ θ).univCl := PRA_proves_goal first second θ hθ p
#print axioms PRATwoInductionTagged.PRA_proves_goal_of_two_tagged
#print axioms PRA_proves_zero_substitution
#print axioms PRA_proves_one_substitution
#print axioms PRA_proves_goal
end DiophantineConsistency.PRATwoParameterFreeInductionChecks
