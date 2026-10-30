import DiophantineConsistency.PRATwoInductionTagged
import DiophantineConsistency.PRATwoInductionTagCodes
set_option autoImplicit false
namespace DiophantineConsistency.PRATwoParameterFreeInduction
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAStageCodedInduction PRATwoInductionTagged PRATwoInductionTagCodes

/-- Two coded Σ₁ induction axioms whose predicate bodies do not use the
universal induction parameter can be eliminated simultaneously. The tags are
concrete PR codes, with both substitution identities proved in candidate PRA. -/
theorem PRA_proves_goal (first second : Code 2) (θ : Semiproposition language 1) (hθ : θ.Open)
    (p : ((PRA ∪ {(inductionFormula (liftTwo first)).univCl}) ∪
      {(inductionFormula (liftTwo second)).univCl}) ⊢ (∃⁰ θ).univCl) :
    PRA ⊢ (∃⁰ θ).univCl := by
  apply PRA_proves_goal_of_two_tagged (tagged first second) (liftTwo first) (liftTwo second) zeroTag oneTag
  · exact PRA_proves_zero_substitution first second
  · exact PRA_proves_one_substitution first second
  · exact hθ
  · exact p
end DiophantineConsistency.PRATwoParameterFreeInduction
