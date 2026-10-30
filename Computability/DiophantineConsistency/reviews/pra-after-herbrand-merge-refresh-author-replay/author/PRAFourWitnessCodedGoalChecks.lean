import DiophantineConsistency.PRAFourWitnessCodedGoal
set_option autoImplicit false
namespace DiophantineConsistency.PRAFourWitnessCodedGoalChecks
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAUniversalCandidate PRAStageCodedChi
  HerbrandFourTriplePrenexAdapter HerbrandFixedGoalWeakening PRAFourWitnessCodedGoal
example {m : ℕ} (pred : Code (m+3)) (θ : Semiproposition language 1) (hθ : θ.Open)
    (p : UniversalAxiom ⊢
      (∃⁰ (∃⁰ (∃⁰ (∃⁰ (∀⁰ (∀⁰ (∀⁰ (sourceMatrix (chiMatrix pred) (liftGoal θ))))))))).univCl) :
    PRA ⊢ (∃⁰ θ).univCl := PRA_proves_goal pred θ hθ p
#print axioms PRA_proves_goal
end DiophantineConsistency.PRAFourWitnessCodedGoalChecks
