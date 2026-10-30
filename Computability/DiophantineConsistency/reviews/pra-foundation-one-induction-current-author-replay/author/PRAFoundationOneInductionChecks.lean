import DiophantineConsistency.PRAFoundationOneInduction
set_option autoImplicit false
namespace DiophantineConsistency.PRAFoundationOneInductionChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAStageInductionSchema PRAFoundationOneInduction
example (pred : Code 3) (θ : Semiproposition language 1) (hθ : θ.Open)
    (p : (PRA ∪ {(succInd (codedSigma pred)).univCl}) ⊢ (∃⁰ θ).univCl) :
    PRA ⊢ (∃⁰ θ).univCl := PRA_proves_goal_of_succInd pred θ hθ p
#print axioms candidate_proves_with_coded_axiom
#print axioms PRA_proves_goal_of_succInd
end DiophantineConsistency.PRAFoundationOneInductionChecks
