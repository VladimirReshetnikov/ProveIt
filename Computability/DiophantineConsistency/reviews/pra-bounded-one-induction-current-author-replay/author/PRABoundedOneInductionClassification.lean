import DiophantineConsistency.PRABoundedOneInduction
/-! A bounded matrix gives a syntactically Σ₁ induction predicate. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRABoundedOneInductionClassification
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRAOpenOneInduction

theorem boundedSigma_sigma (ψ : Semisentence language 3) (hψ : Hierarchy 𝚺 0 ψ) :
    Hierarchy 𝚺 1 (openSigma ψ) := by
  unfold openSigma
  apply Hierarchy.sigma
  exact Hierarchy.rew _ (Hierarchy.zero_eq_alt hψ)
end DiophantineConsistency.PRABoundedOneInductionClassification
