import DiophantineConsistency.PRAStageInductionSchema
/-! The explicit induction predicate is strictly Σ₁. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAStageSigmaClassification
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRAFiniteFunctionCodes PRAStageInductionSchema

theorem codedSigma_sigma {n : ℕ} (pred : Code (n+3)) : Hierarchy 𝚺 1 (codedSigma pred) := by
  unfold codedSigma
  apply Hierarchy.sigma
  exact Hierarchy.rel _ _ _ _
end DiophantineConsistency.PRAStageSigmaClassification
