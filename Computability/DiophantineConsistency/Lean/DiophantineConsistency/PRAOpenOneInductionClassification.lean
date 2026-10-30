import DiophantineConsistency.PRAOpenOneInduction
/-! The arbitrary open-matrix predicate is syntactically Σ₁. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAOpenOneInductionClassification
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRAOpenOneInduction

theorem openSigma_sigma (ψ : Semisentence language 3) (hψ : ψ.Open) :
    Hierarchy 𝚺 1 (openSigma ψ) := by
  unfold openSigma
  apply Hierarchy.sigma
  apply Hierarchy.of_open
  exact Semiformula.rew_open_iff.mpr hψ
end DiophantineConsistency.PRAOpenOneInductionClassification
