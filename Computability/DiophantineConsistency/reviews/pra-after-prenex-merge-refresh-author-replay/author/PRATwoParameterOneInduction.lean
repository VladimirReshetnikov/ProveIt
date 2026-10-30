import DiophantineConsistency.PRATwoParameterInductionTransfer
import DiophantineConsistency.PRATwoParameterPacking
/-! Eliminate one bounded Σ₁ induction instance with two free parameters. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRATwoParameterOneInduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRAOpenOneInduction PRATwoParameterInductionTransfer PRATwoParameterPacking

theorem PRA_proves_goal_of_two_parameter_induction
    (ψ : Semisentence language 4) (hψ : Hierarchy 𝚺 0 ψ)
    (θ : Semiproposition language 1) (hθ : θ.Open)
    (p : (PRA ∪ {(succInd (twoSigma ψ)).univCl}) ⊢ (∃⁰ θ).univCl) :
    PRA ⊢ (∃⁰ θ).univCl := by
  apply PRATwoParameterInductionTransfer.PRA_proves_goal_of_two_parameter_induction
    ψ (packed ψ) (packed_bounded ψ hψ) ?_ θ hθ p
  intro M _ _ _ _
  exact modelPacking ψ
end DiophantineConsistency.PRATwoParameterOneInduction
