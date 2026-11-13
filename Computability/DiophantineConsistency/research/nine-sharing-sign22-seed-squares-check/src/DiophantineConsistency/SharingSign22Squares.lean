import DiophantineConsistency.SharingSeed22Dodecic
import DiophantineConsistency.SharingSign33Squares

/-! SOURCE-ONLY candidate: square decomposition for sign22. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.SharingSign22Squares
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem seed_zero_iff_residuals (p : Fin 4 → ℤ) (v : Fin 23 → V) :
    InternalZero (SharingSeed22Dodecic.seed p) v ↔
      ∀ e ∈ SharingSeed22Dodecic.firstResidual p :: SharingSeed22Dodecic.remainingResiduals p,
        InternalZero e v := by
  have h := SharingSign33Squares.squareSum_zero_iff
    (SharingSeed22Dodecic.firstResidual p :: SharingSeed22Dodecic.remainingResiduals p) v
  simpa only [SharingSign33Squares.squareSum, SharingSign33Squares.square_syntax,
    SharingSeed22Dodecic.seed] using h
end DiophantineConsistency.SharingSign22Squares
#print axioms DiophantineConsistency.SharingSign22Squares.seed_zero_iff_residuals
