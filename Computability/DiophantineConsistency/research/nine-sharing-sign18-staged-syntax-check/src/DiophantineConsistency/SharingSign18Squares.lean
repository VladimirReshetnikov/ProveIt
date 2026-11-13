import DiophantineConsistency.SharingSeed18Degree94
import DiophantineConsistency.SharingSign33Squares

/-! SOURCE-ONLY candidate: square decomposition for sign18. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.SharingSign18Squares
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem seed_zero_iff_residuals (p : Fin 4 → ℤ) (v : Fin 19 → V) :
    InternalZero (SharingSeed18Degree94.seed p) v ↔
      ∀ e ∈ SharingSeed18Degree94.firstResidual p :: SharingSeed18Degree94.remainingResiduals p,
        InternalZero e v := by
  have h := SharingSign33Squares.squareSum_zero_iff
    (SharingSeed18Degree94.firstResidual p :: SharingSeed18Degree94.remainingResiduals p) v
  simpa only [SharingSign33Squares.squareSum, SharingSign33Squares.square_syntax,
    SharingSeed18Degree94.seed] using h
end DiophantineConsistency.SharingSign18Squares
#print axioms DiophantineConsistency.SharingSign18Squares.seed_zero_iff_residuals
