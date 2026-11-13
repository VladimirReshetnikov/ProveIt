import DiophantineConsistency.SharingSeed17Degree96
import DiophantineConsistency.SharingSign33Squares

/-! SOURCE-ONLY candidate: square decomposition for sign17. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.SharingSign17Squares
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem seed_zero_iff_residuals (p : Fin 4 → ℤ) (v : Fin 18 → V) :
    InternalZero (SharingSeed17Degree96.seed p) v ↔
      ∀ e ∈ SharingSeed17Degree96.firstResidual p :: SharingSeed17Degree96.remainingResiduals p,
        InternalZero e v := by
  have h := SharingSign33Squares.squareSum_zero_iff
    (SharingSeed17Degree96.firstResidual p :: SharingSeed17Degree96.remainingResiduals p) v
  simpa only [SharingSign33Squares.squareSum, SharingSign33Squares.square_syntax,
    SharingSeed17Degree96.seed] using h
end DiophantineConsistency.SharingSign17Squares
#print axioms DiophantineConsistency.SharingSign17Squares.seed_zero_iff_residuals
