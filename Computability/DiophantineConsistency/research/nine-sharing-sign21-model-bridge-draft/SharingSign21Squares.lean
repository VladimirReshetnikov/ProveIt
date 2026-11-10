import DiophantineConsistency.SharingSeed21Degree14
import DiophantineConsistency.SharingSign33Squares

/-! SOURCE-ONLY candidate: square decomposition for sign21. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.SharingSign21Squares
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem seed_zero_iff_residuals (p : Fin 4 → ℤ) (v : Fin 22 → V) :
    InternalZero (SharingSeed21Degree14.seed p) v ↔
      ∀ e ∈ SharingSeed21Degree14.firstResidual p :: SharingSeed21Degree14.remainingResiduals p,
        InternalZero e v := by
  have h := SharingSign33Squares.squareSum_zero_iff
    (SharingSeed21Degree14.firstResidual p :: SharingSeed21Degree14.remainingResiduals p) v
  simpa only [SharingSign33Squares.squareSum, SharingSign33Squares.square_syntax,
    SharingSeed21Degree14.seed] using h
end DiophantineConsistency.SharingSign21Squares
#print axioms DiophantineConsistency.SharingSign21Squares.seed_zero_iff_residuals
