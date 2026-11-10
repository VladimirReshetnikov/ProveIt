import DiophantineConsistency.SharingSeed24Octic
import DiophantineConsistency.SharingSign33Squares

/-! SOURCE-ONLY candidate: square decomposition for sign24. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.SharingSign24Squares
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem seed_zero_iff_residuals (p : Fin 4 → ℤ) (v : Fin 25 → V) :
    InternalZero (SharingSeed24Octic.seed p) v ↔
      ∀ e ∈ SharingSeed24Octic.firstResidual p :: SharingSeed24Octic.remainingResiduals p,
        InternalZero e v := by
  have h := SharingSign33Squares.squareSum_zero_iff
    (SharingSeed24Octic.firstResidual p :: SharingSeed24Octic.remainingResiduals p) v
  simpa only [SharingSign33Squares.squareSum, SharingSign33Squares.square_syntax,
    SharingSeed24Octic.seed] using h
end DiophantineConsistency.SharingSign24Squares
#print axioms DiophantineConsistency.SharingSign24Squares.seed_zero_iff_residuals
