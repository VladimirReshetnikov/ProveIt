import DiophantineConsistency.SharingSeed25Octic
import DiophantineConsistency.SharingSign33Squares

/-! UNCOMPILED diagnostic: extract the 16 symbolic sign25 residuals in a model.
No bridge to sign26 or Jones theorem is claimed. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.SharingSign25Squares
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem seed_zero_iff_residuals (p : Fin 4 → ℤ) (v : Fin 26 → V) :
    InternalZero (SharingSeed25Octic.seed p) v ↔
      ∀ e ∈ SharingSeed25Octic.firstResidual p :: SharingSeed25Octic.remainingResiduals p,
        InternalZero e v := by
  have h := SharingSign33Squares.squareSum_zero_iff
    (SharingSeed25Octic.firstResidual p :: SharingSeed25Octic.remainingResiduals p) v
  simpa only [SharingSign33Squares.squareSum, SharingSign33Squares.square_syntax,
    SharingSeed25Octic.seed] using h
end DiophantineConsistency.SharingSign25Squares

#print axioms DiophantineConsistency.SharingSign25Squares.seed_zero_iff_residuals
