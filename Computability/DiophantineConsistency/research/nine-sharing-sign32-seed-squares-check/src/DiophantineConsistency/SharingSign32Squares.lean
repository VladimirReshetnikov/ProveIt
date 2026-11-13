import DiophantineConsistency.SharingSeed32Sextic
import DiophantineConsistency.SharingSign33Squares

/-! UNCOMPILED diagnostic: extract the 23 symbolic sign32 residuals in a model.
No bridge to sign33 or sextic Jones theorem is claimed. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.SharingSign32Squares
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem seed_zero_iff_residuals (p : Fin 4 → ℤ) (v : Fin 33 → V) :
    InternalZero (SharingSeed32Sextic.seed p) v ↔
      ∀ e ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p,
        InternalZero e v := by
  have h := SharingSign33Squares.squareSum_zero_iff
    (SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p) v
  simpa only [SharingSign33Squares.squareSum, SharingSign33Squares.square_syntax,
    SharingSeed32Sextic.seed] using h
end DiophantineConsistency.SharingSign32Squares

#print axioms DiophantineConsistency.SharingSign32Squares.seed_zero_iff_residuals
