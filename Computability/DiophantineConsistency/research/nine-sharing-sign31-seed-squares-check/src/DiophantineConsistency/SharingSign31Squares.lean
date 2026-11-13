import DiophantineConsistency.SharingSeed31Sextic
import DiophantineConsistency.SharingSign33Squares

/-! UNCOMPILED diagnostic: extract the 22 symbolic sign31 residuals in a model.
No bridge to sign32 or sextic Jones theorem is claimed. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.SharingSign31Squares
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem seed_zero_iff_residuals (p : Fin 4 → ℤ) (v : Fin 32 → V) :
    InternalZero (SharingSeed31Sextic.seed p) v ↔
      ∀ e ∈ SharingSeed31Sextic.firstResidual p :: SharingSeed31Sextic.remainingResiduals p,
        InternalZero e v := by
  have h := SharingSign33Squares.squareSum_zero_iff
    (SharingSeed31Sextic.firstResidual p :: SharingSeed31Sextic.remainingResiduals p) v
  simpa only [SharingSign33Squares.squareSum, SharingSign33Squares.square_syntax,
    SharingSeed31Sextic.seed] using h
end DiophantineConsistency.SharingSign31Squares

#print axioms DiophantineConsistency.SharingSign31Squares.seed_zero_iff_residuals
