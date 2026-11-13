import DiophantineConsistency.SharingSeed28Sextic
import DiophantineConsistency.SharingSign33Squares

/-! UNCOMPILED diagnostic: extract the 19 symbolic sign28 residuals in a model.
No bridge to sign31 or sextic Jones theorem is claimed. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.SharingSign28Squares
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem seed_zero_iff_residuals (p : Fin 4 → ℤ) (v : Fin 29 → V) :
    InternalZero (SharingSeed28Sextic.seed p) v ↔
      ∀ e ∈ SharingSeed28Sextic.firstResidual p :: SharingSeed28Sextic.remainingResiduals p,
        InternalZero e v := by
  have h := SharingSign33Squares.squareSum_zero_iff
    (SharingSeed28Sextic.firstResidual p :: SharingSeed28Sextic.remainingResiduals p) v
  simpa only [SharingSign33Squares.squareSum, SharingSign33Squares.square_syntax,
    SharingSeed28Sextic.seed] using h
end DiophantineConsistency.SharingSign28Squares

#print axioms DiophantineConsistency.SharingSign28Squares.seed_zero_iff_residuals
