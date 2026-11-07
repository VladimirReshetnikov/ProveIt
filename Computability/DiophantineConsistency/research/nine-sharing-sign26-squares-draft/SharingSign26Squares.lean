import DiophantineConsistency.SharingSeed26Sextic
import DiophantineConsistency.SharingSign33Squares

/-! UNCOMPILED diagnostic: extract the 17 symbolic sign26 residuals in a model.
No bridge to sign27 or sextic Jones theorem is claimed. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.SharingSign26Squares
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem seed_zero_iff_residuals (p : Fin 4 → ℤ) (v : Fin 27 → V) :
    InternalZero (SharingSeed26Sextic.seed p) v ↔
      ∀ e ∈ SharingSeed26Sextic.firstResidual p :: SharingSeed26Sextic.remainingResiduals p,
        InternalZero e v := by
  have h := SharingSign33Squares.squareSum_zero_iff
    (SharingSeed26Sextic.firstResidual p :: SharingSeed26Sextic.remainingResiduals p) v
  simpa only [SharingSign33Squares.squareSum, SharingSign33Squares.square_syntax,
    SharingSeed26Sextic.seed] using h
end DiophantineConsistency.SharingSign26Squares

#print axioms DiophantineConsistency.SharingSign26Squares.seed_zero_iff_residuals
