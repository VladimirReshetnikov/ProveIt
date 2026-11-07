import DiophantineConsistency.SharingSeed27Sextic
import DiophantineConsistency.SharingSign33Squares

/-! UNCOMPILED diagnostic: extract the 18 symbolic sign27 residuals in a model.
No bridge to sign28 or sextic Jones theorem is claimed. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.SharingSign27Squares
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem seed_zero_iff_residuals (p : Fin 4 → ℤ) (v : Fin 28 → V) :
    InternalZero (SharingSeed27Sextic.seed p) v ↔
      ∀ e ∈ SharingSeed27Sextic.firstResidual p :: SharingSeed27Sextic.remainingResiduals p,
        InternalZero e v := by
  have h := SharingSign33Squares.squareSum_zero_iff
    (SharingSeed27Sextic.firstResidual p :: SharingSeed27Sextic.remainingResiduals p) v
  simpa only [SharingSign33Squares.squareSum, SharingSign33Squares.square_syntax,
    SharingSeed27Sextic.seed] using h
end DiophantineConsistency.SharingSign27Squares

#print axioms DiophantineConsistency.SharingSign27Squares.seed_zero_iff_residuals
