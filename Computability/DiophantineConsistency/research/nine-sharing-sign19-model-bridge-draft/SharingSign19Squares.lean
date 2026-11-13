import DiophantineConsistency.SharingSeed19Degree44
import DiophantineConsistency.SharingSign33Squares

/-! SOURCE-ONLY candidate: square decomposition for sign19. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.SharingSign19Squares
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem seed_zero_iff_residuals (p : Fin 4 → ℤ) (v : Fin 20 → V) :
    InternalZero (SharingSeed19Degree44.seed p) v ↔
      ∀ e ∈ SharingSeed19Degree44.firstResidual p :: SharingSeed19Degree44.remainingResiduals p,
        InternalZero e v := by
  have h := SharingSign33Squares.squareSum_zero_iff
    (SharingSeed19Degree44.firstResidual p :: SharingSeed19Degree44.remainingResiduals p) v
  simpa only [SharingSign33Squares.squareSum, SharingSign33Squares.square_syntax,
    SharingSeed19Degree44.seed] using h
end DiophantineConsistency.SharingSign19Squares
#print axioms DiophantineConsistency.SharingSign19Squares.seed_zero_iff_residuals
