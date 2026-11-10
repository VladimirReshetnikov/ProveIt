import DiophantineConsistency.SharingSeed16Degree112
import DiophantineConsistency.SharingSign33Squares

/-! SOURCE-ONLY candidate: square decomposition for sign16. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.SharingSign16Squares
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem seed_zero_iff_residuals (p : Fin 4 → ℤ) (v : Fin 17 → V) :
    InternalZero (SharingSeed16Degree112.seed p) v ↔
      ∀ e ∈ SharingSeed16Degree112.firstResidual p :: SharingSeed16Degree112.remainingResiduals p,
        InternalZero e v := by
  have h := SharingSign33Squares.squareSum_zero_iff
    (SharingSeed16Degree112.firstResidual p :: SharingSeed16Degree112.remainingResiduals p) v
  simpa only [SharingSign33Squares.squareSum, SharingSign33Squares.square_syntax,
    SharingSeed16Degree112.seed] using h
end DiophantineConsistency.SharingSign16Squares
#print axioms DiophantineConsistency.SharingSign16Squares.seed_zero_iff_residuals
