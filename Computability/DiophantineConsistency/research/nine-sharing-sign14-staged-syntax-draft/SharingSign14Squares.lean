import DiophantineConsistency.SharingSeed14Degree124
import DiophantineConsistency.SharingSign33Squares

/-! SOURCE-ONLY candidate: square decomposition for sign14. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.SharingSign14Squares
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem seed_zero_iff_residuals (p : Fin 4 → ℤ) (v : Fin 15 → V) :
    InternalZero (SharingSeed14Degree124.seed p) v ↔
      ∀ e ∈ SharingSeed14Degree124.firstResidual p :: SharingSeed14Degree124.remainingResiduals p,
        InternalZero e v := by
  have h := SharingSign33Squares.squareSum_zero_iff
    (SharingSeed14Degree124.firstResidual p :: SharingSeed14Degree124.remainingResiduals p) v
  simpa only [SharingSign33Squares.squareSum, SharingSign33Squares.square_syntax,
    SharingSeed14Degree124.seed] using h
end DiophantineConsistency.SharingSign14Squares
#print axioms DiophantineConsistency.SharingSign14Squares.seed_zero_iff_residuals
