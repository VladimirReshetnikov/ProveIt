import DiophantineConsistency.SharingSeed20Degree20
import DiophantineConsistency.SharingSign33Squares

/-! SOURCE-ONLY candidate: square decomposition for sign20. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.SharingSign20Squares
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem seed_zero_iff_residuals (p : Fin 4 → ℤ) (v : Fin 21 → V) :
    InternalZero (SharingSeed20Degree20.seed p) v ↔
      ∀ e ∈ SharingSeed20Degree20.firstResidual p :: SharingSeed20Degree20.remainingResiduals p,
        InternalZero e v := by
  have h := SharingSign33Squares.squareSum_zero_iff
    (SharingSeed20Degree20.firstResidual p :: SharingSeed20Degree20.remainingResiduals p) v
  simpa only [SharingSign33Squares.squareSum, SharingSign33Squares.square_syntax,
    SharingSeed20Degree20.seed] using h
end DiophantineConsistency.SharingSign20Squares
#print axioms DiophantineConsistency.SharingSign20Squares.seed_zero_iff_residuals
