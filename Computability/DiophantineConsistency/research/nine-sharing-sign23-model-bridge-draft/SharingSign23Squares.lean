import DiophantineConsistency.SharingSeed23Octic
import DiophantineConsistency.SharingSign33Squares

/-! SOURCE-ONLY candidate: square decomposition for sign23. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.SharingSign23Squares
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem seed_zero_iff_residuals (p : Fin 4 → ℤ) (v : Fin 24 → V) :
    InternalZero (SharingSeed23Octic.seed p) v ↔
      ∀ e ∈ SharingSeed23Octic.firstResidual p :: SharingSeed23Octic.remainingResiduals p,
        InternalZero e v := by
  have h := SharingSign33Squares.squareSum_zero_iff
    (SharingSeed23Octic.firstResidual p :: SharingSeed23Octic.remainingResiduals p) v
  simpa only [SharingSign33Squares.squareSum, SharingSign33Squares.square_syntax,
    SharingSeed23Octic.seed] using h
end DiophantineConsistency.SharingSign23Squares
#print axioms DiophantineConsistency.SharingSign23Squares.seed_zero_iff_residuals
