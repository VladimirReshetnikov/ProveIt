import DiophantineConsistency.Sign16RowPremises

/-! SOURCE-ONLY extraction of the four remaining non-Nt row evaluations. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign16OtherRows
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingSeed16Degree112 Sign16RowPremises
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem row00_of_seed (p : Fin 4 → ℤ) (v : Fin 17 → V)
    (hz : InternalZero (seed p) v) :
    E p v (shared34 p) - E p v (shared33 p) * (E p v (shared18 p) * E p v (shared18 p)) = 0 := by
  have hm : row00 p ∈ firstResidual p :: remainingResiduals p := by
    simp [firstResidual, remainingResiduals]
  have he := (internalZero_iff _ _).mp ((SharingSign16Squares.seed_zero_iff_residuals p v).mp hz _ hm)
  simpa only [row00, E, Expr.evalRing_sub, Expr.evalRing_mul] using he

theorem row01_of_seed (p : Fin 4 → ℤ) (v : Fin 17 → V)
    (hz : InternalZero (seed p) v) :
    ι (v 15) - ((E p v (shared19 p) * (ι (v 10) + 1) +
      ((ι (v 11) + 1) + (ι (v 12) + 1)) + E p v (shared15 p)) - E p v (shared25 p)) = 0 := by
  have hm : row01 p ∈ firstResidual p :: remainingResiduals p := by
    simp [firstResidual, remainingResiduals]
  have he := (internalZero_iff _ _).mp ((SharingSign16Squares.seed_zero_iff_residuals p v).mp hz _ hm)
  simpa only [row01, E, Expr.evalRing_sub, Expr.evalRing_add, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one] using he

theorem row02_of_seed (p : Fin 4 → ℤ) (v : Fin 17 → V)
    (hz : InternalZero (seed p) v) :
    ι (v 15) * ι (v 15) - E p v (shared27 p) * (E p v (shared27 p) +
      ((ι (v 11) + 1) + (ι (v 12) + 1))) - 1 = 0 := by
  have hm : row02 p ∈ firstResidual p :: remainingResiduals p := by
    simp [firstResidual, remainingResiduals]
  have he := (internalZero_iff _ _).mp ((SharingSign16Squares.seed_zero_iff_residuals p v).mp hz _ hm)
  simpa only [row02, E, Expr.evalRing_sub, Expr.evalRing_add, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one] using he

theorem row06_of_seed (p : Fin 4 → ℤ) (v : Fin 17 → V)
    (hz : InternalZero (seed p) v) :
    E p v (shared33 p) * ((ι (v 5) + 1) * (ι (v 5) + 1)) -
      E p v (shared36 p) - E p v (shared33 p) = 0 := by
  have hm : row06 p ∈ firstResidual p :: remainingResiduals p := by
    simp [firstResidual, remainingResiduals]
  have he := (internalZero_iff _ _).mp ((SharingSign16Squares.seed_zero_iff_residuals p v).mp hz _ hm)
  simpa only [row06, E, Expr.evalRing_sub, Expr.evalRing_add, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one] using he
end DiophantineConsistency.Sign16OtherRows
#print axioms DiophantineConsistency.Sign16OtherRows.row00_of_seed
#print axioms DiophantineConsistency.Sign16OtherRows.row01_of_seed
#print axioms DiophantineConsistency.Sign16OtherRows.row02_of_seed
#print axioms DiophantineConsistency.Sign16OtherRows.row06_of_seed
