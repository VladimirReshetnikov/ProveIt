import DiophantineConsistency.Sign21AxisCoeffLemmas

/-! SOURCE-ONLY: the coefficient of the actual sign21 seed on the axis. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign21LeadingRow
open MvPolynomial

set_option maxHeartbeats 4000000 in
theorem leading_count (p : Fin 4 → ℤ) :
    (SharingSeed21Degree14.remainingResiduals p).count leading = 1 := by
  change 1 = 1
  rfl

theorem seed_axis_coeff (p : Fin 4 → ℤ) :
    coeff index14 ((SharingSeed21Degree14.seed p).evalRing axisPoly) = 1 := by
  have hf := square_coeff_zero (SharingSeed21Degree14.firstResidual p) (first_weighted_degree_le p)
  have hr := remaining_coeff p (SharingSeed21Degree14.remainingResiduals p) (by intro e he; exact he)
  rw [leading_count] at hr
  simp only [SharingSeed21Degree14.seed, Expr.evalRing_add, Expr.evalRing_mul,
    ModelJonesSyntax.evalRing_sumExpressions, List.map_map, Function.comp_apply]
  change coeff index14
    ((SharingSeed21Degree14.firstResidual p).evalRing axisPoly *
      (SharingSeed21Degree14.firstResidual p).evalRing axisPoly +
      axisSquares (SharingSeed21Degree14.remainingResiduals p)) = 1
  rw [MvPolynomial.coeff_add, hf, hr]
  norm_num
end DiophantineConsistency.Sign21LeadingRow
#print axioms DiophantineConsistency.Sign21LeadingRow.leading_count
#print axioms DiophantineConsistency.Sign21LeadingRow.seed_axis_coeff
