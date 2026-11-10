import DiophantineConsistency.Sign22AxisCoeffLemmas

/-! SOURCE-ONLY: the twelfth coefficient of the actual sign22 seed on the axis. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign22LeadingRows
open MvPolynomial

set_option maxHeartbeats 4000000 in
theorem n0_count (p : Fin 4 → ℤ) :
    (SharingSeed22Dodecic.remainingResiduals p).count n0 = 1 := by
  change 1 = 1
  rfl

set_option maxHeartbeats 4000000 in
theorem dc2_count (p : Fin 4 → ℤ) :
    (SharingSeed22Dodecic.remainingResiduals p).count dc2 = 1 := by
  change 1 = 1
  rfl

theorem seed_axis_coeff (p : Fin 4 → ℤ) :
    coeff index12 ((SharingSeed22Dodecic.seed p).evalRing axisPoly) = 272 := by
  have hf := square_coeff_zero (SharingSeed22Dodecic.firstResidual p) (first_weighted_degree_le p)
  have hr := remaining_coeff p (SharingSeed22Dodecic.remainingResiduals p) (by intro e he; exact he)
  rw [n0_count, dc2_count] at hr
  simp only [SharingSeed22Dodecic.seed, Expr.evalRing_add, Expr.evalRing_mul,
    ModelJonesSyntax.evalRing_sumExpressions, List.map_map]
  change coeff index12
    ((SharingSeed22Dodecic.firstResidual p).evalRing axisPoly *
      (SharingSeed22Dodecic.firstResidual p).evalRing axisPoly +
      axisSquares (SharingSeed22Dodecic.remainingResiduals p)) = 272
  rw [MvPolynomial.coeff_add, hf, hr]
  norm_num
end DiophantineConsistency.Sign22LeadingRows
#print axioms DiophantineConsistency.Sign22LeadingRows.n0_count
#print axioms DiophantineConsistency.Sign22LeadingRows.dc2_count
#print axioms DiophantineConsistency.Sign22LeadingRows.seed_axis_coeff
