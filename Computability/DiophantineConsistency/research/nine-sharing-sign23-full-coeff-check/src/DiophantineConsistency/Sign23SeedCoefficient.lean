import DiophantineConsistency.Sign23AxisCoeffLemmas

/-! SOURCE-ONLY: the eighth coefficient of the actual sign23 seed on the axis. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign23LeadingRows
open MvPolynomial

set_option maxHeartbeats 4000000 in
theorem n0_count (p : Fin 4 → ℤ) :
    (SharingSeed23Octic.remainingResiduals p).count n0 = 1 := by
  change 1 = 1
  rfl

set_option maxHeartbeats 4000000 in
theorem dc2_count (p : Fin 4 → ℤ) :
    (SharingSeed23Octic.remainingResiduals p).count dc2 = 1 := by
  change 1 = 1
  rfl

theorem seed_axis_coeff (p : Fin 4 → ℤ) :
    coeff index8 ((SharingSeed23Octic.seed p).evalRing axisPoly) = 2 := by
  have hf := square_coeff_zero (SharingSeed23Octic.firstResidual p) (first_weighted_degree_le p)
  have hr := remaining_coeff p (SharingSeed23Octic.remainingResiduals p) (by intro e he; exact he)
  rw [n0_count, dc2_count] at hr
  simp only [SharingSeed23Octic.seed, Expr.evalRing_add, Expr.evalRing_mul,
    ModelJonesSyntax.evalRing_sumExpressions, List.map_map]
  change coeff index8
    ((SharingSeed23Octic.firstResidual p).evalRing axisPoly *
      (SharingSeed23Octic.firstResidual p).evalRing axisPoly +
      axisSquares (SharingSeed23Octic.remainingResiduals p)) = 2
  rw [MvPolynomial.coeff_add, hf, hr]
  norm_num
end DiophantineConsistency.Sign23LeadingRows
#print axioms DiophantineConsistency.Sign23LeadingRows.n0_count
#print axioms DiophantineConsistency.Sign23LeadingRows.dc2_count
#print axioms DiophantineConsistency.Sign23LeadingRows.seed_axis_coeff
