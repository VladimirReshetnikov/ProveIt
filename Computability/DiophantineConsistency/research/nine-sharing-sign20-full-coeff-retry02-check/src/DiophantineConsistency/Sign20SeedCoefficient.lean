import DiophantineConsistency.Sign20AxisCoeffLemmas

/-! SOURCE-ONLY: the twentieth coefficient of the actual sign20 seed on the axis. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign20LeadingRows
open MvPolynomial

set_option maxHeartbeats 4000000 in
theorem n0_count (p : Fin 4 → ℤ) :
    (SharingSeed20Degree20.remainingResiduals p).count (n0 p) = 1 := by
  simp [SharingSeed20Degree20.remainingResiduals, n0, dc2, e, u, a, delta]

set_option maxHeartbeats 4000000 in
theorem dc2_count (p : Fin 4 → ℤ) :
    (SharingSeed20Degree20.remainingResiduals p).count (dc2 p) = 1 := by
  simp [SharingSeed20Degree20.remainingResiduals, n0, dc2, e, u, a, delta]

theorem seed_axis_coeff (p : Fin 4 → ℤ) :
    coeff index20 ((SharingSeed20Degree20.seed p).evalRing axisPoly) = 2 * (p 0)^4 := by
  have hf := square_coeff_zero (SharingSeed20Degree20.firstResidual p) (first_weighted_degree_le p)
  have hr := remaining_coeff p (SharingSeed20Degree20.remainingResiduals p) (by intro e he; exact he)
  rw [n0_count, dc2_count] at hr
  simp only [SharingSeed20Degree20.seed, Expr.evalRing_add, Expr.evalRing_mul,
    ModelJonesSyntax.evalRing_sumExpressions, List.map_map]
  change coeff index20
    ((SharingSeed20Degree20.firstResidual p).evalRing axisPoly *
      (SharingSeed20Degree20.firstResidual p).evalRing axisPoly +
      axisSquares (SharingSeed20Degree20.remainingResiduals p)) = 2 * (p 0)^4
  rw [MvPolynomial.coeff_add, hf, hr]
  norm_num
end DiophantineConsistency.Sign20LeadingRows
#print axioms DiophantineConsistency.Sign20LeadingRows.n0_count
#print axioms DiophantineConsistency.Sign20LeadingRows.dc2_count
#print axioms DiophantineConsistency.Sign20LeadingRows.seed_axis_coeff
