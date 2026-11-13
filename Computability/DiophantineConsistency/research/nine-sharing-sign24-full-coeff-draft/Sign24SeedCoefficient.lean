import DiophantineConsistency.Sign24AxisCoeffLemmas

/-! SOURCE-ONLY: the coefficient of the actual sign24 seed on the axis. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign24LeadingN0
open MvPolynomial

set_option maxHeartbeats 4000000 in
theorem n0_count (p : Fin 4 → ℤ) :
    (SharingSeed24Octic.remainingResiduals p).count n0 = 1 := by
  change 1 = 1
  rfl

theorem seed_axis_coeff (p : Fin 4 → ℤ) :
    coeff index8 ((SharingSeed24Octic.seed p).evalRing axisPoly) = 1 := by
  have hf := square_coeff_zero (SharingSeed24Octic.firstResidual p) (first_weighted_degree_le p)
  have hr := remaining_coeff p (SharingSeed24Octic.remainingResiduals p) (by intro e he; exact he)
  rw [n0_count] at hr
  simp only [SharingSeed24Octic.seed, Expr.evalRing_add, Expr.evalRing_mul,
    ModelJonesSyntax.evalRing_sumExpressions, List.map_map, Function.comp_apply]
  change coeff index8
    ((SharingSeed24Octic.firstResidual p).evalRing axisPoly *
      (SharingSeed24Octic.firstResidual p).evalRing axisPoly +
      axisSquares (SharingSeed24Octic.remainingResiduals p)) = 1
  rw [MvPolynomial.coeff_add, hf, hr]
  norm_num
end DiophantineConsistency.Sign24LeadingN0
#print axioms DiophantineConsistency.Sign24LeadingN0.n0_count
#print axioms DiophantineConsistency.Sign24LeadingN0.seed_axis_coeff
