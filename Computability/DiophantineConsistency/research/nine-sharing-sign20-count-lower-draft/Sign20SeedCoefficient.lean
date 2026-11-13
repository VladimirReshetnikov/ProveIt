import DiophantineConsistency.Sign20CountProof

/-! SOURCE-ONLY: the twentieth coefficient of the actual sign20 seed on the axis. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign20LeadingRows
open MvPolynomial

theorem seed_axis_coeff (p : Fin 4 → ℤ) :
    coeff index20 ((SharingSeed20Degree20.seed p).evalRing axisPoly) = 2 * (p 0)^4 := by
  have hf := square_coeff_zero (SharingSeed20Degree20.firstResidual p) (first_weighted_degree_le p)
  have hr := remaining_coeff p (SharingSeed20Degree20.remainingResiduals p) (by intro e he; exact he)
  rw [Sign20CountProof.n0_count, Sign20CountProof.dc2_count] at hr
  simp only [SharingSeed20Degree20.seed, Expr.evalRing_add, Expr.evalRing_mul,
    ModelJonesSyntax.evalRing_sumExpressions, List.map_map]
  change coeff index20
    ((SharingSeed20Degree20.firstResidual p).evalRing axisPoly *
      (SharingSeed20Degree20.firstResidual p).evalRing axisPoly +
      axisSquares (SharingSeed20Degree20.remainingResiduals p)) = 2 * (p 0)^4
  rw [MvPolynomial.coeff_add, hf, hr]
  norm_num
end DiophantineConsistency.Sign20LeadingRows
#print axioms DiophantineConsistency.Sign20LeadingRows.seed_axis_coeff
