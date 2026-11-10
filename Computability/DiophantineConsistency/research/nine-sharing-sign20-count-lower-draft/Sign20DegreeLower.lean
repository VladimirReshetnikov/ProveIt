import DiophantineConsistency.Sign20SeedCoefficient
import DiophantineConsistency.Sign20DiagonalDegree

/-! SOURCE-ONLY: connect the seed axis coefficient to the direct expression. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign20LeadingRows
open MvPolynomial

theorem diagonal_eval (e : Expr (Fin 20)) :
    diagonal e.toPolynomial = e.evalRing diagonalVars := by
  induction e <;> simp_all [diagonal, Expr.toPolynomial, Expr.evalRing]
  exact map_intCast (MvPolynomial.eval₂Hom MvPolynomial.C diagonalVars) _

theorem direct_axis (p : Fin 4 → ℤ) :
    diagonal (Sign20AbstractExpression.expression p).toPolynomial =
      (SharingSeed20Degree20.seed p).evalRing axisPoly := by
  rw [diagonal_eval]
  change ((SharingSeed20Degree20.seed p).subst
    (Fin.cons (.constant 1) (fun i => .var i))).evalRing diagonalVars = _
  rw [ModelJonesSyntax.evalRing_subst]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · fin_cases j <;> rfl

theorem expression_polynomial_degree_ge (p : Fin 4 → ℤ) (hp : p 0 ≠ 0) :
    20 ≤ (Sign20AbstractExpression.expression p).toPolynomial.totalDegree := by
  have hcoeff : coeff index20 (diagonal (Sign20AbstractExpression.expression p).toPolynomial) = 2 * (p 0)^4 := by
    rw [direct_axis]
    exact seed_axis_coeff p
  have hne : coeff index20 (diagonal (Sign20AbstractExpression.expression p).toPolynomial) ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 4 hp)
  have hdiag : 20 ≤ (diagonal (Sign20AbstractExpression.expression p).toPolynomial).totalDegree := by
    by_contra hn
    have hlt : (diagonal (Sign20AbstractExpression.expression p).toPolynomial).totalDegree <
        ∑ i ∈ index20.support, index20 i := by
      rw [index20_sum]
      omega
    exact hne (MvPolynomial.coeff_eq_zero_of_totalDegree_lt hlt)
  exact hdiag.trans (diagonal_totalDegree_le _)
end DiophantineConsistency.Sign20LeadingRows
#print axioms DiophantineConsistency.Sign20LeadingRows.diagonal_eval
#print axioms DiophantineConsistency.Sign20LeadingRows.direct_axis
#print axioms DiophantineConsistency.Sign20LeadingRows.expression_polynomial_degree_ge
