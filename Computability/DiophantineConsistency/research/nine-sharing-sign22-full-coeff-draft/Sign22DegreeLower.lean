import DiophantineConsistency.Sign22SeedCoefficient
import DiophantineConsistency.Sign22DiagonalDegree

/-! SOURCE-ONLY: connect the seed axis coefficient to the direct expression. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign22LeadingRows
open MvPolynomial

theorem diagonal_eval (e : Expr (Fin 22)) :
    diagonal e.toPolynomial = e.evalRing diagonalVars := by
  induction e <;> simp_all [diagonal, Expr.toPolynomial, Expr.evalRing]
  exact map_intCast (MvPolynomial.eval₂Hom MvPolynomial.C diagonalVars) _

theorem direct_axis (p : Fin 4 → ℤ) :
    diagonal (Sign22AbstractExpression.expression p).toPolynomial =
      (SharingSeed22Dodecic.seed p).evalRing axisPoly := by
  rw [diagonal_eval]
  change ((SharingSeed22Dodecic.seed p).subst
    (Fin.cons (.constant 1) (fun i => .var i))).evalRing diagonalVars = _
  rw [ModelJonesSyntax.evalRing_subst]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · fin_cases j <;> rfl

theorem expression_polynomial_degree_ge (p : Fin 4 → ℤ) :
    12 ≤ (Sign22AbstractExpression.expression p).toPolynomial.totalDegree := by
  have hcoeff : coeff index12 (diagonal (Sign22AbstractExpression.expression p).toPolynomial) = 272 := by
    rw [direct_axis]
    exact seed_axis_coeff p
  have hne : coeff index12 (diagonal (Sign22AbstractExpression.expression p).toPolynomial) ≠ 0 := by
    rw [hcoeff]
    norm_num
  have hdiag : 12 ≤ (diagonal (Sign22AbstractExpression.expression p).toPolynomial).totalDegree := by
    by_contra hn
    have hlt : (diagonal (Sign22AbstractExpression.expression p).toPolynomial).totalDegree <
        ∑ i ∈ index12.support, index12 i := by
      rw [index12_sum]
      omega
    exact hne (MvPolynomial.coeff_eq_zero_of_totalDegree_lt hlt)
  exact hdiag.trans (diagonal_totalDegree_le _)
end DiophantineConsistency.Sign22LeadingRows
#print axioms DiophantineConsistency.Sign22LeadingRows.diagonal_eval
#print axioms DiophantineConsistency.Sign22LeadingRows.direct_axis
#print axioms DiophantineConsistency.Sign22LeadingRows.expression_polynomial_degree_ge
