import DiophantineConsistency.Sign24SeedCoefficient
import DiophantineConsistency.Sign24DiagonalDegree

/-! SOURCE-ONLY: connect the seed axis coefficient to the direct expression. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign24LeadingN0
open MvPolynomial

theorem diagonal_eval (e : Expr (Fin 24)) :
    diagonal e.toPolynomial = e.evalRing diagonalVars := by
  induction e <;> simp_all [diagonal, Expr.toPolynomial, Expr.evalRing]
  exact map_intCast (MvPolynomial.eval₂Hom MvPolynomial.C diagonalVars) _

theorem direct_axis (p : Fin 4 → ℤ) :
    diagonal (Sign24AbstractExpression.expression p).toPolynomial =
      (SharingSeed24Octic.seed p).evalRing axisPoly := by
  rw [diagonal_eval]
  change ((SharingSeed24Octic.seed p).subst
    (Fin.cons (.constant 1) (fun i => .var i))).evalRing diagonalVars = _
  rw [ModelJonesSyntax.evalRing_subst]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · fin_cases j <;> rfl

theorem expression_polynomial_degree_ge (p : Fin 4 → ℤ) :
    8 ≤ (Sign24AbstractExpression.expression p).toPolynomial.totalDegree := by
  have hcoeff : coeff index8 (diagonal (Sign24AbstractExpression.expression p).toPolynomial) = 1 := by
    rw [direct_axis]
    exact seed_axis_coeff p
  have hne : coeff index8 (diagonal (Sign24AbstractExpression.expression p).toPolynomial) ≠ 0 := by
    rw [hcoeff]
    norm_num
  have hdiag : 8 ≤ (diagonal (Sign24AbstractExpression.expression p).toPolynomial).totalDegree := by
    by_contra hn
    have hlt : (diagonal (Sign24AbstractExpression.expression p).toPolynomial).totalDegree <
        ∑ i ∈ index8.support, index8 i := by
      rw [index8_sum]
      omega
    exact hne (MvPolynomial.coeff_eq_zero_of_totalDegree_lt hlt)
  exact hdiag.trans (diagonal_totalDegree_le _)
end DiophantineConsistency.Sign24LeadingN0
#print axioms DiophantineConsistency.Sign24LeadingN0.diagonal_eval
#print axioms DiophantineConsistency.Sign24LeadingN0.direct_axis
#print axioms DiophantineConsistency.Sign24LeadingN0.expression_polynomial_degree_ge
