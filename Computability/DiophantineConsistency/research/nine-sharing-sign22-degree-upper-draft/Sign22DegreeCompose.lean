import DiophantineConsistency.Sign22DegreeResiduals

/-! SOURCE-ONLY: compose seed, input-removal, and polynomial degree bounds. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign22SyntaxDegree

theorem seed_degree_le (p : Fin 4 → ℤ) : degree (SharingSeed22Dodecic.seed p) ≤ 12 := by
  change max (degree (SharingSeed22Dodecic.firstResidual p) +
      degree (SharingSeed22Dodecic.firstResidual p))
    (degree (QuarticSyntax.sumExpressions
      ((SharingSeed22Dodecic.remainingResiduals p).map fun e => e * e))) ≤ 12
  apply max_le
  · have h := first_degree_le p
    omega
  · exact sum_squares_degree_le _ (remaining_degree_le p)

theorem expression_degree_le (p : Fin 4 → ℤ) :
    degree (Sign22AbstractExpression.expression p) ≤ 12 := by
  exact (removeInput_degree_le (SharingSeed22Dodecic.seed p)).trans (seed_degree_le p)

theorem expression_polynomial_degree_le (p : Fin 4 → ℤ) :
    (Sign22AbstractExpression.expression p).toPolynomial.totalDegree ≤ 12 :=
  (polynomial_degree_le _).trans (expression_degree_le p)

theorem current_polynomial_degree_le :
    Sign22CurrentExpression.expression.toPolynomial.totalDegree ≤ 12 :=
  expression_polynomial_degree_le CurrentWindowCarry2011.ports
end DiophantineConsistency.Sign22SyntaxDegree
#print axioms DiophantineConsistency.Sign22SyntaxDegree.seed_degree_le
#print axioms DiophantineConsistency.Sign22SyntaxDegree.expression_degree_le
#print axioms DiophantineConsistency.Sign22SyntaxDegree.expression_polynomial_degree_le
#print axioms DiophantineConsistency.Sign22SyntaxDegree.current_polynomial_degree_le
