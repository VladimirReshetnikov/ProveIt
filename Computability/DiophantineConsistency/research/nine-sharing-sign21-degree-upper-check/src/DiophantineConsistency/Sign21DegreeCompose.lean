import DiophantineConsistency.Sign21DegreeResiduals

/-! SOURCE-ONLY: compose seed, input-removal, and polynomial degree bounds. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign21SyntaxDegree

theorem seed_degree_le (p : Fin 4 → ℤ) : degree (SharingSeed21Degree14.seed p) ≤ 14 := by
  change max (degree (SharingSeed21Degree14.firstResidual p) +
      degree (SharingSeed21Degree14.firstResidual p))
    (degree (QuarticSyntax.sumExpressions
      ((SharingSeed21Degree14.remainingResiduals p).map fun e => e * e))) ≤ 14
  apply max_le
  · have h := first_degree_le p
    omega
  · exact sum_squares_degree_le _ (remaining_degree_le p)

theorem expression_degree_le (p : Fin 4 → ℤ) :
    degree (Sign21AbstractExpression.expression p) ≤ 14 := by
  exact (removeInput_degree_le (SharingSeed21Degree14.seed p)).trans (seed_degree_le p)

theorem expression_polynomial_degree_le (p : Fin 4 → ℤ) :
    (Sign21AbstractExpression.expression p).toPolynomial.totalDegree ≤ 14 :=
  (polynomial_degree_le _).trans (expression_degree_le p)

theorem current_polynomial_degree_le :
    Sign21CurrentExpression.expression.toPolynomial.totalDegree ≤ 14 :=
  expression_polynomial_degree_le CurrentWindowCarry2011.ports
end DiophantineConsistency.Sign21SyntaxDegree
#print axioms DiophantineConsistency.Sign21SyntaxDegree.seed_degree_le
#print axioms DiophantineConsistency.Sign21SyntaxDegree.expression_degree_le
#print axioms DiophantineConsistency.Sign21SyntaxDegree.expression_polynomial_degree_le
#print axioms DiophantineConsistency.Sign21SyntaxDegree.current_polynomial_degree_le
