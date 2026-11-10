import DiophantineConsistency.Sign24DegreeResiduals

/-! SOURCE-ONLY: compose seed, input-removal, and polynomial degree bounds. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign24SyntaxDegree

theorem seed_degree_le (p : Fin 4 → ℤ) : degree (SharingSeed24Octic.seed p) ≤ 8 := by
  change max (degree (SharingSeed24Octic.firstResidual p) +
      degree (SharingSeed24Octic.firstResidual p))
    (degree (QuarticSyntax.sumExpressions
      ((SharingSeed24Octic.remainingResiduals p).map fun e => e * e))) ≤ 8
  apply max_le
  · have h := first_degree_le p
    omega
  · exact sum_squares_degree_le _ (remaining_degree_le p)

theorem expression_degree_le (p : Fin 4 → ℤ) :
    degree (Sign24AbstractExpression.expression p) ≤ 8 := by
  exact (removeInput_degree_le (SharingSeed24Octic.seed p)).trans (seed_degree_le p)

theorem expression_polynomial_degree_le (p : Fin 4 → ℤ) :
    (Sign24AbstractExpression.expression p).toPolynomial.totalDegree ≤ 8 :=
  (polynomial_degree_le _).trans (expression_degree_le p)

theorem current_polynomial_degree_le :
    Sign24CurrentExpression.expression.toPolynomial.totalDegree ≤ 8 :=
  expression_polynomial_degree_le CurrentWindowCarry2011.ports
end DiophantineConsistency.Sign24SyntaxDegree
#print axioms DiophantineConsistency.Sign24SyntaxDegree.seed_degree_le
#print axioms DiophantineConsistency.Sign24SyntaxDegree.expression_degree_le
#print axioms DiophantineConsistency.Sign24SyntaxDegree.expression_polynomial_degree_le
#print axioms DiophantineConsistency.Sign24SyntaxDegree.current_polynomial_degree_le
