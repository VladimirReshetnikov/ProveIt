import DiophantineConsistency.Sign17DegreeResiduals

/-! SOURCE-ONLY: compose seed, input-removal, and polynomial degree bounds. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17SyntaxDegree

theorem seed_degree_le (p : Fin 4 → ℤ) : degree (SharingSeed17Degree96.seed p) ≤ 96 := by
  change max (degree (SharingSeed17Degree96.firstResidual p) +
      degree (SharingSeed17Degree96.firstResidual p))
    (degree (QuarticSyntax.sumExpressions
      ((SharingSeed17Degree96.remainingResiduals p).map fun e => e * e))) ≤ 96
  apply max_le
  · have h := first_degree_le p
    omega
  · exact sum_squares_degree_le _ (remaining_degree_le p)

theorem expression_degree_le (p : Fin 4 → ℤ) :
    degree (Sign17AbstractExpression.expression p) ≤ 96 := by
  exact (removeInput_degree_le (SharingSeed17Degree96.seed p)).trans (seed_degree_le p)

theorem expression_polynomial_degree_le (p : Fin 4 → ℤ) :
    (Sign17AbstractExpression.expression p).toPolynomial.totalDegree ≤ 96 :=
  (polynomial_degree_le _).trans (expression_degree_le p)

theorem current_polynomial_degree_le :
    Sign17CurrentExpression.expression.toPolynomial.totalDegree ≤ 96 :=
  expression_polynomial_degree_le CurrentWindowCarry2011.ports
end DiophantineConsistency.Sign17SyntaxDegree
#print axioms DiophantineConsistency.Sign17SyntaxDegree.seed_degree_le
#print axioms DiophantineConsistency.Sign17SyntaxDegree.expression_degree_le
#print axioms DiophantineConsistency.Sign17SyntaxDegree.expression_polynomial_degree_le
#print axioms DiophantineConsistency.Sign17SyntaxDegree.current_polynomial_degree_le
