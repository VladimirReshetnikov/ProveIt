import DiophantineConsistency.Sign14DegreeResiduals

/-! SOURCE-ONLY: compose seed, input-removal, and polynomial degree bounds. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14SyntaxDegree

theorem seed_degree_le (p : Fin 4 → ℤ) : degree (SharingSeed14Degree124.seed p) ≤ 124 := by
  change max (degree (SharingSeed14Degree124.firstResidual p) +
      degree (SharingSeed14Degree124.firstResidual p))
    (degree (QuarticSyntax.sumExpressions
      ((SharingSeed14Degree124.remainingResiduals p).map fun e => e * e))) ≤ 124
  apply max_le
  · have h := first_degree_le p
    omega
  · exact sum_squares_degree_le _ (remaining_degree_le p)

theorem expression_degree_le (p : Fin 4 → ℤ) :
    degree (Sign14AbstractExpression.expression p) ≤ 124 := by
  exact (removeInput_degree_le (SharingSeed14Degree124.seed p)).trans (seed_degree_le p)

theorem expression_polynomial_degree_le (p : Fin 4 → ℤ) :
    (Sign14AbstractExpression.expression p).toPolynomial.totalDegree ≤ 124 :=
  (polynomial_degree_le _).trans (expression_degree_le p)

theorem current_polynomial_degree_le :
    Sign14CurrentExpression.expression.toPolynomial.totalDegree ≤ 124 :=
  expression_polynomial_degree_le CurrentWindowCarry2011.ports
end DiophantineConsistency.Sign14SyntaxDegree
#print axioms DiophantineConsistency.Sign14SyntaxDegree.seed_degree_le
#print axioms DiophantineConsistency.Sign14SyntaxDegree.expression_degree_le
#print axioms DiophantineConsistency.Sign14SyntaxDegree.expression_polynomial_degree_le
#print axioms DiophantineConsistency.Sign14SyntaxDegree.current_polynomial_degree_le
