import DiophantineConsistency.Sign20DegreeResiduals

/-! SOURCE-ONLY: compose seed, input-removal, and polynomial degree bounds. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign20SyntaxDegree

theorem seed_degree_le (p : Fin 4 → ℤ) : degree (SharingSeed20Degree20.seed p) ≤ 20 := by
  change max (degree (SharingSeed20Degree20.firstResidual p) +
      degree (SharingSeed20Degree20.firstResidual p))
    (degree (QuarticSyntax.sumExpressions
      ((SharingSeed20Degree20.remainingResiduals p).map fun e => e * e))) ≤ 20
  apply max_le
  · have h := first_degree_le p
    omega
  · exact sum_squares_degree_le _ (remaining_degree_le p)

theorem expression_degree_le (p : Fin 4 → ℤ) :
    degree (Sign20AbstractExpression.expression p) ≤ 20 := by
  exact (removeInput_degree_le (SharingSeed20Degree20.seed p)).trans (seed_degree_le p)

theorem expression_polynomial_degree_le (p : Fin 4 → ℤ) :
    (Sign20AbstractExpression.expression p).toPolynomial.totalDegree ≤ 20 :=
  (polynomial_degree_le _).trans (expression_degree_le p)

theorem current_polynomial_degree_le :
    Sign20CurrentExpression.expression.toPolynomial.totalDegree ≤ 20 :=
  expression_polynomial_degree_le CurrentWindowCarry2011.ports
end DiophantineConsistency.Sign20SyntaxDegree
#print axioms DiophantineConsistency.Sign20SyntaxDegree.seed_degree_le
#print axioms DiophantineConsistency.Sign20SyntaxDegree.expression_degree_le
#print axioms DiophantineConsistency.Sign20SyntaxDegree.expression_polynomial_degree_le
#print axioms DiophantineConsistency.Sign20SyntaxDegree.current_polynomial_degree_le
