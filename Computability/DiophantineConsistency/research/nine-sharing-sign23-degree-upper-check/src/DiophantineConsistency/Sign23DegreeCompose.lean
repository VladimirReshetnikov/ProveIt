import DiophantineConsistency.Sign23DegreeResiduals

/-! SOURCE-ONLY: compose seed, input-removal, and polynomial degree bounds. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign23SyntaxDegree

theorem seed_degree_le (p : Fin 4 → ℤ) : degree (SharingSeed23Octic.seed p) ≤ 8 := by
  change max (degree (SharingSeed23Octic.firstResidual p) +
      degree (SharingSeed23Octic.firstResidual p))
    (degree (QuarticSyntax.sumExpressions
      ((SharingSeed23Octic.remainingResiduals p).map fun e => e * e))) ≤ 8
  apply max_le
  · have h := first_degree_le p
    omega
  · exact sum_squares_degree_le _ (remaining_degree_le p)

theorem expression_degree_le (p : Fin 4 → ℤ) :
    degree (Sign23AbstractExpression.expression p) ≤ 8 := by
  exact (removeInput_degree_le (SharingSeed23Octic.seed p)).trans (seed_degree_le p)

theorem expression_polynomial_degree_le (p : Fin 4 → ℤ) :
    (Sign23AbstractExpression.expression p).toPolynomial.totalDegree ≤ 8 :=
  (polynomial_degree_le _).trans (expression_degree_le p)

theorem current_polynomial_degree_le :
    Sign23CurrentExpression.expression.toPolynomial.totalDegree ≤ 8 :=
  expression_polynomial_degree_le CurrentWindowCarry2011.ports
end DiophantineConsistency.Sign23SyntaxDegree
#print axioms DiophantineConsistency.Sign23SyntaxDegree.seed_degree_le
#print axioms DiophantineConsistency.Sign23SyntaxDegree.expression_degree_le
#print axioms DiophantineConsistency.Sign23SyntaxDegree.expression_polynomial_degree_le
#print axioms DiophantineConsistency.Sign23SyntaxDegree.current_polynomial_degree_le
