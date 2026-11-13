import DiophantineConsistency.Sign24SyntaxDegree

/-! SOURCE-ONLY: bound the concrete sign24 expression's polynomial degree. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign24SyntaxDegree

theorem expression_syntax_degree (p : Fin 4 → ℤ) :
    degree (Sign24AbstractExpression.expression p) = 8 := by
  rfl

theorem expression_polynomial_degree_le (p : Fin 4 → ℤ) :
    (Sign24AbstractExpression.expression p).toPolynomial.totalDegree ≤ 8 := by
  exact (polynomial_degree_le _).trans (le_of_eq (expression_syntax_degree p))

theorem current_polynomial_degree_le :
    Sign24CurrentExpression.expression.toPolynomial.totalDegree ≤ 8 := by
  exact expression_polynomial_degree_le CurrentWindowCarry2011.ports
end DiophantineConsistency.Sign24SyntaxDegree
#print axioms DiophantineConsistency.Sign24SyntaxDegree.expression_syntax_degree
#print axioms DiophantineConsistency.Sign24SyntaxDegree.expression_polynomial_degree_le
#print axioms DiophantineConsistency.Sign24SyntaxDegree.current_polynomial_degree_le
