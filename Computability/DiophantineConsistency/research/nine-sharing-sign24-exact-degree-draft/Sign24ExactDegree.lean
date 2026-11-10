import DiophantineConsistency.Sign24DegreeCompose
import DiophantineConsistency.Sign24DegreeLower

/-! SOURCE-ONLY: combine the checked abstract-expression degree inequalities. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign24ExactDegree

theorem abstract_exact (p : Fin 4 → ℤ) :
    (Sign24AbstractExpression.expression p).toPolynomial.totalDegree = 8 :=
  Nat.le_antisymm (Sign24SyntaxDegree.expression_polynomial_degree_le p)
    (Sign24LeadingN0.expression_polynomial_degree_ge p)

theorem current_exact :
    Sign24CurrentExpression.expression.toPolynomial.totalDegree = 8 :=
  abstract_exact CurrentWindowCarry2011.ports
end DiophantineConsistency.Sign24ExactDegree
#print axioms DiophantineConsistency.Sign24ExactDegree.abstract_exact
#print axioms DiophantineConsistency.Sign24ExactDegree.current_exact
