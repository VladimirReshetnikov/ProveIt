import DiophantineConsistency.Sign21DegreeCompose
import DiophantineConsistency.Sign21DegreeLower

/-! SOURCE-ONLY: combine the checked abstract-expression degree inequalities. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign21ExactDegree

theorem abstract_exact (p : Fin 4 → ℤ) :
    (Sign21AbstractExpression.expression p).toPolynomial.totalDegree = 14 :=
  Nat.le_antisymm (Sign21SyntaxDegree.expression_polynomial_degree_le p)
    (Sign21LeadingRow.expression_polynomial_degree_ge p)

theorem current_exact :
    Sign21CurrentExpression.expression.toPolynomial.totalDegree = 14 :=
  abstract_exact CurrentWindowCarry2011.ports
end DiophantineConsistency.Sign21ExactDegree
#print axioms DiophantineConsistency.Sign21ExactDegree.abstract_exact
#print axioms DiophantineConsistency.Sign21ExactDegree.current_exact
