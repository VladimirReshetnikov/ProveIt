import DiophantineConsistency.Sign22DegreeCompose
import DiophantineConsistency.Sign22DegreeLower

/-! SOURCE-ONLY: combine the checked abstract-expression degree inequalities. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign22ExactDegree

theorem abstract_exact (p : Fin 4 → ℤ) :
    (Sign22AbstractExpression.expression p).toPolynomial.totalDegree = 12 :=
  Nat.le_antisymm (Sign22SyntaxDegree.expression_polynomial_degree_le p)
    (Sign22LeadingRows.expression_polynomial_degree_ge p)

theorem current_exact :
    Sign22CurrentExpression.expression.toPolynomial.totalDegree = 12 :=
  abstract_exact CurrentWindowCarry2011.ports
end DiophantineConsistency.Sign22ExactDegree
#print axioms DiophantineConsistency.Sign22ExactDegree.abstract_exact
#print axioms DiophantineConsistency.Sign22ExactDegree.current_exact
