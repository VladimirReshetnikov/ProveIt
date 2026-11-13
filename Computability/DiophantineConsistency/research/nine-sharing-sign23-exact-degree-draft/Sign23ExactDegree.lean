import DiophantineConsistency.Sign23DegreeCompose
import DiophantineConsistency.Sign23DegreeLower

/-! SOURCE-ONLY: combine the checked abstract-expression degree inequalities. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign23ExactDegree

theorem abstract_exact (p : Fin 4 → ℤ) :
    (Sign23AbstractExpression.expression p).toPolynomial.totalDegree = 8 :=
  Nat.le_antisymm (Sign23SyntaxDegree.expression_polynomial_degree_le p)
    (Sign23LeadingRows.expression_polynomial_degree_ge p)

theorem current_exact :
    Sign23CurrentExpression.expression.toPolynomial.totalDegree = 8 :=
  abstract_exact CurrentWindowCarry2011.ports
end DiophantineConsistency.Sign23ExactDegree
#print axioms DiophantineConsistency.Sign23ExactDegree.abstract_exact
#print axioms DiophantineConsistency.Sign23ExactDegree.current_exact
