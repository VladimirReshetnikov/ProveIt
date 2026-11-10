import DiophantineConsistency.Sign20DegreeCompose
import DiophantineConsistency.Sign20DegreeLower
import DiophantineConsistency.Sign20CurrentBeta

/-! SOURCE-ONLY: combine conditional degree inequalities and current positivity. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign20ExactDegree

theorem abstract_exact (p : Fin 4 → ℤ) (hp : p 0 ≠ 0) :
    (Sign20AbstractExpression.expression p).toPolynomial.totalDegree = 20 :=
  Nat.le_antisymm (Sign20SyntaxDegree.expression_polynomial_degree_le p)
    (Sign20LeadingRows.expression_polynomial_degree_ge p hp)

theorem current_exact :
    Sign20CurrentExpression.expression.toPolynomial.totalDegree = 20 :=
  abstract_exact CurrentWindowCarry2011.ports Sign20CurrentBeta.nonzero
end DiophantineConsistency.Sign20ExactDegree
#print axioms DiophantineConsistency.Sign20ExactDegree.abstract_exact
#print axioms DiophantineConsistency.Sign20ExactDegree.current_exact
