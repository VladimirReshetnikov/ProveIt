import DiophantineConsistency.Sign14Optimized93Expression
import DiophantineConsistency.Sign14Optimized94Degree

/-! SOURCE-ONLY: transfer exact degree from the 94-gate expression. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Optimized93Current

def expression : Expr (Fin 14) :=
  Sign14Optimized93Expression.expression CurrentWindowCarry2011.ports

theorem totalDegree_eq : expression.toPolynomial.totalDegree = 124 := by
  unfold expression
  rw [Sign14Optimized93Expression.polynomial_eq]
  exact Sign14Optimized94Current.totalDegree_eq
end DiophantineConsistency.Sign14Optimized93Current
#print axioms DiophantineConsistency.Sign14Optimized93Current.totalDegree_eq
