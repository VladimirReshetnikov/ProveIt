import DiophantineConsistency.Sign14Optimized94Expression
import DiophantineConsistency.Sign14Optimized95Degree

/-! SOURCE-ONLY: transfer exact degree from the 95-gate expression. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Optimized94Current

def expression : Expr (Fin 14) :=
  Sign14Optimized94Expression.expression CurrentWindowCarry2011.ports

theorem totalDegree_eq : expression.toPolynomial.totalDegree = 124 := by
  unfold expression
  rw [Sign14Optimized94Expression.polynomial_eq]
  exact Sign14Optimized95Current.totalDegree_eq
end DiophantineConsistency.Sign14Optimized94Current
#print axioms DiophantineConsistency.Sign14Optimized94Current.totalDegree_eq
