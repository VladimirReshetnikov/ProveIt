import DiophantineConsistency.Sign14Optimized86To92
import DiophantineConsistency.Sign14Optimized92Degree

/-! SOURCE-ONLY: transfer exact degree from the 93-gate expression. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Optimized86Current

def expression : Expr (Fin 14) :=
  Sign14Optimized86Expression.expression CurrentWindowCarry2011.ports

theorem totalDegree_eq : expression.toPolynomial.totalDegree = 124 := by
  unfold expression
  rw [Sign14Optimized86To92.polynomial_eq]
  exact Sign14Optimized92Current.totalDegree_eq
end DiophantineConsistency.Sign14Optimized86Current
#print axioms DiophantineConsistency.Sign14Optimized86Current.totalDegree_eq
