import DiophantineConsistency.Sign14Optimized95Expression
import DiophantineConsistency.Sign14ExactDegree

/-! SOURCE-ONLY: transfer exact degree to the 95-gate current expression. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Optimized95Current

def expression : Expr (Fin 14) :=
  Sign14Optimized95Expression.expression CurrentWindowCarry2011.ports

theorem totalDegree_eq : expression.toPolynomial.totalDegree = 124 := by
  unfold expression
  rw [Sign14Optimized95Expression.polynomial_eq]
  exact Sign14ExactDegree.current_exact
end DiophantineConsistency.Sign14Optimized95Current
#print axioms DiophantineConsistency.Sign14Optimized95Current.totalDegree_eq
