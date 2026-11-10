import DiophantineConsistency.Sign14PrefixDagAssembly
import DiophantineConsistency.Sign14ExactDegree

/-! SOURCE-ONLY: transfer the exact degree to the fragment-DAG expression. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14PrefixDagCurrent

def expression : Expr (Fin 14) :=
  Sign14PrefixDagAssembly.expression CurrentWindowCarry2011.ports

theorem expression_eq : expression = Sign14CurrentExpression.expression := by
  exact Sign14PrefixDagAssembly.expression_eq CurrentWindowCarry2011.ports

theorem totalDegree_eq : expression.toPolynomial.totalDegree = 124 := by
  rw [expression_eq]
  exact Sign14ExactDegree.current_exact
end DiophantineConsistency.Sign14PrefixDagCurrent
#print axioms DiophantineConsistency.Sign14PrefixDagCurrent.expression_eq
#print axioms DiophantineConsistency.Sign14PrefixDagCurrent.totalDegree_eq
