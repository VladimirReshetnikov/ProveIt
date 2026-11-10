import DiophantineConsistency.Current14Carrier65DegreeDirect
import DiophantineConsistency.CurrentEquationSyntax2011
import DiophantineConsistency.WeightedExpressionDegree

/-! Candidate direct expression specialization without the DAG import. -/
namespace DiophantineConsistency.Current14Carrier65DegreeExpression

theorem expression_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (ObjectCurrentEquation2011.expressionAt p).evalRing v =
      Carrier65.value (fun j => (p j : R)) v := by
  simp only [ObjectCurrentEquation2011.expressionAt, Expr.evalRing_add,
    Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_pow, Expr.evalRing_var,
    Expr.evalRing_constant, Expr.evalRing_ofNat, Nat.cast_ofNat, Nat.cast_one,
    Carrier65.value, Carrier65.core]

theorem expression_eq_polynomial (p : Fin 4 → ℤ) :
    (ObjectCurrentEquation2011.expressionAt p).toPolynomial = Carrier65.polynomial p := by
  rw [← Expr.evalRing_X, expression_eval]
  rfl

theorem expression_exact (p : Fin 4 → ℤ) (hp : p 0 ≠ 0) :
    (ObjectCurrentEquation2011.expressionAt p).toPolynomial.totalDegree = 150 := by
  rw [expression_eq_polynomial]
  exact Current14Carrier65DegreeDirect.polynomial_exact p hp

end DiophantineConsistency.Current14Carrier65DegreeExpression

#print axioms DiophantineConsistency.Current14Carrier65DegreeExpression.expression_eq_polynomial
#print axioms DiophantineConsistency.Current14Carrier65DegreeExpression.expression_exact
