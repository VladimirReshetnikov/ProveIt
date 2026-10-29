import DiophantineConsistency.AdaptiveEquationSyntax2011
import DiophantineConsistency.NativeAdaptiveGraph

/-! Exact binding of the adaptive expression to the accepted polynomial. -/
set_option Elab.async false
namespace DiophantineConsistency.NativeAdaptiveExpression2011
open AdaptiveEquationSyntax2011

/-- The literal expression computes exactly the accepted integer graph. -/
theorem eval_expressionAt (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) :
    (expressionAt p).eval v = NativeAdaptiveGraph.value p v := by
  simp only [expressionAt, NativeAdaptiveGraph.value, NativeAdaptiveGraph.core,
    Expr.eval_add, Expr.eval_sub, Expr.eval_mul, Expr.eval_var, Expr.eval_constant]
  rfl

/-- Binding to the actual polynomial includes every coefficient and gate. -/
theorem polynomial_expressionAt (p : Fin 4 → ℤ) :
    (expressionAt p).toPolynomial = NativeAdaptiveGraph.polynomial p := by
  apply MvPolynomial.funext
  intro v
  rw [Expr.eval_toPolynomial, eval_expressionAt, NativeAdaptiveGraph.eval_polynomial]

theorem split_zero_iff (p : Fin 4 → ℤ) (v : Fin 13 → ℕ) :
    InternalZero (expressionAt p) v ↔
      MvPolynomial.eval (fun i => (v i : ℤ)) (NativeAdaptiveGraph.polynomial p) = 0 := by
  rw [NativeAdaptiveGraph.eval_polynomial, ← eval_expressionAt, Expr.eval_eq_zero_iff_splitNatural]
  simp only [InternalZero, NatExpr.evalSemiring_nat]

theorem current_polynomial : expression.toPolynomial =
    NativeAdaptiveGraph.polynomial CurrentWindowCarry2011.ports :=
  polynomial_expressionAt _

end DiophantineConsistency.NativeAdaptiveExpression2011
