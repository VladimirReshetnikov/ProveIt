import DiophantineConsistency.AdaptiveEquationSyntax2011
import DiophantineConsistency.NativeAdaptiveGraph

/-! Exact binding of the adaptive expression to the accepted polynomial. -/
set_option Elab.async false
namespace DiophantineConsistency.NativeAdaptiveExpression2011
open AdaptiveEquationSyntax2011

/-- Interpret the finite syntax in an arbitrary commutative ring. -/
private def evalRing {σ R : Type*} [CommRing R] (v : σ → R) : Expr σ → R
  | .constant z => (z : R)
  | .var i => v i
  | .add p q => evalRing v p + evalRing v q
  | .sub p q => evalRing v p - evalRing v q
  | .mul p q => evalRing v p * evalRing v q

private theorem evalRing_X {σ : Type*} (e : Expr σ) :
    evalRing (MvPolynomial.X : σ → MvPolynomial σ ℤ) e = e.toPolynomial := by
  induction e <;> simp_all [evalRing, Expr.toPolynomial]

private theorem evalRing_expressionAt {R : Type*} [CommRing R]
    (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    evalRing v (expressionAt p) = NativeAdaptiveGraph.value (fun j => (p j : R)) v := by
  simp only [expressionAt, evalRing, NativeAdaptiveGraph.value, NativeAdaptiveGraph.core,
    Int.cast_ofNat]

/-- The literal expression computes exactly the accepted integer graph. -/
theorem eval_expressionAt (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) :
    (expressionAt p).eval v = NativeAdaptiveGraph.value p v := by
  simp only [expressionAt, NativeAdaptiveGraph.value, NativeAdaptiveGraph.core,
    Expr.eval_add, Expr.eval_sub, Expr.eval_mul, Expr.eval_var, Expr.eval_constant]
  rfl

/-- Binding to the actual polynomial includes every coefficient and gate. -/
theorem polynomial_expressionAt (p : Fin 4 → ℤ) :
    (expressionAt p).toPolynomial = NativeAdaptiveGraph.polynomial p := by
  rw [← evalRing_X, evalRing_expressionAt]
  rfl

theorem split_zero_iff (p : Fin 4 → ℤ) (v : Fin 13 → ℕ) :
    InternalZero (expressionAt p) v ↔
      MvPolynomial.eval (fun i => (v i : ℤ)) (NativeAdaptiveGraph.polynomial p) = 0 := by
  rw [NativeAdaptiveGraph.eval_polynomial, ← eval_expressionAt, Expr.eval_eq_zero_iff_splitNatural]
  simp only [InternalZero, NatExpr.evalSemiring_nat]

theorem current_polynomial : expression.toPolynomial =
    NativeAdaptiveGraph.polynomial CurrentWindowCarry2011.ports :=
  polynomial_expressionAt _

end DiophantineConsistency.NativeAdaptiveExpression2011
