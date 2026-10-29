import DiophantineConsistency.NativeAdaptiveExpression2011

set_option Elab.async false
namespace DiophantineConsistency.NativeAdaptiveExpression2011Checks
open AdaptiveEquationSyntax2011 NativeAdaptiveExpression2011

example (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) :
    (expressionAt p).eval v = NativeAdaptiveGraph.value p v := eval_expressionAt p v
example (p : Fin 4 → ℤ) :
    (expressionAt p).toPolynomial = NativeAdaptiveGraph.polynomial p := polynomial_expressionAt p
example (p : Fin 4 → ℤ) (v : Fin 13 → ℕ) :
    InternalZero (expressionAt p) v ↔
      MvPolynomial.eval (fun i => (v i : ℤ)) (NativeAdaptiveGraph.polynomial p) = 0 := split_zero_iff p v
example : expression.toPolynomial = NativeAdaptiveGraph.polynomial CurrentWindowCarry2011.ports := current_polynomial

#print axioms eval_expressionAt
#print axioms polynomial_expressionAt
#print axioms split_zero_iff
#print axioms current_polynomial
end DiophantineConsistency.NativeAdaptiveExpression2011Checks
