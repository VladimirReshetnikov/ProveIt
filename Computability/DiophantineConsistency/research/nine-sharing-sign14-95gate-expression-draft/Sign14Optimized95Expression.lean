import DiophantineConsistency.Sign14Optimized95

/-! SOURCE-ONLY: fixed-input expression and polynomial transfer. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Optimized95Expression

def expression (p : Fin 4 → ℤ) : Expr (Fin 14) :=
  Sign32GenericRemoveInput.removeInput (Sign14Optimized95.seed p)

theorem eval_expression {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (expression p).evalRing v = (Sign14AbstractExpression.expression p).evalRing v := by
  change (Sign32GenericRemoveInput.removeInput (Sign14Optimized95.seed p)).evalRing v =
    (Sign32GenericRemoveInput.removeInput (SharingSeed14Degree124.seed p)).evalRing v
  rw [Sign32GenericRemoveInput.eval_removeInput, Sign32GenericRemoveInput.eval_removeInput]
  exact Sign14Optimized95.seed_eval p _

theorem polynomial_eq (p : Fin 4 → ℤ) :
    (expression p).toPolynomial = (Sign14AbstractExpression.expression p).toPolynomial := by
  have h := eval_expression p (MvPolynomial.X : Fin 14 → MvPolynomial (Fin 14) ℤ)
  simpa only [Expr.evalRing_X] using h
end DiophantineConsistency.Sign14Optimized95Expression
#print axioms DiophantineConsistency.Sign14Optimized95Expression.eval_expression
#print axioms DiophantineConsistency.Sign14Optimized95Expression.polynomial_eq
