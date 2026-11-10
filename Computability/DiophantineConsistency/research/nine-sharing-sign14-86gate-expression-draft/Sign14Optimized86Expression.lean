import DiophantineConsistency.Sign14Optimized86

/-! SOURCE-ONLY: fixed-input expression and polynomial transfer from 86 to 90. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Optimized86Expression

def expression (p : Fin 4 → ℤ) : Expr (Fin 14) :=
  Sign32GenericRemoveInput.removeInput (Sign14Optimized86.seed p)

theorem eval_expression {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (expression p).evalRing v =
      (Sign32GenericRemoveInput.removeInput (Sign14Optimized90.seed p)).evalRing v := by
  unfold expression
  rw [Sign32GenericRemoveInput.eval_removeInput, Sign32GenericRemoveInput.eval_removeInput]
  exact Sign14Optimized86.seed_eval p _

theorem polynomial_eq (p : Fin 4 → ℤ) :
    (expression p).toPolynomial =
      (Sign32GenericRemoveInput.removeInput (Sign14Optimized90.seed p)).toPolynomial := by
  have h := eval_expression p (MvPolynomial.X : Fin 14 → MvPolynomial (Fin 14) ℤ)
  simpa only [Expr.evalRing_X] using h
end DiophantineConsistency.Sign14Optimized86Expression
#print axioms DiophantineConsistency.Sign14Optimized86Expression.eval_expression
#print axioms DiophantineConsistency.Sign14Optimized86Expression.polynomial_eq
