import DiophantineConsistency.Sign14Optimized86Expression

/-! SOURCE-ONLY: compose 86-to-90 and 90-to-92 seed evaluation. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Optimized86To92

theorem eval_expression {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (Sign14Optimized86Expression.expression p).evalRing v =
      (Sign32GenericRemoveInput.removeInput (Sign14Optimized92.seed p)).evalRing v := by
  calc
    _ = (Sign32GenericRemoveInput.removeInput (Sign14Optimized90.seed p)).evalRing v :=
      Sign14Optimized86Expression.eval_expression p v
    _ = _ := by
      rw [Sign32GenericRemoveInput.eval_removeInput, Sign32GenericRemoveInput.eval_removeInput]
      exact Sign14Optimized90.seed_eval p _

theorem polynomial_eq (p : Fin 4 → ℤ) :
    (Sign14Optimized86Expression.expression p).toPolynomial =
      (Sign32GenericRemoveInput.removeInput (Sign14Optimized92.seed p)).toPolynomial := by
  have h := eval_expression p (MvPolynomial.X : Fin 14 → MvPolynomial (Fin 14) ℤ)
  simpa only [Expr.evalRing_X] using h
end DiophantineConsistency.Sign14Optimized86To92
#print axioms DiophantineConsistency.Sign14Optimized86To92.eval_expression
#print axioms DiophantineConsistency.Sign14Optimized86To92.polynomial_eq
