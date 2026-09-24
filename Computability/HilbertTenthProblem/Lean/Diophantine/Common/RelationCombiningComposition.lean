import Diophantine.Common.RelationCombiningPolynomial

/-!
# Polynomial substitution for the relation-combining construction

The radicands and the four arithmetic parameters may themselves be ordinary
integer multivariate polynomials. Substitution into `core` produces another
ordinary integer polynomial, and its evaluation agrees with `value` applied
to the evaluated inputs. This is an algebraic composition statement only.

The specialization `polynomial q` puts the radicands in `Fin q` and the four
parameters in `Fin 4`, giving a literal polynomial on their disjoint union.
-/

namespace Diophantine.RelationCombiningPolynomial

open MvPolynomial

noncomputable section

variable {σ : Type*}

/-- Substitute the four parameter polynomials for `n`, `B`, `C`, `D`. -/
def parameterSubstitution (n b c d : MvPolynomial σ ℤ) :
    Coeff →+* MvPolynomial σ ℤ :=
  eval₂Hom C ![n, b, c, d]

/-- Compose the relation-combining core with arbitrary integer polynomials.
No finiteness assumption on the target variable type is required. -/
def compose (q : ℕ) (A : Fin q → MvPolynomial σ ℤ)
    (n b c d : MvPolynomial σ ℤ) : MvPolynomial σ ℤ :=
  eval₂ (parameterSubstitution n b c d) A (core q)

/-- Evaluating the substituted coefficients is the original coefficient
evaluation at the four evaluated parameter polynomials. -/
theorem eval_comp_parameterSubstitution (v : σ → ℤ)
    (n b c d : MvPolynomial σ ℤ) :
    (eval v).comp (parameterSubstitution n b c d) =
      coeffEval (eval v n) (eval v b) (eval v c) (eval v d) := by
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [parameterSubstitution, coeffEval]
  · intro i
    fin_cases i <;> simp [parameterSubstitution, coeffEval]

/-- Evaluation commutes with simultaneous substitution of the radicands
and all four arithmetic parameters. -/
theorem eval_compose (q : ℕ) (A : Fin q → MvPolynomial σ ℤ)
    (n b c d : MvPolynomial σ ℤ) (v : σ → ℤ) :
    eval v (compose q A n b c d) =
      value q (fun i => eval v (A i))
        (eval v n) (eval v b) (eval v c) (eval v d) := by
  unfold compose value
  rw [eval₂_comp_left, eval_comp_parameterSubstitution]
  rfl

/-- The literal ordinary integer polynomial. The left coordinates are the
`q` radicands; right coordinates `0`, `1`, `2`, `3` are `n`, `B`, `C`, `D`. -/
def polynomial (q : ℕ) : MvPolynomial (Fin q ⊕ Fin 4) ℤ :=
  compose q (fun i => X (Sum.inl i))
    (X (Sum.inr 0)) (X (Sum.inr 1)) (X (Sum.inr 2)) (X (Sum.inr 3))

/-- The literal polynomial has exactly the same integer values as `core`. -/
theorem eval_polynomial (q : ℕ) (A : Fin q → ℤ) (n b c d : ℤ) :
    eval (Sum.elim A ![n, b, c, d]) (polynomial q) = value q A n b c d := by
  rw [polynomial, eval_compose]
  simp

/-- Evaluation on an arbitrary assignment to the disjoint-union coordinates. -/
theorem eval_polynomial_assignment (q : ℕ) (v : Fin q ⊕ Fin 4 → ℤ) :
    eval v (polynomial q) =
      value q (fun i => v (Sum.inl i))
        (v (Sum.inr 0)) (v (Sum.inr 1)) (v (Sum.inr 2)) (v (Sum.inr 3)) := by
  rw [polynomial, eval_compose]
  simp

end

end Diophantine.RelationCombiningPolynomial
