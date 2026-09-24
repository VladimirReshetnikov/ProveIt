import Mathlib.NumberTheory.Dioph
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Connecting polynomial functions and multivariate polynomials

Mathlib's Diophantine predicates use `IsPoly`, an inductive description of
integer-valued functions on natural assignments. These functions are exactly
the evaluations of ordinary integer multivariate polynomials. Neither
direction requires the variable type to be finite.
-/

namespace Diophantine

/-- Evaluation of an integer multivariate polynomial on natural assignments
is a polynomial function in Mathlib's Diophantine sense. -/
theorem isPoly_eval_mvPolynomial {α : Type*} (p : MvPolynomial α ℤ) :
    IsPoly (fun v : α → ℕ => MvPolynomial.eval (fun idx => (v idx : ℤ)) p) := by
  induction p using MvPolynomial.induction_on with
  | C coeff =>
      simpa only [MvPolynomial.eval_C] using (IsPoly.const (α := α) coeff)
  | add p q hp hq =>
      simpa only [MvPolynomial.eval_add, zero_sub, sub_neg_eq_add] using
        hp.sub ((IsPoly.const 0).sub hq)
  | mul_X p idx hp =>
      simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_X] using
        hp.mul (IsPoly.proj idx)

/-- The inductive polynomial-function predicate is equivalent to evaluation
of an ordinary integer multivariate polynomial. -/
theorem isPoly_iff_exists_mvPolynomial {α : Type*} {f : (α → ℕ) → ℤ} :
    IsPoly f ↔ ∃ p : MvPolynomial α ℤ,
      ∀ v, MvPolynomial.eval (fun idx => (v idx : ℤ)) p = f v := by
  constructor
  · intro hf
    induction hf with
    | proj idx =>
        exact ⟨MvPolynomial.X idx, fun _ => MvPolynomial.eval_X _⟩
    | const coeff =>
        exact ⟨MvPolynomial.C coeff, fun _ => MvPolynomial.eval_C _⟩
    | sub _ _ ihf ihg =>
        obtain ⟨p, hp⟩ := ihf
        obtain ⟨q, hq⟩ := ihg
        refine ⟨p - q, fun v => ?_⟩
        simp only [MvPolynomial.eval_sub, hp v, hq v]
    | mul _ _ ihf ihg =>
        obtain ⟨p, hp⟩ := ihf
        obtain ⟨q, hq⟩ := ihg
        refine ⟨p * q, fun v => ?_⟩
        simp only [MvPolynomial.eval_mul, hp v, hq v]
  · rintro ⟨p, hp⟩
    have heq : (fun v : α → ℕ =>
        MvPolynomial.eval (fun idx => (v idx : ℤ)) p) = f := funext hp
    rw [← heq]
    exact isPoly_eval_mvPolynomial p

end Diophantine
