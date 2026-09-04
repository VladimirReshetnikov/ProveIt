import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Deterministic polynomial grid certificates

Agreement on a Cartesian grid determines a polynomial whenever each grid
side has more elements than the corresponding degree of the difference.
No characteristic-zero or field hypothesis is needed: an integral domain
suffices. Bounds on the two separate polynomials give a convenient
specialization and an injective evaluation map on the bounded-degree class.

This is the grid certificate of the coefficient-calculus manuscript.
The proof applies Mathlib's multivariate root bound to the difference.
-/

set_option autoImplicit false

namespace Fabius

variable {σ R : Type*} [Finite σ] [CommRing R] [IsDomain R]

/-- Two polynomials are equal if their difference has degree smaller than
each grid side and their evaluations agree throughout the grid. -/
theorem mvPolynomial_eq_of_eval_eq_on_grid
    (P Q : MvPolynomial σ R) (S : σ → Finset R)
    (hdeg : ∀ i, (P - Q).degreeOf i < (S i).card)
    (heval : ∀ x : σ → R, (∀ i, x i ∈ S i) →
      MvPolynomial.eval x P = MvPolynomial.eval x Q) : P = Q := by
  apply sub_eq_zero.mp
  refine MvPolynomial.eq_zero_of_eval_zero_at_prod_finset (P - Q) S hdeg ?_
  intro x hx
  rw [map_sub, heval x hx, sub_self]

/-- Degree bounds on the difference and at least one more node in every
coordinate yield a deterministic equality certificate. -/
theorem mvPolynomial_eq_of_eval_eq_on_grid_of_degreeOf_sub_le
    (P Q : MvPolynomial σ R) (D : σ → ℕ) (S : σ → Finset R)
    (hdeg : ∀ i, (P - Q).degreeOf i ≤ D i)
    (hcard : ∀ i, D i + 1 ≤ (S i).card)
    (heval : ∀ x : σ → R, (∀ i, x i ∈ S i) →
      MvPolynomial.eval x P = MvPolynomial.eval x Q) : P = Q := by
  apply mvPolynomial_eq_of_eval_eq_on_grid P Q S ?_ heval
  intro i
  exact lt_of_lt_of_le (Nat.lt_succ_of_le (hdeg i)) (hcard i)

/-- Separate coordinatewise degree bounds suffice for the grid certificate;
no degree computation of the expanded difference is required. -/
theorem mvPolynomial_eq_of_eval_eq_on_grid_of_degreeOf_le
    (P Q : MvPolynomial σ R) (D : σ → ℕ) (S : σ → Finset R)
    (hP : ∀ i, P.degreeOf i ≤ D i)
    (hQ : ∀ i, Q.degreeOf i ≤ D i)
    (hcard : ∀ i, D i + 1 ≤ (S i).card)
    (heval : ∀ x : σ → R, (∀ i, x i ∈ S i) →
      MvPolynomial.eval x P = MvPolynomial.eval x Q) : P = Q := by
  apply mvPolynomial_eq_of_eval_eq_on_grid_of_degreeOf_sub_le P Q D S ?_ hcard heval
  intro i
  exact (MvPolynomial.degreeOf_sub_le i P Q).trans (max_le (hP i) (hQ i))

/-- Evaluation on a finite Cartesian grid is injective on polynomials whose
degree in each coordinate is smaller than the corresponding grid side. -/
theorem mvPolynomial_grid_eval_injective (S : σ → Finset R) :
    Function.Injective
      (fun P : {P : MvPolynomial σ R // ∀ i, P.degreeOf i < (S i).card} =>
        fun x : {x : σ → R // ∀ i, x i ∈ S i} => MvPolynomial.eval x.val P.val) := by
  intro P Q h
  apply Subtype.ext
  apply mvPolynomial_eq_of_eval_eq_on_grid P.val Q.val S ?_ ?_
  · intro i
    exact lt_of_le_of_lt (MvPolynomial.degreeOf_sub_le i P.val Q.val)
      (max_lt (P.property i) (Q.property i))
  · intro x hx
    exact congrFun h ⟨x, hx⟩

end Fabius
