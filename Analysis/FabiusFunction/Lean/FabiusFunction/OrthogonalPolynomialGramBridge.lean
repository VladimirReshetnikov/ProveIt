import FabiusFunction.FiniteMomentJacobi
import FabiusFunction.OrthogonalPolynomialParity

/-!
# The generic Gram--Stieltjes construction specializes to the up measure

`FiniteMomentGram` and `GramStieltjes` develop moment functionals, Hankel
matrices, and monic orthogonal polynomials for an arbitrary scalar moment
sequence.  The older up-measure development constructs the same objects
directly from Bochner integrals and bordered determinants.  This module proves
that the two interfaces agree.

The key bridge is the polynomial integration formula

`momentFunctional (upMoment F) p = ∫ x, p.eval x ∂rvachevMeasure F`.

It identifies the generic Hankel matrix and determinant definitionally with
their up-specific counterparts.  Uniqueness of the generic monic orthogonal
polynomial then identifies it with `upOrthoPolynomial`.  The result is a
one-way dependency from the reusable finite algebra to the analytic up-law
pipeline; neither foundational module imports the other.
-/

set_option autoImplicit false

open MeasureTheory Polynomial

namespace Fabius

noncomputable section

/-- The generic polynomial moment functional of the up-moment sequence is
integration against the canonical up measure. -/
theorem momentFunctional_upMoment_eq_integral (F : BoundedFabius)
    (hF : IsFabius F) (p : Polynomial ℝ) :
    momentFunctional (upMoment F) p =
      ∫ x, p.eval x ∂(rvachevMeasure F) := by
  rw [momentFunctional_eq_sum_range (upMoment F) p p.natDegree le_rfl]
  have heval : (fun x : ℝ ↦ p.eval x) = fun x : ℝ ↦
      ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * x ^ k := by
    funext x
    rw [Polynomial.eval_eq_sum_range]
  rw [heval, integral_finsetSum _ fun k _ ↦
    (integrable_pow_rvachevMeasure F hF k).const_mul (p.coeff k)]
  apply Finset.sum_congr rfl
  intro k _
  rw [MeasureTheory.integral_const_mul]
  rfl

/-- The generic moment pairing for the up moments is the integral of the
product of the two polynomial evaluations. -/
theorem momentPairing_upMoment_eq_integral (F : BoundedFabius)
    (hF : IsFabius F) (p q : Polynomial ℝ) :
    momentPairing (upMoment F) p q =
      ∫ x, p.eval x * q.eval x ∂(rvachevMeasure F) := by
  rw [momentPairing_apply, momentFunctional_upMoment_eq_integral F hF]
  simp only [Polynomial.eval_mul]

/-- The up-specific Hankel matrix is the generic Hankel matrix of the
up-moment sequence. -/
theorem momentHankel_eq_momentHankelMatrix (F : BoundedFabius) (n : ℕ) :
    momentHankel F n = momentHankelMatrix (upMoment F) n := by
  rfl

/-- The up-specific Hankel determinant is the generic determinant of the
up-moment sequence. -/
theorem hankelDet_eq_momentHankelDet (F : BoundedFabius) (n : ℕ) :
    hankelDet F n = momentHankelDet (upMoment F) n := by
  rfl

/-- The generic Gram--Stieltjes polynomial of the up-moment sequence is
exactly the monic orthogonal polynomial constructed directly from the up
measure. -/
theorem upOrthoPolynomial_eq_gramStieltjesPolynomial
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    upOrthoPolynomial F n = gramStieltjesPolynomial (upMoment F) n := by
  have hdet : momentHankelDet (upMoment F) n ≠ 0 := by
    rw [← hankelDet_eq_momentHankelDet]
    exact ne_of_gt (hankelDet_pos F hF n)
  refine eq_gramStieltjesPolynomial_of_isMonicOfDegree_of_orthogonal
    (upMoment F) n hdet (upOrthoPolynomial F n) ?_ ?_
  · exact ⟨natDegree_upOrthoPolynomial F hF n,
      upOrthoPolynomial_monic F hF n⟩
  · intro q hq
    rw [momentPairing_upMoment_eq_integral F hF]
    simpa only [Polynomial.eval_mul] using
      integral_upOrthoPolynomial_mul_eval F hF n q hq

/-- The two fraction-free determinant polynomials agree as well: the bordered
Hankel cofactor expansion is the last-adjugate-column construction. -/
theorem hankelOrthoPolynomial_eq_gramStieltjesNumerator
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    hankelOrthoPolynomial F n = gramStieltjesNumerator (upMoment F) n := by
  have h := upOrthoPolynomial_eq_gramStieltjesPolynomial F hF n
  rw [upOrthoPolynomial, gramStieltjesPolynomial,
    ← hankelDet_eq_momentHankelDet] at h
  exact mul_left_cancel₀
    (Polynomial.C_ne_zero.mpr
      (inv_ne_zero (ne_of_gt (hankelDet_pos F hF n)))) h

/-- The up-specific Hankel ratio is the generic Gram--Stieltjes norm
specialized to the up-moment sequence. -/
theorem hankelRatio_eq_gramStieltjesNorm (F : BoundedFabius) (n : ℕ) :
    hankelRatio F n = gramStieltjesNorm (upMoment F) n := by
  rfl

/-- Symmetry of the up measure makes the generic Jacobi diagonal vanish. -/
theorem gramStieltjesJacobiDiagonal_upMoment_eq_zero
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    gramStieltjesJacobiDiagonal (upMoment F) n = 0 := by
  rw [gramStieltjesJacobiDiagonal,
    ← upOrthoPolynomial_eq_gramStieltjesPolynomial F hF n,
    momentPairing_upMoment_eq_integral F hF]
  have h := integral_mul_sq_upOrthoPolynomial_eq_zero F hF n
  have hnum : ∫ x,
      (Polynomial.X * upOrthoPolynomial F n).eval x *
        (upOrthoPolynomial F n).eval x ∂(rvachevMeasure F) = 0 := by
    simpa only [Polynomial.eval_mul, Polynomial.eval_X, pow_two,
      mul_assoc] using h
  rw [hnum, zero_div]

/-- The generic Jacobi subdiagonal of the up moments is the quotient of the
two consecutive up-specific Hankel ratios. -/
theorem gramStieltjesJacobiSubdiagonal_upMoment_eq
    (F : BoundedFabius) (n : ℕ) :
    gramStieltjesJacobiSubdiagonal (upMoment F) n =
      hankelRatio F (n + 1) / hankelRatio F n := by
  rfl

end

end Fabius
