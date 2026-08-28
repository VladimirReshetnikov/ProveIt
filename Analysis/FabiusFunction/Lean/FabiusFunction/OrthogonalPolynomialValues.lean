import FabiusFunction.OrthogonalPolynomialConstruction
import FabiusFunction.MomentHankelValues

/-!
# Exact low-order orthogonal polynomials of the up-measure

The first concrete instances of the determinant construction: since
`m₀ = 1` and `m₁ = 0`, the degree-one determinant polynomial is
already the identity, `h₁P₁(x) = x`, and the monic orthogonal
polynomial `P₁` is the monomial `x` itself.  (The degree-zero instance
`P₀ = 1` lives in `OrthogonalPolynomialConstruction`, where it needs
no moment values.)
-/

set_option autoImplicit false

open MeasureTheory Matrix

namespace Fabius

/-- The degree-one determinant polynomial is the identity monomial:
`h₁P₁(x) = x`. -/
theorem hankelOrthoPolynomial_one (F : BoundedFabius)
    (hF : IsFabius F) :
    hankelOrthoPolynomial F 1 = Polynomial.X := by
  have h0 : ((momentBordered F 1 0).submatrix (Fin.last 1).succAbove
      (0 : Fin 2).succAbove).det = upMoment F 1 := by
    rw [Matrix.det_fin_one, Matrix.submatrix_apply]
    have hrow : (Fin.last 1).succAbove (0 : Fin 1) = (0 : Fin 2) := rfl
    have hcol : (0 : Fin 2).succAbove (0 : Fin 1) = (1 : Fin 2) := rfl
    rw [hrow, hcol]
    simp [momentBordered]
  have h1 : ((momentBordered F 1 0).submatrix (Fin.last 1).succAbove
      (1 : Fin 2).succAbove).det = upMoment F 0 := by
    rw [Matrix.det_fin_one, Matrix.submatrix_apply]
    have hrow : (Fin.last 1).succAbove (0 : Fin 1) = (0 : Fin 2) := rfl
    have hcol : (1 : Fin 2).succAbove (0 : Fin 1) = (0 : Fin 2) := rfl
    rw [hrow, hcol]
    simp [momentBordered]
  rw [hankelOrthoPolynomial, Fin.sum_univ_two, h0, h1,
    upMoment_one F hF, upMoment_zero F hF]
  simp [Fin.val_last]

/-- The first monic orthogonal polynomial is the identity monomial,
`P₁(x) = x`. -/
theorem upOrthoPolynomial_one (F : BoundedFabius) (hF : IsFabius F) :
    upOrthoPolynomial F 1 = Polynomial.X := by
  rw [upOrthoPolynomial, hankelOrthoPolynomial_one F hF,
    hankelDet_one F hF]
  norm_num

/-- Sanity instance of the norm identity at `n = 1`: the up-measure's
variance is the Hankel ratio `a₁ = 1/9`. -/
theorem integral_sq_eq_hankelRatio_one (F : BoundedFabius)
    (hF : IsFabius F) :
    ∫ x, x ^ 2 ∂(rvachevMeasure F) = hankelRatio F 1 := by
  have h := integral_upOrthoPolynomial_sq F hF 1
  rw [upOrthoPolynomial_one F hF] at h
  simpa using h
