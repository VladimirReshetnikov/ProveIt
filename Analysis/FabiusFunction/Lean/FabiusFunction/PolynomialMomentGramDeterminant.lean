import FabiusFunction.FiniteMomentJacobi
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Polynomial changes of basis for moment Gram determinants

This module isolates the finite change-of-basis calculation behind Gram
determinants in a polynomial basis.  For a coherent family `p : ℕ → R[X]`,
whose `k`-th member has degree at most `k`, let `C_n` be the matrix whose
`j`-th column is the coefficient vector of `p j`.  Then the Gram matrix of
the first `n` family members for an arbitrary moment pairing is

`G_n = C_nᵀ H_n C_n`,

where `H_n` is the monomial Hankel matrix.  Since `C_n` is upper triangular,
its determinant is the product of the diagonal coefficients.  Taking
determinants therefore gives

`det G_n = (∏_{j<n} coeff (p j) j)² det H_n`.

The final theorem transports the Hankel cross-ratio for the finite
Gram--Stieltjes Jacobi subdiagonal through any such polynomial basis.  No
measure, positivity, orthogonality, root theorem, or infinite continued
fraction is used.
-/

set_option autoImplicit false

open Finset Polynomial
open scoped BigOperators

namespace Fabius

noncomputable section

/-! ## Coefficient and Gram matrices -/

/-- The order-`n` coefficient matrix of a polynomial family.  Its `j`-th
column is the coefficient vector of `p j` in the monomial basis. -/
def polynomialCoefficientMatrix {R : Type*} [Semiring R]
    (p : ℕ → R[X]) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  fun i j ↦ (p (j : ℕ)).coeff (i : ℕ)

/-- Entry formula for the polynomial coefficient matrix. -/
@[simp]
theorem polynomialCoefficientMatrix_apply {R : Type*} [Semiring R]
    (p : ℕ → R[X]) (n : ℕ) (i j : Fin n) :
    polynomialCoefficientMatrix p n i j =
      (p (j : ℕ)).coeff (i : ℕ) :=
  rfl

/-- The order-`n` Gram matrix of a polynomial family for a scalar moment
pairing. -/
def polynomialMomentGramMatrix {R : Type*} [CommSemiring R]
    (moment : ℕ → R) (p : ℕ → R[X]) (n : ℕ) :
    Matrix (Fin n) (Fin n) R :=
  fun i j ↦ momentPairing moment (p (i : ℕ)) (p (j : ℕ))

/-- Entry formula for the polynomial moment Gram matrix. -/
@[simp]
theorem polynomialMomentGramMatrix_apply {R : Type*} [CommSemiring R]
    (moment : ℕ → R) (p : ℕ → R[X]) (n : ℕ) (i j : Fin n) :
    polynomialMomentGramMatrix moment p n i j =
      momentPairing moment (p (i : ℕ)) (p (j : ℕ)) :=
  rfl

private theorem polynomial_eq_sum_fin_coeff_mul_X_pow
    {R : Type*} [Semiring R] (q : R[X]) (n : ℕ)
    (hdeg : q.natDegree < n) :
    q = ∑ i : Fin n, q.coeff (i : ℕ) • Polynomial.X ^ (i : ℕ) := by
  calc
    q = ∑ i ∈ Finset.range n,
        Polynomial.C (q.coeff i) * Polynomial.X ^ i :=
      q.as_sum_range_C_mul_X_pow' hdeg
    _ = ∑ i : Fin n,
        Polynomial.C (q.coeff (i : ℕ)) * Polynomial.X ^ (i : ℕ) := by
      symm
      exact Fin.sum_univ_eq_sum_range
        (fun i : ℕ ↦ Polynomial.C (q.coeff i) * Polynomial.X ^ i) n
    _ = ∑ i : Fin n, q.coeff (i : ℕ) •
        Polynomial.X ^ (i : ℕ) := by
      simp only [Polynomial.smul_eq_C_mul]

/-- A coherent polynomial family changes the monomial Hankel matrix by
congruence: `G_n = C_nᵀ H_n C_n`. -/
theorem polynomialMomentGramMatrix_eq_transpose_mul_hankel_mul
    {R : Type*} [CommSemiring R] (moment : ℕ → R) (p : ℕ → R[X])
    (n : ℕ) (hdeg : ∀ k : ℕ, (p k).natDegree ≤ k) :
    polynomialMomentGramMatrix moment p n =
      (polynomialCoefficientMatrix p n).transpose *
        (momentHankelMatrix moment n * polynomialCoefficientMatrix p n) := by
  ext i j
  have hi : (p (i : ℕ)).natDegree < n :=
    lt_of_le_of_lt (hdeg (i : ℕ)) i.isLt
  have hj : (p (j : ℕ)).natDegree < n :=
    lt_of_le_of_lt (hdeg (j : ℕ)) j.isLt
  rw [polynomialMomentGramMatrix_apply,
    polynomial_eq_sum_fin_coeff_mul_X_pow (p (i : ℕ)) n hi,
    polynomial_eq_sum_fin_coeff_mul_X_pow (p (j : ℕ)) n hj]
  simp only [map_sum, map_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    momentPairing_X_pow, Matrix.mul_apply, Matrix.transpose_apply,
    polynomialCoefficientMatrix_apply, momentHankelMatrix_apply,
    Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-! ## Determinants -/

/-- Taking determinants in `G_n = C_nᵀ H_n C_n` gives the square of the
coefficient determinant times the Hankel determinant. -/
theorem polynomialMomentGramMatrix_det_eq_coefficient_det_sq_mul
    {R : Type*} [CommRing R] (moment : ℕ → R) (p : ℕ → R[X])
    (n : ℕ) (hdeg : ∀ k : ℕ, (p k).natDegree ≤ k) :
    (polynomialMomentGramMatrix moment p n).det =
      (polynomialCoefficientMatrix p n).det ^ 2 *
        momentHankelDet moment n := by
  rw [polynomialMomentGramMatrix_eq_transpose_mul_hankel_mul
      moment p n hdeg,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  unfold momentHankelDet
  ring

/-- The coefficient matrix of a coherent polynomial family is upper
triangular, so its determinant is the product of its diagonal coefficients. -/
theorem polynomialCoefficientMatrix_det_eq_prod_coeff
    {R : Type*} [CommRing R] (p : ℕ → R[X]) (n : ℕ)
    (hdeg : ∀ k : ℕ, (p k).natDegree ≤ k) :
    (polynomialCoefficientMatrix p n).det =
      ∏ i : Fin n, (p (i : ℕ)).coeff (i : ℕ) := by
  apply Matrix.det_of_upperTriangular
  intro i j hji
  rw [polynomialCoefficientMatrix_apply]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (hdeg (j : ℕ)) hji)

/-- The Gram determinant of a coherent polynomial family is the Hankel
determinant multiplied by the square of the product of its diagonal
coefficients. -/
theorem polynomialMomentGramMatrix_det_eq_prod_coeff_sq_mul
    {R : Type*} [CommRing R] (moment : ℕ → R) (p : ℕ → R[X])
    (n : ℕ) (hdeg : ∀ k : ℕ, (p k).natDegree ≤ k) :
    (polynomialMomentGramMatrix moment p n).det =
      (∏ i : Fin n, (p (i : ℕ)).coeff (i : ℕ)) ^ 2 *
        momentHankelDet moment n := by
  rw [polynomialMomentGramMatrix_det_eq_coefficient_det_sq_mul
      moment p n hdeg,
    polynomialCoefficientMatrix_det_eq_prod_coeff p n hdeg]

private theorem polynomialDiagonalCoefficient_prod_succ
    {K : Type*} [Field K] (p : ℕ → K[X]) (n : ℕ) :
    (∏ i : Fin (n + 1), (p (i : ℕ)).coeff (i : ℕ)) =
      (∏ i : Fin n, (p (i : ℕ)).coeff (i : ℕ)) *
        (p n).coeff n := by
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]

/-- The finite Gram--Stieltjes Jacobi subdiagonal expressed through Gram
determinants in an arbitrary coherent polynomial basis.  The prefactor is
the square of the quotient of two consecutive diagonal coefficients.  No
Hankel nonvanishing assumption is needed: when the middle determinant is
zero, both cross-ratios are zero under field division. -/
theorem gramStieltjesJacobiSubdiagonal_eq_polynomialMomentGramMatrix_det_ratio
    {K : Type*} [Field K] (moment : ℕ → K) (p : ℕ → K[X]) (n : ℕ)
    (hdeg : ∀ k : ℕ, (p k).natDegree ≤ k)
    (hcoeff : ∀ k : ℕ, (p k).coeff k ≠ 0) :
    gramStieltjesJacobiSubdiagonal moment n =
      ((p n).coeff n / (p (n + 1)).coeff (n + 1)) ^ 2 *
        ((polynomialMomentGramMatrix moment p (n + 2)).det *
            (polynomialMomentGramMatrix moment p n).det /
          (polynomialMomentGramMatrix moment p (n + 1)).det ^ 2) := by
  by_cases hdet : momentHankelDet moment (n + 1) = 0
  · rw [gramStieltjesJacobiSubdiagonal_eq_det_ratio,
      polynomialMomentGramMatrix_det_eq_prod_coeff_sq_mul
        moment p (n + 2) hdeg,
      polynomialMomentGramMatrix_det_eq_prod_coeff_sq_mul
        moment p n hdeg,
      polynomialMomentGramMatrix_det_eq_prod_coeff_sq_mul
        moment p (n + 1) hdeg]
    simp [hdet]
  have hprod_ne (k : ℕ) :
      (∏ i : Fin k, (p (i : ℕ)).coeff (i : ℕ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ ↦ hcoeff (i : ℕ)
  have hcoeff_n : (p n).coeff n ≠ 0 := hcoeff n
  have hcoeff_succ : (p (n + 1)).coeff (n + 1) ≠ 0 :=
    hcoeff (n + 1)
  have hprod_n :
      (∏ i : Fin n, (p (i : ℕ)).coeff (i : ℕ)) ≠ 0 :=
    hprod_ne n
  rw [gramStieltjesJacobiSubdiagonal_eq_det_ratio,
    polynomialMomentGramMatrix_det_eq_prod_coeff_sq_mul
      moment p (n + 2) hdeg,
    polynomialMomentGramMatrix_det_eq_prod_coeff_sq_mul
      moment p n hdeg,
    polynomialMomentGramMatrix_det_eq_prod_coeff_sq_mul
      moment p (n + 1) hdeg]
  simp_rw [polynomialDiagonalCoefficient_prod_succ]
  field_simp [hcoeff_n, hcoeff_succ, hprod_n, hdet]

end

end Fabius
