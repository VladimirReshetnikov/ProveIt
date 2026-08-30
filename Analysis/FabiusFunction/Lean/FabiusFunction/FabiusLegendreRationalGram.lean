import FabiusFunction.FabiusLegendreHankelDeterminant
import FabiusFunction.LegendrePolynomialRational

/-!
# Executable rational Legendre Gram determinants

The rational Rvachev moments and the executable rational Legendre coefficient
evaluator make every finite entry of the up-law Legendre Gram matrix available
as a bounded double sum over `ℚ`.  This module packages that sum, its finite
matrix, and its determinant, and identifies them with the abstract
moment-pairing objects developed elsewhere.

Coefficientwise casting sends the rational matrix and determinant to
`upLegendreGramMatrix` and `upLegendreGramDet` for every genuine Fabius
representative.  Over `ℚ` itself, the determinant is the rational Hankel
determinant times the product of the squared Legendre leading coefficients.
Consequently the exact rational Gram--Stieltjes norms and zero-based Jacobi
subdiagonals yield Legendre-determinant ratios.

All three definitions below are finite and executable.  The argument does
not use the still-open Gaunt/Wigner-symbol expansion of the entries, and it
makes no claim about Christoffel reconstruction or an infinite Jacobi
product.
-/

set_option autoImplicit false

open Finset Polynomial
open scoped BigOperators

namespace Fabius

/-! ## Executable rational Gram data -/

/-- The rational Rvachev pairing of two ordinary Legendre polynomials,
written as a bounded double sum of their coefficients and the executable raw
moments. -/
def rvachevLegendreGramEntryRat (i j : ℕ) : ℚ :=
  ∑ a ∈ range (i + 1), ∑ b ∈ range (j + 1),
    legendrePolynomialCoeffRat i a *
      legendrePolynomialCoeffRat j b *
        rvachevRawMomentRat (a + b)

/-- The bounded coefficient sum is the rational moment pairing of the two
Legendre polynomials. -/
theorem rvachevLegendreGramEntryRat_eq_momentPairing (i j : ℕ) :
    rvachevLegendreGramEntryRat i j =
      momentPairing rvachevRawMomentRat
        (legendrePolynomialRat i) (legendrePolynomialRat j) := by
  have hi : (legendrePolynomialRat i).natDegree < i + 1 := by simp
  have hj : (legendrePolynomialRat j).natDegree < j + 1 := by simp
  have hiExpansion :=
    (legendrePolynomialRat i).as_sum_range_C_mul_X_pow' hi
  have hjExpansion :=
    (legendrePolynomialRat j).as_sum_range_C_mul_X_pow' hj
  calc
    rvachevLegendreGramEntryRat i j =
        ∑ a ∈ range (i + 1), ∑ b ∈ range (j + 1),
          legendrePolynomialCoeffRat i a *
            legendrePolynomialCoeffRat j b *
              rvachevRawMomentRat (a + b) := rfl
    _ = momentPairing rvachevRawMomentRat
          (∑ a ∈ range (i + 1),
            C ((legendrePolynomialRat i).coeff a) * X ^ a)
          (∑ b ∈ range (j + 1),
            C ((legendrePolynomialRat j).coeff b) * X ^ b) := by
      symm
      simp only [map_sum, LinearMap.sum_apply,
        Polynomial.C_mul_X_pow_eq_monomial, momentPairing_monomial,
        coeff_legendrePolynomialRat]
      conv_lhs => rw [Finset.sum_comm]
    _ = momentPairing rvachevRawMomentRat
          (legendrePolynomialRat i) (legendrePolynomialRat j) := by
      rw [← hiExpansion, ← hjExpansion]

/-- The order-`n` matrix of executable rational Legendre Gram entries. -/
def rvachevLegendreGramMatrixRat (n : ℕ) :
    Matrix (Fin n) (Fin n) ℚ :=
  fun i j ↦ rvachevLegendreGramEntryRat (i : ℕ) (j : ℕ)

/-- Entry formula for the executable rational Legendre Gram matrix. -/
@[simp]
theorem rvachevLegendreGramMatrixRat_apply
    (n : ℕ) (i j : Fin n) :
    rvachevLegendreGramMatrixRat n i j =
      rvachevLegendreGramEntryRat (i : ℕ) (j : ℕ) :=
  rfl

/-- The executable matrix is exactly the abstract polynomial moment Gram
matrix over the rational Rvachev moments. -/
theorem rvachevLegendreGramMatrixRat_eq_polynomialMomentGramMatrix
    (n : ℕ) :
    rvachevLegendreGramMatrixRat n =
      polynomialMomentGramMatrix rvachevRawMomentRat
        legendrePolynomialRat n := by
  ext i j
  rw [rvachevLegendreGramMatrixRat_apply,
    polynomialMomentGramMatrix_apply,
    rvachevLegendreGramEntryRat_eq_momentPairing]

/-- The determinant of the order-`n` executable rational Legendre Gram
matrix. -/
def rvachevLegendreGramDetRat (n : ℕ) : ℚ :=
  (rvachevLegendreGramMatrixRat n).det

/-! ## Real-cast bridges -/

/-- Casting an executable rational entry to `ℝ` gives the up-law moment
pairing of the corresponding real Legendre polynomials. -/
theorem rvachevLegendreGramEntryRat_cast
    (F : BoundedFabius) (hF : IsFabius F) (i j : ℕ) :
    (rvachevLegendreGramEntryRat i j : ℝ) =
      momentPairing (upMoment F)
        (legendrePolynomial i) (legendrePolynomial j) := by
  rw [rvachevLegendreGramEntryRat_eq_momentPairing]
  change Rat.castHom ℝ
      (momentPairing rvachevRawMomentRat
        (legendrePolynomialRat i) (legendrePolynomialRat j)) = _
  calc
    Rat.castHom ℝ
        (momentPairing rvachevRawMomentRat
          (legendrePolynomialRat i) (legendrePolynomialRat j)) =
      momentPairing
        (fun k ↦ Rat.castHom ℝ (rvachevRawMomentRat k))
        ((legendrePolynomialRat i).map (Rat.castHom ℝ))
        ((legendrePolynomialRat j).map (Rat.castHom ℝ)) :=
      (momentPairing_map (Rat.castHom ℝ) rvachevRawMomentRat
        (legendrePolynomialRat i) (legendrePolynomialRat j)).symm
    _ = momentPairing (upMoment F)
        (legendrePolynomial i) (legendrePolynomial j) := by
      rw [legendrePolynomialRat_cast, legendrePolynomialRat_cast]
      apply congrArg
        (fun moment : ℕ → ℝ ↦ momentPairing moment
          (legendrePolynomial i) (legendrePolynomial j))
      funext k
      exact (upMoment_eq_rvachevRawMomentRat_cast F hF k).symm

/-- Mapping every rational matrix entry to `ℝ` gives the real up-law
Legendre Gram matrix. -/
theorem rvachevLegendreGramMatrixRat_cast
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    (rvachevLegendreGramMatrixRat n).map (fun q : ℚ ↦ (q : ℝ)) =
      upLegendreGramMatrix F n := by
  ext i j
  rw [Matrix.map_apply, rvachevLegendreGramMatrixRat_apply,
    upLegendreGramMatrix, polynomialMomentGramMatrix_apply]
  exact rvachevLegendreGramEntryRat_cast F hF (i : ℕ) (j : ℕ)

/-- Casting the executable rational determinant to `ℝ` gives the real up-law
Legendre Gram determinant. -/
theorem rvachevLegendreGramDetRat_cast
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    (rvachevLegendreGramDetRat n : ℝ) =
      upLegendreGramDet F n := by
  unfold rvachevLegendreGramDetRat upLegendreGramDet
  rw [Rat.cast_det, rvachevLegendreGramMatrixRat_cast F hF n]

/-! ## Rational determinant identities and positivity -/

private theorem
    rvachevLegendreGramDetRat_eq_coeff_prod_sq_mul_rvachevHankelDetRat
    (n : ℕ) :
    rvachevLegendreGramDetRat n =
      (∏ i : Fin n,
        (legendrePolynomialRat (i : ℕ)).coeff (i : ℕ)) ^ 2 *
        rvachevHankelDetRat n := by
  unfold rvachevLegendreGramDetRat
  rw [rvachevLegendreGramMatrixRat_eq_polynomialMomentGramMatrix]
  simpa only [rvachevHankelDetRat] using
    polynomialMomentGramMatrix_det_eq_prod_coeff_sq_mul
      rvachevRawMomentRat legendrePolynomialRat n
      (fun k ↦ (natDegree_legendrePolynomialRat k).le)

/-- The executable rational Legendre Gram determinant is the rational
Hankel determinant multiplied by the product of the squared Legendre leading
coefficients. -/
theorem
    rvachevLegendreGramDetRat_eq_prod_leadingCoeff_sq_mul_rvachevHankelDetRat
    (n : ℕ) :
    rvachevLegendreGramDetRat n =
      (∏ i : Fin n,
        ((2 : ℚ)⁻¹ ^ (i : ℕ) *
          ((2 * (i : ℕ)).choose (i : ℕ) : ℚ)) ^ 2) *
        rvachevHankelDetRat n := by
  rw [
    rvachevLegendreGramDetRat_eq_coeff_prod_sq_mul_rvachevHankelDetRat,
    ← Finset.prod_pow]
  simp_rw [coeff_legendrePolynomialRat_self]

/-- The empty executable rational Legendre Gram determinant is one. -/
@[simp]
theorem rvachevLegendreGramDetRat_zero :
    rvachevLegendreGramDetRat 0 = 1 := by
  rw [
    rvachevLegendreGramDetRat_eq_prod_leadingCoeff_sq_mul_rvachevHankelDetRat]
  simp [rvachevHankelDetRat]

/-- Every executable rational Legendre Gram determinant is strictly
positive. -/
theorem rvachevLegendreGramDetRat_pos (n : ℕ) :
    0 < rvachevLegendreGramDetRat n := by
  have hreal : (0 : ℝ) < (rvachevLegendreGramDetRat n : ℝ) := by
    rw [rvachevLegendreGramDetRat_cast fabius fabius_spec n]
    exact upLegendreGramDet_pos fabius fabius_spec n
  exact (Rat.cast_pos (K := ℝ)).mp hreal

private theorem legendrePolynomialRatDiagonalCoefficient_prod_succ
    (n : ℕ) :
    (∏ i : Fin (n + 1),
      (legendrePolynomialRat (i : ℕ)).coeff (i : ℕ)) =
      (∏ i : Fin n,
        (legendrePolynomialRat (i : ℕ)).coeff (i : ℕ)) *
        (legendrePolynomialRat n).coeff n := by
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]

/-! ## Norm and Jacobi determinant ratios -/

/-- The exact rational squared norm of the degree-`n` monic orthogonal
polynomial is a quotient of consecutive rational Legendre Gram determinants,
with the squared degree-`n` Legendre leading coefficient removed. -/
theorem rvachevOrthoNormRat_eq_rvachevLegendreGramDetRat_ratio (n : ℕ) :
    rvachevOrthoNormRat n =
      rvachevLegendreGramDetRat (n + 1) /
        (legendrePolynomialCoeffRat n n ^ 2 *
          rvachevLegendreGramDetRat n) := by
  have hprod :
      (∏ i : Fin n,
        (legendrePolynomialRat (i : ℕ)).coeff (i : ℕ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _hi ↦
      coeff_legendrePolynomialRat_self_ne_zero (i : ℕ)
  have hcoeff : (legendrePolynomialRat n).coeff n ≠ 0 :=
    coeff_legendrePolynomialRat_self_ne_zero n
  have hhankel : rvachevHankelDetRat n ≠ 0 :=
    ne_of_gt (rvachevHankelDetRat_pos n)
  rw [rvachevOrthoNormRat, gramStieltjesNorm]
  change rvachevHankelDetRat (n + 1) / rvachevHankelDetRat n = _
  rw [← coeff_legendrePolynomialRat n n]
  rw [
    rvachevLegendreGramDetRat_eq_coeff_prod_sq_mul_rvachevHankelDetRat,
    rvachevLegendreGramDetRat_eq_coeff_prod_sq_mul_rvachevHankelDetRat,
    legendrePolynomialRatDiagonalCoefficient_prod_succ]
  field_simp [hprod, hcoeff, hhankel]

/-- The zero-based rational Jacobi subdiagonal, conventionally
`beta_(n+1)`, is the indicated cross-ratio of executable rational Legendre
Gram determinants. -/
theorem
    rvachevJacobiSubdiagonalRat_eq_rvachevLegendreGramDetRat_ratio
    (n : ℕ) :
    rvachevJacobiSubdiagonalRat n =
      ((((n + 1 : ℕ) : ℚ) / ((2 * n + 1 : ℕ) : ℚ)) ^ 2) *
        (rvachevLegendreGramDetRat (n + 2) *
            rvachevLegendreGramDetRat n /
          rvachevLegendreGramDetRat (n + 1) ^ 2) := by
  have h :=
    gramStieltjesJacobiSubdiagonal_eq_polynomialMomentGramMatrix_det_ratio
      rvachevRawMomentRat legendrePolynomialRat n
      (fun k ↦ (natDegree_legendrePolynomialRat k).le)
      coeff_legendrePolynomialRat_self_ne_zero
  simp_rw [←
    rvachevLegendreGramMatrixRat_eq_polynomialMomentGramMatrix] at h
  simpa only [rvachevJacobiSubdiagonalRat,
    rvachevLegendreGramDetRat,
    coeff_legendrePolynomialRat_self_div_succ] using h

end Fabius
