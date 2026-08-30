import FabiusFunction.LegendrePolynomial
import FabiusFunction.PolynomialMomentGramDeterminant
import FabiusFunction.RvachevRationalJacobi
import Mathlib.Data.Nat.Choose.Central

/-!
# Legendre Gram determinants for the Rvachev up law

The ordinary Legendre polynomials form a triangular change of basis from
monomials.  This module specializes the generic polynomial moment-Gram
determinant identity to the moment sequence of Rvachev's `up` measure.

If `D_n` is the determinant of the Gram matrix of
`P_0, ..., P_(n-1)` in the up-law pairing, then

`D_n = (prod_{j<n} L_j^2) * Delta_n`,

where `L_j = 2^(-j) * choose (2j) j` is the leading coefficient of `P_j`
and `Delta_n` is the monomial Hankel determinant.  Transporting the Hankel
cross-ratio through this change of basis gives the zero-based Jacobi formula

`beta_(n+1) = ((n+1)/(2n+1))^2 * D_(n+2) * D_n / D_(n+1)^2`.

Everything proved here is finite linear algebra.  In particular, this module
does not claim the finite Gaunt/Wigner-symbol expansion of the matrix entries,
their rationality by that route, any Christoffel reconstruction, or an
infinite Jacobi-product formula.
-/

set_option autoImplicit false

open Finset Polynomial
open scoped BigOperators

namespace Fabius

noncomputable section

/-! ## The up-law Gram matrix in the Legendre basis -/

/-- The order-`n` Gram matrix of the first `n` ordinary Legendre polynomials
for the moment pairing of Rvachev's up law. -/
def upLegendreGramMatrix (F : BoundedFabius) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  polynomialMomentGramMatrix (upMoment F) legendrePolynomial n

/-- An entry of the up-law Legendre Gram matrix is the integral of the two
Legendre polynomials against the canonical Rvachev measure. -/
@[simp]
theorem upLegendreGramMatrix_apply_eq_integral
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (i j : Fin n) :
    upLegendreGramMatrix F n i j =
      ∫ x, (legendrePolynomial (i : ℕ)).eval x *
        (legendrePolynomial (j : ℕ)).eval x ∂(rvachevMeasure F) := by
  rw [upLegendreGramMatrix, polynomialMomentGramMatrix_apply,
    momentPairing_upMoment_eq_integral F hF]

/-- The determinant of the order-`n` up-law Legendre Gram matrix. -/
def upLegendreGramDet (F : BoundedFabius) (n : ℕ) : ℝ :=
  (upLegendreGramMatrix F n).det

/-- The Legendre Gram determinant is the monomial Hankel determinant times
the product of the squared Legendre leading coefficients. -/
theorem upLegendreGramDet_eq_prod_leadingCoeff_sq_mul_hankelDet
    (F : BoundedFabius) (n : ℕ) :
    upLegendreGramDet F n =
      (∏ i : Fin n,
          ((2 : ℝ)⁻¹ ^ (i : ℕ) *
            (2 * (i : ℕ)).choose (i : ℕ)) ^ 2) *
        hankelDet F n := by
  unfold upLegendreGramDet upLegendreGramMatrix
  rw [polynomialMomentGramMatrix_det_eq_prod_coeff_sq_mul
    (upMoment F) legendrePolynomial n
    (fun k ↦ (natDegree_legendrePolynomial k).le)]
  rw [← Finset.prod_pow]
  simp_rw [coeff_legendrePolynomial_self]
  rw [← hankelDet_eq_momentHankelDet]

/-- The empty up-law Legendre Gram determinant is one. -/
@[simp]
theorem upLegendreGramDet_zero (F : BoundedFabius) :
    upLegendreGramDet F 0 = 1 := by
  rw [upLegendreGramDet_eq_prod_leadingCoeff_sq_mul_hankelDet]
  simp

/-- Every up-law Legendre Gram determinant is strictly positive. -/
theorem upLegendreGramDet_pos
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    0 < upLegendreGramDet F n := by
  rw [upLegendreGramDet_eq_prod_leadingCoeff_sq_mul_hankelDet]
  apply mul_pos
  · apply Finset.prod_pos
    intro i _hi
    apply sq_pos_of_pos
    apply mul_pos
    · positivity
    · exact_mod_cast Nat.choose_pos (show (i : ℕ) ≤ 2 * (i : ℕ) by omega)
  · exact hankelDet_pos F hF n

/-! ## Transport of the Jacobi subdiagonal -/

private theorem coeff_legendrePolynomial_self_ne_zero (n : ℕ) :
    (legendrePolynomial n).coeff n ≠ 0 := by
  rw [coeff_legendrePolynomial_self]
  apply mul_ne_zero
  · positivity
  · exact_mod_cast Nat.ne_of_gt
      (Nat.choose_pos (show n ≤ 2 * n by omega))

/-- The quotient of two consecutive Legendre leading coefficients is
`(n+1)/(2n+1)`. -/
theorem coeff_legendrePolynomial_self_div_succ (n : ℕ) :
    (legendrePolynomial n).coeff n /
        (legendrePolynomial (n + 1)).coeff (n + 1) =
      (((n + 1 : ℕ) : ℝ) / ((2 * n + 1 : ℕ) : ℝ)) := by
  have hrecNat :
      (n + 1) * (2 * (n + 1)).choose (n + 1) =
        2 * (2 * n + 1) * (2 * n).choose n := by
    simpa only [Nat.centralBinom_eq_two_mul_choose] using
      Nat.succ_mul_centralBinom_succ n
  have hrec :
      ((n + 1 : ℕ) : ℝ) *
          (((2 * (n + 1)).choose (n + 1) : ℕ) : ℝ) =
        2 * ((2 * n + 1 : ℕ) : ℝ) *
          (((2 * n).choose n : ℕ) : ℝ) := by
    exact_mod_cast hrecNat
  have hleadSucc : (legendrePolynomial (n + 1)).coeff (n + 1) ≠ 0 :=
    coeff_legendrePolynomial_self_ne_zero (n + 1)
  have hodd : (((2 * n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  apply (div_eq_iff hleadSucc).2
  rw [div_mul_eq_mul_div, eq_div_iff hodd]
  rw [coeff_legendrePolynomial_self, coeff_legendrePolynomial_self,
    pow_succ]
  linear_combination -((2 : ℝ)⁻¹ ^ (n + 1)) * hrec

/-- The zero-based up-law Jacobi subdiagonal, conventionally
`beta_(n+1)`, is the indicated cross-ratio of Legendre Gram determinants. -/
theorem gramStieltjesJacobiSubdiagonal_upMoment_eq_upLegendreGramDet_ratio
    (F : BoundedFabius) (n : ℕ) :
    gramStieltjesJacobiSubdiagonal (upMoment F) n =
      ((((n + 1 : ℕ) : ℝ) / ((2 * n + 1 : ℕ) : ℝ)) ^ 2) *
        (upLegendreGramDet F (n + 2) * upLegendreGramDet F n /
          upLegendreGramDet F (n + 1) ^ 2) := by
  have h :=
    gramStieltjesJacobiSubdiagonal_eq_polynomialMomentGramMatrix_det_ratio
      (upMoment F) legendrePolynomial n
      (fun k ↦ (natDegree_legendrePolynomial k).le)
      coeff_legendrePolynomial_self_ne_zero
  simpa only [upLegendreGramDet, upLegendreGramMatrix,
    coeff_legendrePolynomial_self_div_succ] using h

/-- Casting the exact rational Rvachev Jacobi subdiagonal to the reals gives
the same Legendre Gram-determinant formula.  The index `n` on the left is
zero-based, so this is the conventional coefficient `beta_(n+1)`. -/
theorem rvachevJacobiSubdiagonalRat_cast_eq_upLegendreGramDet_ratio
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    (rvachevJacobiSubdiagonalRat n : ℝ) =
      ((((n + 1 : ℕ) : ℝ) / ((2 * n + 1 : ℕ) : ℝ)) ^ 2) *
        (upLegendreGramDet F (n + 2) * upLegendreGramDet F n /
          upLegendreGramDet F (n + 1) ^ 2) := by
  rw [rvachevJacobiSubdiagonalRat_cast F hF n,
    ← gramStieltjesJacobiSubdiagonal_upMoment_eq F n]
  exact
    gramStieltjesJacobiSubdiagonal_upMoment_eq_upLegendreGramDet_ratio
      F n

end

end Fabius
