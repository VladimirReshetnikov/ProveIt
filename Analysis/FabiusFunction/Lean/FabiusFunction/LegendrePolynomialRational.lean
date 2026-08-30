import FabiusFunction.LegendrePolynomial
import Mathlib.Data.Nat.Choose.Central

/-!
# Rational Legendre polynomials with executable coefficients

Mathlib's shifted Legendre polynomial has integer coefficients and satisfies
`shiftedLegendre n (x) = P_n(1 - 2x)`.  Substituting `(1 - X) / 2` in its
explicit finite sum therefore gives the ordinary Legendre polynomial `P_n`.

The scalar function `legendrePolynomialCoeffRat` performs the resulting
finite coefficient sum directly in `ℚ` and is executable.  The accompanying
`Polynomial ℚ` wrapper is marked noncomputable because it uses Mathlib's
generic polynomial-algebra operations; a coefficient theorem identifies the
wrapper with the executable scalar function at every index.
-/

set_option autoImplicit false

open Finset Polynomial
open scoped BigOperators

namespace Fabius

/-! ## Rational construction and real bridge -/

/-- The executable coefficient of `X^k` in the rational ordinary Legendre
polynomial `P_n`.  The outer factor is the `r`-th shifted-Legendre
coefficient, while the inner factor is the coefficient of `X^k` in
`((1-X)/2)^r`; `choose r k = 0` automatically removes the terms with
`r < k`. -/
def legendrePolynomialCoeffRat (n k : ℕ) : ℚ :=
  ∑ r ∈ range (n + 1),
    (((-1 : ℚ) ^ r) * (n.choose r : ℚ) *
        ((n + r).choose n : ℚ)) *
      ((2 : ℚ)⁻¹ ^ r * (-1 : ℚ) ^ k * (r.choose k : ℚ))

/-- The rational ordinary Legendre polynomial, obtained from the explicit
shifted-Legendre sum by the affine substitution `x ↦ (1-x)/2`:
`P_n(x) = ∑_{r=0}^n (-1)^r choose(n,r) choose(n+r,n) ((1-x)/2)^r`.
Its coefficients are computed by the executable function
`legendrePolynomialCoeffRat`. -/
noncomputable def legendrePolynomialRat (n : ℕ) : ℚ[X] :=
  ∑ r ∈ range (n + 1),
    C (((-1 : ℚ) ^ r) * (n.choose r : ℚ) *
        ((n + r).choose n : ℚ)) *
      (C ((2 : ℚ)⁻¹) * (1 - X)) ^ r

private theorem legendrePolynomialRat_eq_shiftedLegendre_comp (n : ℕ) :
    legendrePolynomialRat n =
      ((Polynomial.shiftedLegendre n).map
        (Int.castRingHom ℚ)).comp
          (C ((2 : ℚ)⁻¹) * (1 - X)) := by
  rw [legendrePolynomialRat, Polynomial.shiftedLegendre,
    Polynomial.map_sum, Polynomial.sum_comp]
  apply Finset.sum_congr rfl
  intro r _hr
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_X, mul_comp, C_comp, pow_comp, X_comp]
  norm_num

/-- Mapping the rational polynomial wrapper to `ℝ` recovers the
Rodrigues-normalized ordinary Legendre polynomial. -/
theorem legendrePolynomialRat_cast (n : ℕ) :
    (legendrePolynomialRat n).map (Rat.castHom ℝ) =
      legendrePolynomial n := by
  let a : ℝ[X] := C ((2 : ℝ)⁻¹) * (1 - X)
  have hshift :
      (legendrePolynomialRat n).map (Rat.castHom ℝ) =
        ((Polynomial.shiftedLegendre n).map
          (Int.castRingHom ℝ)).comp a := by
    rw [legendrePolynomialRat_eq_shiftedLegendre_comp,
      Polynomial.map_comp]
    have hp :
        ((Polynomial.shiftedLegendre n).map
            (Int.castRingHom ℚ)).map (Rat.castHom ℝ) =
          (Polynomial.shiftedLegendre n).map
            (Int.castRingHom ℝ) := by
      ext k
      simp
    have ha :
        (C ((2 : ℚ)⁻¹) * (1 - X)).map (Rat.castHom ℝ) = a := by
      simp [a]
    rw [hp, ha]
  have htranslate := congrArg (fun p : ℝ[X] ↦ p.comp a)
    (legendrePolynomial_comp_one_sub_two_X n)
  have haffine : (1 - C (2 : ℝ) * X).comp a = X := by
    simp only [a, sub_comp, one_comp, mul_comp, C_comp, X_comp]
    have hC : C (2 : ℝ) * C ((2 : ℝ)⁻¹) = (1 : ℝ[X]) := by
      rw [← C_mul]
      norm_num
    calc
      1 - C (2 : ℝ) * (C ((2 : ℝ)⁻¹) * (1 - X)) =
          1 - (C (2 : ℝ) * C ((2 : ℝ)⁻¹)) * (1 - X) := by
            ring
      _ = X := by rw [hC]; ring
  rw [comp_assoc, haffine, comp_X] at htranslate
  exact hshift.trans htranslate.symm

private theorem coeff_legendreAffinePow (r k : ℕ) :
    ((C ((2 : ℚ)⁻¹) * (1 - X)) ^ r : ℚ[X]).coeff k =
      (2 : ℚ)⁻¹ ^ r * (-1 : ℚ) ^ k * (r.choose k : ℚ) := by
  rw [show C ((2 : ℚ)⁻¹) * (1 - X) =
      C (-((2 : ℚ)⁻¹)) * (X + C (-1)) by
        rw [mul_sub, mul_add, mul_one, ← C_mul, C_neg]
        norm_num
        ring,
    mul_pow, ← C_pow, coeff_C_mul, coeff_X_add_C_pow]
  by_cases hk : k ≤ r
  · have hsign :
        (-1 : ℚ) ^ r * (-1 : ℚ) ^ (r - k) = (-1 : ℚ) ^ k := by
      rw [← pow_add]
      rw [show r + (r - k) = 2 * (r - k) + k by omega,
        pow_add, pow_mul]
      norm_num
    rw [neg_pow]
    calc
      (-1 : ℚ) ^ r * (2 : ℚ)⁻¹ ^ r *
          ((-1 : ℚ) ^ (r - k) * (r.choose k : ℚ)) =
        (2 : ℚ)⁻¹ ^ r *
          ((-1 : ℚ) ^ r * (-1 : ℚ) ^ (r - k)) *
            (r.choose k : ℚ) := by ring
      _ = (2 : ℚ)⁻¹ ^ r * (-1 : ℚ) ^ k *
          (r.choose k : ℚ) := by rw [hsign]
  · have hrk : r < k := Nat.lt_of_not_ge hk
    rw [Nat.choose_eq_zero_of_lt hrk]
    simp

/-- Coefficientwise, the rational polynomial wrapper is exactly the
executable finite coefficient sum. -/
@[simp]
theorem coeff_legendrePolynomialRat (n k : ℕ) :
    (legendrePolynomialRat n).coeff k =
      legendrePolynomialCoeffRat n k := by
  rw [legendrePolynomialRat, legendrePolynomialCoeffRat,
    finsetSum_coeff]
  simp_rw [coeff_C_mul, coeff_legendreAffinePow]

/-! ## Exact degree and leading coefficient -/

/-- The rational Legendre polynomial wrapper has natural degree exactly its
index. -/
@[simp]
theorem natDegree_legendrePolynomialRat (n : ℕ) :
    (legendrePolynomialRat n).natDegree = n := by
  calc
    (legendrePolynomialRat n).natDegree =
        ((legendrePolynomialRat n).map (Rat.castHom ℝ)).natDegree :=
      (Polynomial.natDegree_map_eq_of_injective
        (Rat.cast_injective (α := ℝ)) _).symm
    _ = n := by
      rw [legendrePolynomialRat_cast, natDegree_legendrePolynomial]

/-- The top coefficient of the rational ordinary Legendre polynomial is
`2^(-n) * choose(2n,n)`. -/
theorem coeff_legendrePolynomialRat_self (n : ℕ) :
    (legendrePolynomialRat n).coeff n =
      (2 : ℚ)⁻¹ ^ n * ((2 * n).choose n : ℚ) := by
  apply Rat.cast_injective (α := ℝ)
  change Rat.castHom ℝ ((legendrePolynomialRat n).coeff n) =
    Rat.castHom ℝ
      ((2 : ℚ)⁻¹ ^ n * ((2 * n).choose n : ℚ))
  have hcast :
      Rat.castHom ℝ ((legendrePolynomialRat n).coeff n) =
        (legendrePolynomial n).coeff n := by
    simpa only [Polynomial.coeff_map] using congrArg
      (fun p : ℝ[X] ↦ p.coeff n) (legendrePolynomialRat_cast n)
  rw [hcast, coeff_legendrePolynomial_self]
  norm_num

/-- The top coefficient of every rational ordinary Legendre polynomial is
nonzero. -/
theorem coeff_legendrePolynomialRat_self_ne_zero (n : ℕ) :
    (legendrePolynomialRat n).coeff n ≠ 0 := by
  rw [coeff_legendrePolynomialRat_self]
  apply mul_ne_zero
  · positivity
  · exact_mod_cast Nat.ne_of_gt
      (Nat.choose_pos (show n ≤ 2 * n by omega))

/-- The quotient of consecutive rational Legendre top coefficients is
`(n+1)/(2n+1)`. -/
theorem coeff_legendrePolynomialRat_self_div_succ (n : ℕ) :
    (legendrePolynomialRat n).coeff n /
        (legendrePolynomialRat (n + 1)).coeff (n + 1) =
      (((n + 1 : ℕ) : ℚ) / ((2 * n + 1 : ℕ) : ℚ)) := by
  have hrecNat :
      (n + 1) * (2 * (n + 1)).choose (n + 1) =
        2 * (2 * n + 1) * (2 * n).choose n := by
    simpa only [Nat.centralBinom_eq_two_mul_choose] using
      Nat.succ_mul_centralBinom_succ n
  have hrec :
      ((n + 1 : ℕ) : ℚ) *
          (((2 * (n + 1)).choose (n + 1) : ℕ) : ℚ) =
        2 * ((2 * n + 1 : ℕ) : ℚ) *
          (((2 * n).choose n : ℕ) : ℚ) := by
    exact_mod_cast hrecNat
  have hleadSucc :
      (legendrePolynomialRat (n + 1)).coeff (n + 1) ≠ 0 :=
    coeff_legendrePolynomialRat_self_ne_zero (n + 1)
  have hodd : (((2 * n + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
  apply (div_eq_iff hleadSucc).2
  rw [div_mul_eq_mul_div, eq_div_iff hodd]
  rw [coeff_legendrePolynomialRat_self,
    coeff_legendrePolynomialRat_self, pow_succ]
  linear_combination -((2 : ℚ)⁻¹ ^ (n + 1)) * hrec

end Fabius
