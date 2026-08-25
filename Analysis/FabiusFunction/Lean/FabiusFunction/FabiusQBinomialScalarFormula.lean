import FabiusFunction.FabiusQBinomialTaylor

/-!
# Scalar-valued centered q-binomial formulas

The centered inverse-dyadic q-binomial numerator is already known to be a
constant polynomial in its common translation.  This module restores the
normalizing prefactor at the same scalar level and exposes the resulting exact
Fabius identity for arbitrary real and complex translations.
It also records the constant-polynomial theorem coefficientwise: the centered
numerator is the degree-zero coefficient and every positive translation
coefficient vanishes exactly.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

noncomputable section

/-- All translation coefficients of the centered numerator are explicit:
the constant coefficient is the centered numerator itself, and every positive
coefficient cancels. -/
theorem qBinomialThueMorseTranslatedNumeratorPolynomial_coeff
    (n j : ℕ) :
    (qBinomialThueMorseTranslatedNumeratorPolynomial n).coeff j =
      if j = 0 then qBinomialThueMorseNumerator n else 0 := by
  rw [qBinomialThueMorseTranslatedNumeratorPolynomial_eq_const]
  by_cases hj : j = 0
  · subst j
    rw [Polynomial.coeff_C_zero, if_pos rfl]
  · rw [Polynomial.coeff_C_of_ne_zero hj, if_neg hj]

/-- The complete centered translated formula evaluated in a field over `ℚ`. -/
def qBinomialThueMorseTranslatedFormulaIn
    {K : Type*} [Field K] [Algebra ℚ K] (q : K) (n : ℕ) : K :=
  algebraMap ℚ K
      (1 / ((2 : ℚ) ^ (n ^ 2) * qPochhammer (1 / 2) (1 / 2) n)) *
    qBinomialThueMorseTranslatedNumeratorIn q n

/-- The scalar formula is independent of its translation. -/
theorem qBinomialThueMorseTranslatedFormulaIn_eq_centered
    {K : Type*} [Field K] [Algebra ℚ K] (q : K) (n : ℕ) :
    qBinomialThueMorseTranslatedFormulaIn q n =
      algebraMap ℚ K (qBinomialThueMorseFormula n) := by
  rw [qBinomialThueMorseTranslatedFormulaIn,
    qBinomialThueMorseTranslatedNumeratorIn_eq_centered,
    qBinomialThueMorseFormula, map_mul]

/-- Scalar formulas at any two translations agree. -/
theorem qBinomialThueMorseTranslatedFormulaIn_independent
    {K : Type*} [Field K] [Algebra ℚ K] (q₁ q₂ : K) (n : ℕ) :
    qBinomialThueMorseTranslatedFormulaIn q₁ n =
      qBinomialThueMorseTranslatedFormulaIn q₂ n := by
  rw [qBinomialThueMorseTranslatedFormulaIn_eq_centered,
    qBinomialThueMorseTranslatedFormulaIn_eq_centered]

/-- Compatibility with the original rational translated formula. -/
theorem qBinomialThueMorseTranslatedFormulaIn_ratCast
    {K : Type*} [Field K] [Algebra ℚ K] (q : ℚ) (n : ℕ) :
    qBinomialThueMorseTranslatedFormulaIn (algebraMap ℚ K q) n =
      algebraMap ℚ K (qBinomialThueMorseTranslatedFormula q n) := by
  rw [qBinomialThueMorseTranslatedFormulaIn_eq_centered,
    qBinomialThueMorseTranslatedFormula_eq_centered]

/-- Literal Wolfram-style finite-sum expansion over a scalar field. -/
theorem qBinomialThueMorseTranslatedFormulaIn_eq_wolfram_sum
    {K : Type*} [Field K] [Algebra ℚ K] (q : K) (n : ℕ) :
    qBinomialThueMorseTranslatedFormulaIn q n =
      algebraMap ℚ K
          (1 / ((2 : ℚ) ^ (n ^ 2) *
            qPochhammer (1 / 2) (1 / 2) n)) *
        ∑ k ∈ Finset.range (n + 1),
          algebraMap ℚ K
            (qBinomial n k (1 / 2) /
              ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ))) *
            ∑ r ∈ Finset.range (2 ^ k),
              (-1 : K) ^ thueMorseBit r *
                ((r : K) - (2 : K) ^ k + q) ^ (n + k) := by
  rw [qBinomialThueMorseTranslatedFormulaIn,
    qBinomialThueMorseTranslatedNumeratorIn_eq_wolfram_sum]

/-- Exact inverse-dyadic Fabius identity over every scalar field over `ℚ`. -/
theorem qBinomialThueMorseTranslatedFormulaIn_eq_fabiusAtInverseTwoPow
    {K : Type*} [Field K] [Algebra ℚ K] (q : K) (n : ℕ) :
    qBinomialThueMorseTranslatedFormulaIn q n =
      algebraMap ℚ K (fabiusAtInverseTwoPow n) := by
  rw [qBinomialThueMorseTranslatedFormulaIn_eq_centered,
    fabiusAtInverseTwoPow_eq_qBinomialThueMorseFormula]

/-- Fully literal generic scalar inverse-dyadic identity. -/
theorem fabiusAtInverseTwoPow_cast_eq_qBinomialThueMorse_translated_sum
    {K : Type*} [Field K] [Algebra ℚ K] (q : K) (n : ℕ) :
    algebraMap ℚ K (fabiusAtInverseTwoPow n) =
      algebraMap ℚ K
          (1 / ((2 : ℚ) ^ (n ^ 2) *
            qPochhammer (1 / 2) (1 / 2) n)) *
        ∑ k ∈ Finset.range (n + 1),
          algebraMap ℚ K
            (qBinomial n k (1 / 2) /
              ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ))) *
            ∑ r ∈ Finset.range (2 ^ k),
              (-1 : K) ^ thueMorseBit r *
                ((r : K) - (2 : K) ^ k + q) ^ (n + k) := by
  rw [← qBinomialThueMorseTranslatedFormulaIn_eq_fabiusAtInverseTwoPow q n,
    qBinomialThueMorseTranslatedFormulaIn_eq_wolfram_sum]

/-- The centered formula at degree zero is one for every scalar translation. -/
@[simp] theorem qBinomialThueMorseTranslatedFormulaIn_zero
    {K : Type*} [Field K] [Algebra ℚ K] (q : K) :
    qBinomialThueMorseTranslatedFormulaIn q 0 = 1 := by
  rw [qBinomialThueMorseTranslatedFormulaIn_eq_centered,
    ← qBinomialThueMorseRawTranslatedFormula_eq_centered 0 0,
    qBinomialThueMorseRawTranslatedFormula_zero, map_one]

/-- `RCLike` wrapper for every bounded function satisfying the Fabius
characterization.  This simultaneously covers real and complex shifts. -/
theorem fabiusFunction_inverse_two_pow_eq_qBinomialThueMorseTranslatedFormulaIn
    {K : Type*} [RCLike K]
    (F : BoundedFabius) (hF : IsFabius F) (q : K) (n : ℕ) :
    (fabiusReal F (((2 : ℝ) ^ n)⁻¹) : K) =
      qBinomialThueMorseTranslatedFormulaIn q n := by
  rw [qBinomialThueMorseTranslatedFormulaIn_eq_centered]
  have h := congrArg (fun y : ℝ => (y : K))
    (fabiusFunction_inverse_two_pow_eq_qBinomialThueMorseFormula F hF n)
  push_cast at h
  exact h

/-- Canonical real-shift theorem. -/
theorem fabius_inverse_two_pow_eq_qBinomialThueMorseTranslatedFormulaIn_real
    (q : ℝ) (n : ℕ) :
    fabiusReal fabius (((2 : ℝ) ^ n)⁻¹) =
      qBinomialThueMorseTranslatedFormulaIn q n :=
  fabiusFunction_inverse_two_pow_eq_qBinomialThueMorseTranslatedFormulaIn
    fabius fabius_spec q n

/-- Canonical complex-shift theorem. -/
theorem fabius_inverse_two_pow_eq_qBinomialThueMorseTranslatedFormulaIn_complex
    (q : ℂ) (n : ℕ) :
    (fabiusReal fabius (((2 : ℝ) ^ n)⁻¹) : ℂ) =
      qBinomialThueMorseTranslatedFormulaIn q n :=
  fabiusFunction_inverse_two_pow_eq_qBinomialThueMorseTranslatedFormulaIn
    fabius fabius_spec q n

/-- Explicit Gaussian-rational specialization. -/
theorem fabius_inverse_two_pow_eq_qBinomialThueMorseTranslatedFormulaIn_gaussianRat
    (a b : ℚ) (n : ℕ) :
    (fabiusReal fabius (((2 : ℝ) ^ n)⁻¹) : ℂ) =
      qBinomialThueMorseTranslatedFormulaIn
        ((a : ℂ) + (b : ℂ) * Complex.I) n :=
  fabius_inverse_two_pow_eq_qBinomialThueMorseTranslatedFormulaIn_complex
    ((a : ℂ) + (b : ℂ) * Complex.I) n

/-- Fully displayed canonical real-translation identity. -/
theorem fabius_inverse_two_pow_eq_qBinomialThueMorse_translated_sum_real
    (q : ℝ) (n : ℕ) :
    fabiusReal fabius (((2 : ℝ) ^ n)⁻¹) =
      ((1 / ((2 : ℚ) ^ (n ^ 2) *
          qPochhammer (1 / 2) (1 / 2) n) : ℚ) : ℝ) *
        ∑ k ∈ Finset.range (n + 1),
          (qBinomial n k (1 / 2) /
              ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ)) : ℚ) *
            ∑ r ∈ Finset.range (2 ^ k),
              (-1 : ℝ) ^ thueMorseBit r *
                ((r : ℝ) - (2 : ℝ) ^ k + q) ^ (n + k) := by
  calc
    fabiusReal fabius (((2 : ℝ) ^ n)⁻¹) =
        qBinomialThueMorseTranslatedFormulaIn q n :=
      fabius_inverse_two_pow_eq_qBinomialThueMorseTranslatedFormulaIn_real q n
    _ = _ := by
      rw [qBinomialThueMorseTranslatedFormulaIn_eq_wolfram_sum
        (K := ℝ) q n]
      norm_num

/-- Fully displayed canonical complex-translation identity. -/
theorem fabius_inverse_two_pow_eq_qBinomialThueMorse_translated_sum_complex
    (q : ℂ) (n : ℕ) :
    (fabiusReal fabius (((2 : ℝ) ^ n)⁻¹) : ℂ) =
      ((1 / ((2 : ℚ) ^ (n ^ 2) *
          qPochhammer (1 / 2) (1 / 2) n) : ℚ) : ℂ) *
        ∑ k ∈ Finset.range (n + 1),
          (qBinomial n k (1 / 2) /
              ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ)) : ℚ) *
            ∑ r ∈ Finset.range (2 ^ k),
              (-1 : ℂ) ^ thueMorseBit r *
                ((r : ℂ) - (2 : ℂ) ^ k + q) ^ (n + k) := by
  calc
    (fabiusReal fabius (((2 : ℝ) ^ n)⁻¹) : ℂ) =
        qBinomialThueMorseTranslatedFormulaIn q n :=
      fabius_inverse_two_pow_eq_qBinomialThueMorseTranslatedFormulaIn_complex q n
    _ = _ := by
      rw [qBinomialThueMorseTranslatedFormulaIn_eq_wolfram_sum
        (K := ℂ) q n]
      norm_num

end

end Fabius
