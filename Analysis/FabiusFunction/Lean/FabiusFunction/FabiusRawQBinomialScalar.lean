import FabiusFunction.FabiusQBinomialTaylor

/-!
# Scalar-valued raw q-binomial formulas for inverse dyadic Fabius values

`FabiusRawQBinomialFormula` proves the raw-coordinate identity with inner
power `(r + q)^(n+k)` for rational `q`.  Here the finite numerator is first
viewed as a polynomial over `ℚ`.  Its rational identity makes that polynomial
constant, so it can be evaluated at an arbitrary element of any
commutative ring carrying an `ℚ`-algebra structure.  In particular,
the formula holds for every real or complex translation, not merely for
rational or Gaussian-rational ones.  Only the literal `1 / algebraMap`
display of the `(-2)^(n^2)` denominator needs a field.

The generic algebraic theorem is accompanied by one `RCLike`-valued
Fabius-function wrapper, with real and complex compatibility forms and fully
expanded finite-sum statements.
The constant-polynomial proof is also exposed coefficientwise, and rational
translations commute exactly with scalar evaluation already at numerator
level.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

noncomputable section

/-- The raw Thue--Morse power sum as a polynomial in its translation. -/
def thueMorseRawTranslatedPowerSumPolynomial (k d : ℕ) : Polynomial ℚ :=
  ∑ r ∈ Finset.range (2 ^ k),
    Polynomial.C (thueMorseSign r : ℚ) *
      (Polynomial.C (r : ℚ) + Polynomial.X) ^ d

/-- The complete raw-coordinate q-binomial numerator as a polynomial in the
common translation. -/
def qBinomialThueMorseRawTranslatedNumeratorPolynomial
    (n : ℕ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range (n + 1),
    Polynomial.C
      (qBinomial n k (1 / 2) /
        ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ))) *
      thueMorseRawTranslatedPowerSumPolynomial k (n + k)

/-- Rational evaluation of the raw power-sum polynomial recovers the original
raw translated Thue--Morse power sum. -/
@[simp] theorem thueMorseRawTranslatedPowerSumPolynomial_eval
    (q : ℚ) (k d : ℕ) :
    (thueMorseRawTranslatedPowerSumPolynomial k d).eval q =
      thueMorseRawTranslatedPowerSum q k d := by
  rw [thueMorseRawTranslatedPowerSumPolynomial,
    thueMorseRawTranslatedPowerSum]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X]

/-- Rational evaluation of the complete raw numerator polynomial recovers the
original rational raw numerator. -/
@[simp] theorem qBinomialThueMorseRawTranslatedNumeratorPolynomial_eval
    (q : ℚ) (n : ℕ) :
    (qBinomialThueMorseRawTranslatedNumeratorPolynomial n).eval q =
      qBinomialThueMorseRawTranslatedNumerator q n := by
  rw [qBinomialThueMorseRawTranslatedNumeratorPolynomial,
    qBinomialThueMorseRawTranslatedNumerator]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, thueMorseRawTranslatedPowerSumPolynomial_eval]

/-- The raw numerator polynomial is constant.  The factor `(-1)^n` is the
dyadic-reflection sign relating raw and centered coordinates. -/
theorem qBinomialThueMorseRawTranslatedNumeratorPolynomial_eq_const
    (n : ℕ) :
    qBinomialThueMorseRawTranslatedNumeratorPolynomial n =
      Polynomial.C
        ((-1 : ℚ) ^ n * qBinomialThueMorseNumerator n) := by
  apply Polynomial.funext
  intro q
  rw [qBinomialThueMorseRawTranslatedNumeratorPolynomial_eval,
    Polynomial.eval_C,
    qBinomialThueMorseRawTranslatedNumerator_eq_neg_one_pow_mul_centered]

/-- Every positive translation coefficient of the raw numerator cancels.
The all-index form also retains the exact signed centered numerator as the
constant coefficient. -/
theorem qBinomialThueMorseRawTranslatedNumeratorPolynomial_coeff
    (n j : ℕ) :
    (qBinomialThueMorseRawTranslatedNumeratorPolynomial n).coeff j =
      if j = 0 then
        (-1 : ℚ) ^ n * qBinomialThueMorseNumerator n
      else 0 := by
  rw [qBinomialThueMorseRawTranslatedNumeratorPolynomial_eq_const]
  by_cases hj : j = 0
  · subst j
    rw [Polynomial.coeff_C_zero, if_pos rfl]
  · rw [Polynomial.coeff_C_of_ne_zero hj, if_neg hj]

/-- Evaluation of the raw numerator at a scalar in any commutative ring
over `ℚ`. -/
def qBinomialThueMorseRawTranslatedNumeratorIn
    {K : Type*} [CommRing K] [Algebra ℚ K] (q : K) (n : ℕ) : K :=
  Polynomial.eval₂ (algebraMap ℚ K) q
    (qBinomialThueMorseRawTranslatedNumeratorPolynomial n)

/-- Scalar-valued raw numerators are independent of their translation. -/
theorem qBinomialThueMorseRawTranslatedNumeratorIn_eq_centered
    {K : Type*} [CommRing K] [Algebra ℚ K] (q : K) (n : ℕ) :
    qBinomialThueMorseRawTranslatedNumeratorIn q n =
      algebraMap ℚ K
        ((-1 : ℚ) ^ n * qBinomialThueMorseNumerator n) := by
  rw [qBinomialThueMorseRawTranslatedNumeratorIn,
    qBinomialThueMorseRawTranslatedNumeratorPolynomial_eq_const,
    Polynomial.eval₂_C]

/-- Scalar evaluation at a rational translation is the scalar embedding of
the original rational raw numerator. -/
theorem qBinomialThueMorseRawTranslatedNumeratorIn_ratCast
    {K : Type*} [CommRing K] [Algebra ℚ K] (q : ℚ) (n : ℕ) :
    qBinomialThueMorseRawTranslatedNumeratorIn
        (algebraMap ℚ K q) n =
      algebraMap ℚ K
        (qBinomialThueMorseRawTranslatedNumerator q n) := by
  rw [qBinomialThueMorseRawTranslatedNumeratorIn_eq_centered,
    qBinomialThueMorseRawTranslatedNumerator_eq_neg_one_pow_mul_centered]

/-- Literal expansion of the scalar-valued raw numerator. -/
theorem qBinomialThueMorseRawTranslatedNumeratorIn_eq_wolfram_sum
    {K : Type*} [CommRing K] [Algebra ℚ K] (q : K) (n : ℕ) :
    qBinomialThueMorseRawTranslatedNumeratorIn q n =
      ∑ k ∈ Finset.range (n + 1),
        algebraMap ℚ K
          (qBinomial n k (1 / 2) /
            ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ))) *
          ∑ r ∈ Finset.range (2 ^ k),
            (-1 : K) ^ thueMorseBit r *
              ((r : K) + q) ^ (n + k) := by
  rw [qBinomialThueMorseRawTranslatedNumeratorIn,
    qBinomialThueMorseRawTranslatedNumeratorPolynomial]
  simp only [thueMorseRawTranslatedPowerSumPolynomial,
    Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_pow, Polynomial.eval₂_add, Polynomial.eval₂_X]
  apply Finset.sum_congr rfl
  intro k _hk
  congr 1
  apply Finset.sum_congr rfl
  intro r _hr
  rw [← neg_one_pow_thueMorseBit]
  simp only [map_pow, map_neg, map_one, map_natCast]

/-- The raw-coordinate expression with denominator `(-2)^(n^2)`, evaluated
in an arbitrary commutative ring over `ℚ`.  The reciprocal of the
rational prefactor is taken in `ℚ` before the scalar embedding, so no
division in the target is needed; over a field this agrees with the
literal `1 / algebraMap ℚ K (…)` display, see
`fabiusAtInverseTwoPow_cast_eq_qBinomialThueMorse_rawTranslated_sum`. -/
def qBinomialThueMorseRawTranslatedFormulaIn
    {K : Type*} [CommRing K] [Algebra ℚ K] (q : K) (n : ℕ) : K :=
  algebraMap ℚ K
      (1 / ((-2 : ℚ) ^ (n ^ 2) * qPochhammer (1 / 2) (1 / 2) n)) *
    qBinomialThueMorseRawTranslatedNumeratorIn q n

/-- The scalar raw formula is the cast of the centered rational formula. -/
theorem qBinomialThueMorseRawTranslatedFormulaIn_eq_centered
    {K : Type*} [CommRing K] [Algebra ℚ K] (q : K) (n : ℕ) :
    qBinomialThueMorseRawTranslatedFormulaIn q n =
      algebraMap ℚ K (qBinomialThueMorseFormula n) := by
  rw [qBinomialThueMorseRawTranslatedFormulaIn,
    qBinomialThueMorseRawTranslatedNumeratorIn_eq_centered, ← map_mul]
  refine congrArg (algebraMap ℚ K) ?_
  rw [← qBinomialThueMorseRawTranslatedFormula_eq_centered 0 n,
    qBinomialThueMorseRawTranslatedFormula,
    qBinomialThueMorseRawTranslatedNumerator_eq_neg_one_pow_mul_centered]

/-- Compatibility with the original rational-valued raw formula. -/
theorem qBinomialThueMorseRawTranslatedFormulaIn_ratCast
    {K : Type*} [CommRing K] [Algebra ℚ K] (q : ℚ) (n : ℕ) :
    qBinomialThueMorseRawTranslatedFormulaIn (algebraMap ℚ K q) n =
      algebraMap ℚ K (qBinomialThueMorseRawTranslatedFormula q n) := by
  rw [qBinomialThueMorseRawTranslatedFormulaIn_eq_centered,
    qBinomialThueMorseRawTranslatedFormula_eq_centered]

/-- At degree zero the scalar formula is one for every translation, including
the literal `q = 0` case containing `0^0`. -/
@[simp] theorem qBinomialThueMorseRawTranslatedFormulaIn_zero
    {K : Type*} [CommRing K] [Algebra ℚ K] (q : K) :
    qBinomialThueMorseRawTranslatedFormulaIn q 0 = 1 := by
  rw [qBinomialThueMorseRawTranslatedFormulaIn_eq_centered,
    ← qBinomialThueMorseRawTranslatedFormula_eq_centered 0 0,
    qBinomialThueMorseRawTranslatedFormula_zero, map_one]

/-- Generic exact inverse-dyadic Fabius identity for every scalar
translation. -/
theorem qBinomialThueMorseRawTranslatedFormulaIn_eq_fabiusAtInverseTwoPow
    {K : Type*} [CommRing K] [Algebra ℚ K] (q : K) (n : ℕ) :
    qBinomialThueMorseRawTranslatedFormulaIn q n =
      algebraMap ℚ K (fabiusAtInverseTwoPow n) := by
  rw [qBinomialThueMorseRawTranslatedFormulaIn_eq_centered,
    fabiusAtInverseTwoPow_eq_qBinomialThueMorseFormula]

/-- Fully expanded generic scalar identity.  The literal reciprocal
`1 / algebraMap ℚ K (…)` is the one place where the target must be a
field. -/
theorem fabiusAtInverseTwoPow_cast_eq_qBinomialThueMorse_rawTranslated_sum
    {K : Type*} [Field K] [Algebra ℚ K] (q : K) (n : ℕ) :
    algebraMap ℚ K (fabiusAtInverseTwoPow n) =
      (1 / algebraMap ℚ K
          ((-2 : ℚ) ^ (n ^ 2) * qPochhammer (1 / 2) (1 / 2) n)) *
        ∑ k ∈ Finset.range (n + 1),
          algebraMap ℚ K
            (qBinomial n k (1 / 2) /
              ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ))) *
            ∑ r ∈ Finset.range (2 ^ k),
              (-1 : K) ^ thueMorseBit r *
                ((r : K) + q) ^ (n + k) := by
  rw [← qBinomialThueMorseRawTranslatedFormulaIn_eq_fabiusAtInverseTwoPow
    q n, qBinomialThueMorseRawTranslatedFormulaIn,
    qBinomialThueMorseRawTranslatedNumeratorIn_eq_wolfram_sum,
    map_div₀, map_one]

/-- `RCLike` wrapper for every bounded function satisfying the Fabius
characterization and every scalar translation.  This simultaneously covers
real and complex shifts. -/
theorem fabiusFunction_inverse_two_pow_eq_qBinomialThueMorseRawTranslatedFormulaIn
    {K : Type*} [RCLike K]
    (F : BoundedFabius) (hF : IsFabius F) (q : K) (n : ℕ) :
    (fabiusReal F (((2 : ℝ) ^ n)⁻¹) : K) =
      qBinomialThueMorseRawTranslatedFormulaIn q n := by
  rw [qBinomialThueMorseRawTranslatedFormulaIn_eq_centered]
  have h := congrArg (fun y : ℝ => (y : K))
    (fabiusFunction_inverse_two_pow_eq_qBinomialThueMorseFormula F hF n)
  push_cast at h
  exact h

/-- Real-shift form for every bounded Fabius function. -/
theorem fabiusFunction_inverse_two_pow_eq_qBinomialThueMorseRawTranslatedFormula_real
    (F : BoundedFabius) (hF : IsFabius F) (q : ℝ) (n : ℕ) :
    fabiusReal F (((2 : ℝ) ^ n)⁻¹) =
      qBinomialThueMorseRawTranslatedFormulaIn q n := by
  exact fabiusFunction_inverse_two_pow_eq_qBinomialThueMorseRawTranslatedFormulaIn
    F hF q n

/-- Canonical real-shift theorem. -/
theorem fabius_inverse_two_pow_eq_qBinomialThueMorseRawTranslatedFormula_real
    (q : ℝ) (n : ℕ) :
    fabiusReal fabius (((2 : ℝ) ^ n)⁻¹) =
      qBinomialThueMorseRawTranslatedFormulaIn q n :=
  fabiusFunction_inverse_two_pow_eq_qBinomialThueMorseRawTranslatedFormula_real
    fabius fabius_spec q n

/-- Complex-shift form for every bounded Fabius function. -/
theorem fabiusFunction_inverse_two_pow_eq_qBinomialThueMorseRawTranslatedFormula_complex
    (F : BoundedFabius) (hF : IsFabius F) (q : ℂ) (n : ℕ) :
    (fabiusReal F (((2 : ℝ) ^ n)⁻¹) : ℂ) =
      qBinomialThueMorseRawTranslatedFormulaIn q n := by
  exact fabiusFunction_inverse_two_pow_eq_qBinomialThueMorseRawTranslatedFormulaIn
    F hF q n

/-- Canonical complex-shift theorem. -/
theorem fabius_inverse_two_pow_eq_qBinomialThueMorseRawTranslatedFormula_complex
    (q : ℂ) (n : ℕ) :
    (fabiusReal fabius (((2 : ℝ) ^ n)⁻¹) : ℂ) =
      qBinomialThueMorseRawTranslatedFormulaIn q n :=
  fabiusFunction_inverse_two_pow_eq_qBinomialThueMorseRawTranslatedFormula_complex
    fabius fabius_spec q n

/-- Explicit Gaussian-rational specialization of the complex theorem. -/
theorem fabius_inverse_two_pow_eq_qBinomialThueMorseRawTranslatedFormula_gaussianRat
    (a b : ℚ) (n : ℕ) :
    (fabiusReal fabius (((2 : ℝ) ^ n)⁻¹) : ℂ) =
      qBinomialThueMorseRawTranslatedFormulaIn
        ((a : ℂ) + (b : ℂ) * Complex.I) n :=
  fabius_inverse_two_pow_eq_qBinomialThueMorseRawTranslatedFormula_complex
    ((a : ℂ) + (b : ℂ) * Complex.I) n

/-- Canonical fully literal real-translation identity. -/
theorem fabius_inverse_two_pow_eq_qBinomialThueMorse_rawTranslated_sum_real
    (q : ℝ) (n : ℕ) :
    fabiusReal fabius (((2 : ℝ) ^ n)⁻¹) =
      (1 / (((-2 : ℚ) ^ (n ^ 2) *
          qPochhammer (1 / 2) (1 / 2) n : ℚ) : ℝ)) *
        ∑ k ∈ Finset.range (n + 1),
          ((qBinomial n k (1 / 2) /
              ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ)) : ℚ) : ℝ) *
            ∑ r ∈ Finset.range (2 ^ k),
              (-1 : ℝ) ^ thueMorseBit r *
                ((r : ℝ) + q) ^ (n + k) := by
  rw [fabius_inverse_two_pow_eq_qBinomialThueMorseRawTranslatedFormula_real,
    qBinomialThueMorseRawTranslatedFormulaIn,
    qBinomialThueMorseRawTranslatedNumeratorIn_eq_wolfram_sum,
    map_div₀, map_one]
  rfl

/-- Canonical fully literal complex-translation identity. -/
theorem fabius_inverse_two_pow_eq_qBinomialThueMorse_rawTranslated_sum_complex
    (q : ℂ) (n : ℕ) :
    (fabiusReal fabius (((2 : ℝ) ^ n)⁻¹) : ℂ) =
      (1 / (((-2 : ℚ) ^ (n ^ 2) *
          qPochhammer (1 / 2) (1 / 2) n : ℚ) : ℂ)) *
        ∑ k ∈ Finset.range (n + 1),
          ((qBinomial n k (1 / 2) /
              ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ)) : ℚ) : ℂ) *
            ∑ r ∈ Finset.range (2 ^ k),
              (-1 : ℂ) ^ thueMorseBit r *
                ((r : ℂ) + q) ^ (n + k) := by
  rw [fabius_inverse_two_pow_eq_qBinomialThueMorseRawTranslatedFormula_complex,
    qBinomialThueMorseRawTranslatedFormulaIn,
    qBinomialThueMorseRawTranslatedNumeratorIn_eq_wolfram_sum,
    map_div₀, map_one]
  rfl

end

end Fabius
