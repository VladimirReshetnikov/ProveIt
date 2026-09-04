import FabiusFunction.FabiusQBinomialTaylor

/-!
# Scalar-valued arbitrary-dyadic q-binomial Fabius formulas

This module upgrades the common translation in the arbitrary-numerator
dyadic formula from `ℚ` to any commutative ring carrying an
`ℚ`-algebra structure.  The finite expression is first packaged as a
polynomial over `ℚ`; rational translation invariance says that
polynomial is constant, so evaluation works uniformly over `ℝ`, `ℂ`,
and every other `ℚ`-algebra.
The constant-polynomial identity is exposed at every coefficient, retaining
the exact arbitrary-dyadic normalization in degree zero and the cancellation
of every positive translation coefficient.  Scalar evaluation also inherits
the rational formula's representation invariance: the translation and the
chosen numerator/denominator presentation may be changed simultaneously.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

noncomputable section

/-- The arbitrary-numerator inner Thue--Morse sum as a polynomial in its
common translation. -/
def thueMorseDyadicNumeratorTranslatedPowerSumPolynomial
    (m k d : ℕ) : Polynomial ℚ :=
  ∑ r ∈ Finset.range (m * 2 ^ k),
    Polynomial.C (thueMorseSign r : ℚ) *
      (Polynomial.X +
        Polynomial.C ((r : ℚ) - (m : ℚ) * (2 : ℚ) ^ k)) ^ d

/-- Rational evaluation recovers the original translated inner sum. -/
@[simp] theorem thueMorseDyadicNumeratorTranslatedPowerSumPolynomial_eval
    (q : ℚ) (m k d : ℕ) :
    (thueMorseDyadicNumeratorTranslatedPowerSumPolynomial m k d).eval q =
      thueMorseDyadicNumeratorTranslatedPowerSum q m k d := by
  rw [thueMorseDyadicNumeratorTranslatedPowerSumPolynomial,
    thueMorseDyadicNumeratorTranslatedPowerSum]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro r _hr
  congr 1
  ring

/-- Evaluation of one arbitrary-numerator translated inner sum in a
commutative ring over `ℚ`. -/
def thueMorseDyadicNumeratorTranslatedPowerSumIn
    {K : Type*} [CommRing K] [Algebra ℚ K]
    (q : K) (m k d : ℕ) : K :=
  Polynomial.eval₂ (algebraMap ℚ K) q
    (thueMorseDyadicNumeratorTranslatedPowerSumPolynomial m k d)

/-- Literal finite-sum expansion of the scalar-valued inner sum. -/
theorem thueMorseDyadicNumeratorTranslatedPowerSumIn_eq_sum
    {K : Type*} [CommRing K] [Algebra ℚ K]
    (q : K) (m k d : ℕ) :
    thueMorseDyadicNumeratorTranslatedPowerSumIn q m k d =
      ∑ r ∈ Finset.range (m * 2 ^ k),
        algebraMap ℚ K (thueMorseSign r : ℚ) *
          ((r : K) - (m : K) * (2 : K) ^ k + q) ^ d := by
  rw [thueMorseDyadicNumeratorTranslatedPowerSumIn,
    thueMorseDyadicNumeratorTranslatedPowerSumPolynomial]
  simp only [Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_add,
    Polynomial.eval₂_X]
  apply Finset.sum_congr rfl
  intro r _hr
  congr 1
  simp only [map_sub, map_natCast, map_mul, map_pow, map_ofNat]
  ring

/-- Rational casts agree with the original rational inner sum. -/
theorem thueMorseDyadicNumeratorTranslatedPowerSumIn_ratCast
    {K : Type*} [CommRing K] [Algebra ℚ K]
    (q : ℚ) (m k d : ℕ) :
    thueMorseDyadicNumeratorTranslatedPowerSumIn
        (algebraMap ℚ K q) m k d =
      algebraMap ℚ K
        (thueMorseDyadicNumeratorTranslatedPowerSum q m k d) := by
  rw [thueMorseDyadicNumeratorTranslatedPowerSumIn_eq_sum,
    thueMorseDyadicNumeratorTranslatedPowerSum, map_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  simp only [map_mul, map_pow, map_add, map_sub, map_natCast, map_ofNat]

/-- The complete arbitrary-numerator dyadic q-binomial formula as a
polynomial in the common translation. -/
def qBinomialThueMorseDyadicTranslatedFormulaPolynomial
    (m n : ℕ) : Polynomial ℚ :=
  Polynomial.C
      (1 / ((2 : ℚ) ^ (n ^ 2) * qPochhammer (1 / 2) (1 / 2) n)) *
    ∑ k ∈ Finset.range (n + 1),
      Polynomial.C
          (qBinomial n k (1 / 2) /
            ((4 : ℚ) ^ k.choose 2 * ((n + k).factorial : ℚ))) *
        thueMorseDyadicNumeratorTranslatedPowerSumPolynomial
          m k (n + k)

/-- Rational evaluation recovers the original translated dyadic formula. -/
@[simp] theorem qBinomialThueMorseDyadicTranslatedFormulaPolynomial_eval
    (q : ℚ) (m n : ℕ) :
    (qBinomialThueMorseDyadicTranslatedFormulaPolynomial m n).eval q =
      qBinomialThueMorseDyadicTranslatedFormula q m n := by
  rw [qBinomialThueMorseDyadicTranslatedFormulaPolynomial,
    qBinomialThueMorseDyadicTranslatedFormula]
  simp only [Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_finsetSum,
    thueMorseDyadicNumeratorTranslatedPowerSumPolynomial_eval]

/-- Translation invariance of the arbitrary-dyadic formula as a polynomial
identity. -/
theorem qBinomialThueMorseDyadicTranslatedFormulaPolynomial_eq_const
    (m n : ℕ) :
    qBinomialThueMorseDyadicTranslatedFormulaPolynomial m n =
      Polynomial.C (qBinomialThueMorseDyadicFormula m n) := by
  apply Polynomial.funext
  intro q
  rw [qBinomialThueMorseDyadicTranslatedFormulaPolynomial_eval,
    qBinomialThueMorseDyadicTranslatedFormula_eq_centered,
    Polynomial.eval_C]

/-- The arbitrary-dyadic translated formula has only its constant
coefficient: degree zero is the exact centered value, while every positive
translation coefficient vanishes. -/
theorem qBinomialThueMorseDyadicTranslatedFormulaPolynomial_coeff
    (m n j : ℕ) :
    (qBinomialThueMorseDyadicTranslatedFormulaPolynomial m n).coeff j =
      if j = 0 then qBinomialThueMorseDyadicFormula m n else 0 := by
  rw [qBinomialThueMorseDyadicTranslatedFormulaPolynomial_eq_const]
  by_cases hj : j = 0
  · subst j
    rw [Polynomial.coeff_C_zero, if_pos rfl]
  · rw [Polynomial.coeff_C_of_ne_zero hj, if_neg hj]

/-- Evaluation of the arbitrary-numerator translated formula in a
commutative ring over `ℚ`. -/
def qBinomialThueMorseDyadicTranslatedFormulaIn
    {K : Type*} [CommRing K] [Algebra ℚ K]
    (q : K) (m n : ℕ) : K :=
  Polynomial.eval₂ (algebraMap ℚ K) q
    (qBinomialThueMorseDyadicTranslatedFormulaPolynomial m n)

/-- Scalar evaluation is independent of the common translation. -/
theorem qBinomialThueMorseDyadicTranslatedFormulaIn_eq_centered
    {K : Type*} [CommRing K] [Algebra ℚ K]
    (q : K) (m n : ℕ) :
    qBinomialThueMorseDyadicTranslatedFormulaIn q m n =
      algebraMap ℚ K (qBinomialThueMorseDyadicFormula m n) := by
  rw [qBinomialThueMorseDyadicTranslatedFormulaIn,
    qBinomialThueMorseDyadicTranslatedFormulaPolynomial_eq_const,
    Polynomial.eval₂_C]

/-- Pointwise independence of the scalar translation. -/
theorem qBinomialThueMorseDyadicTranslatedFormulaIn_independent
    {K : Type*} [CommRing K] [Algebra ℚ K]
    (q₁ q₂ : K) (m n : ℕ) :
    qBinomialThueMorseDyadicTranslatedFormulaIn q₁ m n =
      qBinomialThueMorseDyadicTranslatedFormulaIn q₂ m n := by
  rw [qBinomialThueMorseDyadicTranslatedFormulaIn_eq_centered,
    qBinomialThueMorseDyadicTranslatedFormulaIn_eq_centered]

/-- Scalar translated formulas agree whenever their natural numerator and
denominator-exponent pairs represent the same rational number.  The two
scalar translations may differ as well. -/
theorem qBinomialThueMorseDyadicTranslatedFormulaIn_eq_of_rat_eq
    {K : Type*} [CommRing K] [Algebra ℚ K]
    (q₁ q₂ : K) (n₁ n₂ m₁ m₂ : ℕ)
    (h : (m₁ : ℚ) / (2 : ℚ) ^ n₁ =
      (m₂ : ℚ) / (2 : ℚ) ^ n₂) :
    qBinomialThueMorseDyadicTranslatedFormulaIn q₁ m₁ n₁ =
      qBinomialThueMorseDyadicTranslatedFormulaIn q₂ m₂ n₂ := by
  rw [qBinomialThueMorseDyadicTranslatedFormulaIn_eq_centered,
    qBinomialThueMorseDyadicTranslatedFormulaIn_eq_centered,
    qBinomialThueMorseDyadicFormula_eq_of_rat_eq n₁ n₂ m₁ m₂ h]

/-- One binary refinement of the represented dyadic leaves the scalar
translated formula unchanged, even when its translation is changed. -/
theorem qBinomialThueMorseDyadicTranslatedFormulaIn_refine
    {K : Type*} [CommRing K] [Algebra ℚ K]
    (q₁ q₂ : K) (m n : ℕ) :
    qBinomialThueMorseDyadicTranslatedFormulaIn q₁ (2 * m) (n + 1) =
      qBinomialThueMorseDyadicTranslatedFormulaIn q₂ m n := by
  rw [qBinomialThueMorseDyadicTranslatedFormulaIn_eq_centered,
    qBinomialThueMorseDyadicTranslatedFormulaIn_eq_centered,
    qBinomialThueMorseDyadicFormula_refine]

/-- Rational casts agree with the original rational formula. -/
theorem qBinomialThueMorseDyadicTranslatedFormulaIn_ratCast
    {K : Type*} [CommRing K] [Algebra ℚ K]
    (q : ℚ) (m n : ℕ) :
    qBinomialThueMorseDyadicTranslatedFormulaIn
        (algebraMap ℚ K q) m n =
      algebraMap ℚ K (qBinomialThueMorseDyadicTranslatedFormula q m n) := by
  rw [qBinomialThueMorseDyadicTranslatedFormulaIn_eq_centered,
    qBinomialThueMorseDyadicTranslatedFormula_eq_centered]

/-- Literal finite-sum expansion of the scalar-valued formula. -/
theorem qBinomialThueMorseDyadicTranslatedFormulaIn_eq_sum
    {K : Type*} [CommRing K] [Algebra ℚ K]
    (q : K) (m n : ℕ) :
    qBinomialThueMorseDyadicTranslatedFormulaIn q m n =
      algebraMap ℚ K
          (1 / ((2 : ℚ) ^ (n ^ 2) *
            qPochhammer (1 / 2) (1 / 2) n)) *
        ∑ k ∈ Finset.range (n + 1),
          algebraMap ℚ K
              (qBinomial n k (1 / 2) /
                ((4 : ℚ) ^ k.choose 2 *
                  ((n + k).factorial : ℚ))) *
            ∑ r ∈ Finset.range (m * 2 ^ k),
              algebraMap ℚ K (thueMorseSign r : ℚ) *
                ((r : K) - (m : K) * (2 : K) ^ k + q) ^
                  (n + k) := by
  rw [qBinomialThueMorseDyadicTranslatedFormulaIn,
    qBinomialThueMorseDyadicTranslatedFormulaPolynomial]
  simp only [thueMorseDyadicNumeratorTranslatedPowerSumPolynomial,
    Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_finsetSum, Polynomial.eval₂_pow,
    Polynomial.eval₂_add, Polynomial.eval₂_X]
  congr 1
  apply Finset.sum_congr rfl
  intro k _hk
  congr 1
  apply Finset.sum_congr rfl
  intro r _hr
  congr 1
  simp only [map_sub, map_natCast, map_mul, map_pow, map_ofNat]
  ring

/-- Wolfram-style scalar expansion, with sign
`(-1)^ThueMorse[r]` in the target field. -/
theorem qBinomialThueMorseDyadicTranslatedFormulaIn_eq_wolfram_sum
    {K : Type*} [CommRing K] [Algebra ℚ K]
    (q : K) (m n : ℕ) :
    qBinomialThueMorseDyadicTranslatedFormulaIn q m n =
      algebraMap ℚ K
          (1 / ((2 : ℚ) ^ (n ^ 2) *
            qPochhammer (1 / 2) (1 / 2) n)) *
        ∑ k ∈ Finset.range (n + 1),
          algebraMap ℚ K
              (qBinomial n k (1 / 2) /
                ((4 : ℚ) ^ k.choose 2 *
                  ((n + k).factorial : ℚ))) *
            ∑ r ∈ Finset.range (m * 2 ^ k),
              (-1 : K) ^ thueMorseBit r *
                ((r : K) - (m : K) * (2 : K) ^ k + q) ^
                  (n + k) := by
  rw [qBinomialThueMorseDyadicTranslatedFormulaIn_eq_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _hk
  congr 1
  apply Finset.sum_congr rfl
  intro r _hr
  rw [← neg_one_pow_thueMorseBit]
  simp only [map_pow, map_neg, map_one]

/-- Exact arbitrary-dyadic value over every commutative ring
over `ℚ`. -/
theorem fabiusDyadic_algebraMap_eq_qBinomialThueMorseDyadicTranslatedFormulaIn
    {K : Type*} [CommRing K] [Algebra ℚ K]
    (q : K) (m n : ℕ) :
    algebraMap ℚ K (fabiusDyadic n m) =
      qBinomialThueMorseDyadicTranslatedFormulaIn q m n := by
  rw [qBinomialThueMorseDyadicTranslatedFormulaIn_eq_centered,
    fabiusDyadic_eq_qBinomialThueMorseDyadicFormula]

/-- Fully literal generic-scalar arbitrary-dyadic formula. -/
theorem fabiusDyadic_algebraMap_eq_qBinomialThueMorseDyadic_translated_sum
    {K : Type*} [CommRing K] [Algebra ℚ K]
    (q : K) (m n : ℕ) :
    algebraMap ℚ K (fabiusDyadic n m) =
      algebraMap ℚ K
          (1 / ((2 : ℚ) ^ (n ^ 2) *
            qPochhammer (1 / 2) (1 / 2) n)) *
        ∑ k ∈ Finset.range (n + 1),
          algebraMap ℚ K
              (qBinomial n k (1 / 2) /
                ((4 : ℚ) ^ k.choose 2 *
                  ((n + k).factorial : ℚ))) *
            ∑ r ∈ Finset.range (m * 2 ^ k),
              (-1 : K) ^ thueMorseBit r *
                ((r : K) - (m : K) * (2 : K) ^ k + q) ^
                  (n + k) := by
  rw [fabiusDyadic_algebraMap_eq_qBinomialThueMorseDyadicTranslatedFormulaIn,
    qBinomialThueMorseDyadicTranslatedFormulaIn_eq_wolfram_sum]

/-- `RCLike`-valued signed-global dyadic identity for an arbitrary
characterized Fabius function and every scalar translation. -/
theorem extendedFabius_dyadic_eq_qBinomialThueMorseDyadicTranslatedFormulaIn_rclike
    {K : Type*} [RCLike K]
    (F : BoundedFabius) (hF : IsFabius F)
    (q : K) (m n : ℕ) :
    (extendedFabius F ((m : ℝ) / (2 : ℝ) ^ n) : K) =
      qBinomialThueMorseDyadicTranslatedFormulaIn q m n := by
  rw [qBinomialThueMorseDyadicTranslatedFormulaIn_eq_centered]
  have h := congrArg (fun z : ℝ => (z : K))
    (extendedFabius_dyadic_eq_qBinomialThueMorseDyadicFormula
      F hF m n)
  simpa using h

/-- `RCLike`-valued bounded dyadic identity for an arbitrary characterized
Fabius function on the unit interval and every scalar translation. -/
theorem fabiusFunction_dyadic_eq_qBinomialThueMorseDyadicTranslatedFormulaIn_rclike
    {K : Type*} [RCLike K]
    (F : BoundedFabius) (hF : IsFabius F)
    (q : K) (m n : ℕ) (hm : m ≤ 2 ^ n) :
    (fabiusReal F ((m : ℝ) / (2 : ℝ) ^ n) : K) =
      qBinomialThueMorseDyadicTranslatedFormulaIn q m n := by
  rw [qBinomialThueMorseDyadicTranslatedFormulaIn_eq_centered]
  have h := congrArg (fun z : ℝ => (z : K))
    (fabiusFunction_dyadic_eq_qBinomialThueMorseDyadicFormula
      F hF m n hm)
  simpa using h

/-- Signed-global dyadic identity for an arbitrary characterized Fabius
function and every real translation. -/
theorem extendedFabius_dyadic_eq_qBinomialThueMorseDyadicTranslatedFormulaIn_real
    (F : BoundedFabius) (hF : IsFabius F)
    (q : ℝ) (m n : ℕ) :
    extendedFabius F ((m : ℝ) / (2 : ℝ) ^ n) =
      qBinomialThueMorseDyadicTranslatedFormulaIn q m n := by
  rw [qBinomialThueMorseDyadicTranslatedFormulaIn_eq_centered]
  exact extendedFabius_dyadic_eq_qBinomialThueMorseDyadicFormula
    F hF m n

/-- Complex-valued signed-global dyadic identity for an arbitrary
characterized Fabius function and every complex translation. -/
theorem extendedFabius_dyadic_eq_qBinomialThueMorseDyadicTranslatedFormulaIn_complex
    (F : BoundedFabius) (hF : IsFabius F)
    (q : ℂ) (m n : ℕ) :
    (extendedFabius F ((m : ℝ) / (2 : ℝ) ^ n) : ℂ) =
      qBinomialThueMorseDyadicTranslatedFormulaIn q m n := by
  rw [qBinomialThueMorseDyadicTranslatedFormulaIn_eq_centered]
  have h := congrArg (fun z : ℝ => (z : ℂ))
    (extendedFabius_dyadic_eq_qBinomialThueMorseDyadicFormula
      F hF m n)
  push_cast at h
  exact h

/-- Bounded dyadic identity for an arbitrary characterized Fabius function
on the unit interval and every real translation. -/
theorem fabiusFunction_dyadic_eq_qBinomialThueMorseDyadicTranslatedFormulaIn_real
    (F : BoundedFabius) (hF : IsFabius F)
    (q : ℝ) (m n : ℕ) (hm : m ≤ 2 ^ n) :
    fabiusReal F ((m : ℝ) / (2 : ℝ) ^ n) =
      qBinomialThueMorseDyadicTranslatedFormulaIn q m n := by
  rw [qBinomialThueMorseDyadicTranslatedFormulaIn_eq_centered]
  exact fabiusFunction_dyadic_eq_qBinomialThueMorseDyadicFormula
    F hF m n hm

/-- Complex-valued bounded dyadic identity for an arbitrary characterized
Fabius function on the unit interval and every complex translation. -/
theorem fabiusFunction_dyadic_eq_qBinomialThueMorseDyadicTranslatedFormulaIn_complex
    (F : BoundedFabius) (hF : IsFabius F)
    (q : ℂ) (m n : ℕ) (hm : m ≤ 2 ^ n) :
    (fabiusReal F ((m : ℝ) / (2 : ℝ) ^ n) : ℂ) =
      qBinomialThueMorseDyadicTranslatedFormulaIn q m n := by
  rw [qBinomialThueMorseDyadicTranslatedFormulaIn_eq_centered]
  have h := congrArg (fun z : ℝ => (z : ℂ))
    (fabiusFunction_dyadic_eq_qBinomialThueMorseDyadicFormula
      F hF m n hm)
  push_cast at h
  exact h

/-- Canonical signed-global dyadic identity for every real translation. -/
theorem globalFabius_dyadic_eq_qBinomialThueMorseDyadicTranslatedFormulaIn_real
    (q : ℝ) (m n : ℕ) :
    globalFabius ((m : ℝ) / (2 : ℝ) ^ n) =
      qBinomialThueMorseDyadicTranslatedFormulaIn q m n := by
  rw [qBinomialThueMorseDyadicTranslatedFormulaIn_eq_centered]
  exact globalFabius_dyadic_eq_qBinomialThueMorseDyadicFormula m n

/-- Canonical signed-global dyadic identity for every complex translation. -/
theorem globalFabius_dyadic_eq_qBinomialThueMorseDyadicTranslatedFormulaIn_complex
    (q : ℂ) (m n : ℕ) :
    (globalFabius ((m : ℝ) / (2 : ℝ) ^ n) : ℂ) =
      qBinomialThueMorseDyadicTranslatedFormulaIn q m n := by
  rw [qBinomialThueMorseDyadicTranslatedFormulaIn_eq_centered]
  have h := congrArg (fun z : ℝ => (z : ℂ))
    (globalFabius_dyadic_eq_qBinomialThueMorseDyadicFormula m n)
  push_cast at h
  exact h

/-- Gaussian-rational specialization of the canonical complex identity. -/
theorem globalFabius_dyadic_eq_qBinomialThueMorseDyadicTranslatedFormulaIn_gaussianRat
    (a b : ℚ) (m n : ℕ) :
    (globalFabius ((m : ℝ) / (2 : ℝ) ^ n) : ℂ) =
      qBinomialThueMorseDyadicTranslatedFormulaIn
        ((a : ℂ) + (b : ℂ) * Complex.I) m n :=
  globalFabius_dyadic_eq_qBinomialThueMorseDyadicTranslatedFormulaIn_complex
    ((a : ℂ) + (b : ℂ) * Complex.I) m n

/-- Fully displayed canonical signed-global formula for every real
translation. -/
theorem globalFabius_dyadic_eq_qBinomialThueMorseDyadic_translated_sum_real
    (q : ℝ) (m n : ℕ) :
    globalFabius ((m : ℝ) / (2 : ℝ) ^ n) =
      ((1 / ((2 : ℚ) ^ (n ^ 2) *
          qPochhammer (1 / 2) (1 / 2) n) : ℚ) : ℝ) *
        ∑ k ∈ Finset.range (n + 1),
          (qBinomial n k (1 / 2) /
              ((4 : ℚ) ^ k.choose 2 *
                ((n + k).factorial : ℚ)) : ℚ) *
            ∑ r ∈ Finset.range (m * 2 ^ k),
              (-1 : ℝ) ^ thueMorseBit r *
                ((r : ℝ) - (m : ℝ) * (2 : ℝ) ^ k + q) ^
                  (n + k) := by
  rw [globalFabius_dyadic_eq_qBinomialThueMorseDyadicTranslatedFormulaIn_real
      q m n,
    qBinomialThueMorseDyadicTranslatedFormulaIn_eq_wolfram_sum q m n]
  norm_num

/-- Fully displayed canonical signed-global formula for every complex
translation. -/
theorem globalFabius_dyadic_eq_qBinomialThueMorseDyadic_translated_sum_complex
    (q : ℂ) (m n : ℕ) :
    (globalFabius ((m : ℝ) / (2 : ℝ) ^ n) : ℂ) =
      ((1 / ((2 : ℚ) ^ (n ^ 2) *
          qPochhammer (1 / 2) (1 / 2) n) : ℚ) : ℂ) *
        ∑ k ∈ Finset.range (n + 1),
          (qBinomial n k (1 / 2) /
              ((4 : ℚ) ^ k.choose 2 *
                ((n + k).factorial : ℚ)) : ℚ) *
            ∑ r ∈ Finset.range (m * 2 ^ k),
              (-1 : ℂ) ^ thueMorseBit r *
                ((r : ℂ) - (m : ℂ) * (2 : ℂ) ^ k + q) ^
                  (n + k) := by
  rw [globalFabius_dyadic_eq_qBinomialThueMorseDyadicTranslatedFormulaIn_complex
      q m n,
    qBinomialThueMorseDyadicTranslatedFormulaIn_eq_wolfram_sum q m n]
  norm_num

/-- Bounded Fabius identity on the unit dyadic interval for every real
translation. -/
theorem fabius_dyadic_eq_qBinomialThueMorseDyadicTranslatedFormulaIn_real
    (q : ℝ) (m n : ℕ) (hm : m ≤ 2 ^ n) :
    fabiusReal fabius ((m : ℝ) / (2 : ℝ) ^ n) =
      qBinomialThueMorseDyadicTranslatedFormulaIn q m n := by
  exact fabiusFunction_dyadic_eq_qBinomialThueMorseDyadicTranslatedFormulaIn_real
    fabius fabius_spec q m n hm

/-- Bounded Fabius identity on the unit dyadic interval for every complex
translation. -/
theorem fabius_dyadic_eq_qBinomialThueMorseDyadicTranslatedFormulaIn_complex
    (q : ℂ) (m n : ℕ) (hm : m ≤ 2 ^ n) :
    (fabiusReal fabius ((m : ℝ) / (2 : ℝ) ^ n) : ℂ) =
      qBinomialThueMorseDyadicTranslatedFormulaIn q m n := by
  exact fabiusFunction_dyadic_eq_qBinomialThueMorseDyadicTranslatedFormulaIn_complex
    fabius fabius_spec q m n hm

end

end Fabius
