import FabiusFunction.FabiusSaddleExpansionCoefficients
import FabiusFunction.FabiusSaddleExponentClosedForm

/-!
# The second periodic saddle correction for the Fabius function

`FabiusSaddleExpansionCoefficients` identifies the first coefficient of the
all-orders central saddle expansion with the closed periodic function
`fabiusFirstSaddleCorrection`.  This module does the same one order further:
it computes `fabiusSaddleMassCoefficient 2` and
`fabiusSaddleLogCoefficient 2` in closed form.

## The parametrization

Write `d n = negativeLaplaceBoundedExponentJet n t` for the bounded exponent
jets.  By `negativeLaplaceExponentPolynomial_succ_eq` the exponent polynomials
are

```text
E 1 = I * (d 0 * X + X^3/3)
E 2 = -(d 1) * X^2/2 + X^4/4
E 3 = I * (-(d 2) * X^3/6 - X^5/5)
E 4 = (d 3) * X^4/24 - X^6/6
```

so `E 1` and `E 3` are `I` times a polynomial with real-analytic coefficients
while `E 2` and `E 4` already have such coefficients.  In this parametrization
the first coefficient becomes strikingly short,

```text
fabiusFirstSaddleCorrection t = -(d 0)^2/2 - d 0 - (d 1)/2 - 1/12,
```

which is proved here as `fabiusFirstSaddleCorrection_eq_jets` and validates the
whole parametrization against the already-established closed form.

## The method

The order-4 coefficient of the generic exponential recurrence
`SaddleExpansion.expCoeff` is

```text
expCoeff E 4 = E 4 + E 3 * E 1 + (E 2)^2/2 + E 2 * (E 1)^2/2 + (E 1)^4/24.
```

Since a commutative `ℚ`-algebra need not be a field, the recurrence is first
unwound in the denominator-cleared form `24 * expCoeff E 4 = ...`; the
`ℚ`-scaled forms `expCoeff_two`, `expCoeff_three` and `expCoeff_four` are then
immediate.  A separate generic lemma,
`twentyFour_mul_expCoeff_four_of_sq_eq_neg_one`, records that whenever the odd
exponent coefficients carry a common square root of `-1`, every power of that
root cancels at order four; this is what makes the Fabius mass coefficient
real without any further conjugation argument.

Substituting the four exponent polynomials produces a polynomial with only even
powers,

```text
expCoeff E 4 =
    (d0^4/24 + d0^2 d1/4 + d0 d2/6 + d1^2/8 + d3/24) X^4
  + (d0^3/18 - d0^2/8 + d0 d1/6 + d0/5 - d1/8 + d2/18 - 1/6) X^6
  + (d0^2/36 - d0/12 + d1/36 + 47/480) X^8
  + (d0/162 - 1/72) X^10
  + X^12/1944,
```

and contracting it monomialwise against the normalized Gaussian moments
`(3, 15, 105, 945, 10395)` gives the mass coefficient.  Finally
`SaddleExpansion.logCoeff_two` converts the mass coefficient into the
logarithmic one, whose closed form is `fabiusSecondSaddleCorrection`:

```text
fabiusSecondSaddleCorrection
  = (8 d0^3 + 12 d0^2 d1 + 12 d0^2 + 48 d0 d1 + 12 d0 d2
      + 6 d1^2 + 24 d1 + 20 d2 + 3 d3) / 24.
```

Every jet is bounded, one-periodic and `C∞`, so the same three properties are
recorded for the correction at the end of the module.
-/

set_option autoImplicit false

open scoped BigOperators ContDiff

namespace Fabius

open Complex Polynomial SaddleExpansion

noncomputable section

/-- The second periodic coefficient after the sharp Lambert main term,
expressed in the bounded exponent jets `negativeLaplaceBoundedExponentJet`.

The full logarithmic expansion begins

`log F(x) = fabiusSharpLambertMain x +
  fabiusFirstSaddleCorrection (fabiusLambertPhase x) / fabiusLambertPhase x +
  fabiusSecondSaddleCorrection (fabiusLambertPhase x) /
    fabiusLambertPhase x ^ 2 + ...`.
-/
def fabiusSecondSaddleCorrection (u : ℝ) : ℝ :=
  (8 * negativeLaplaceBoundedExponentJet 0 u ^ 3 +
      12 * negativeLaplaceBoundedExponentJet 0 u ^ 2 *
        negativeLaplaceBoundedExponentJet 1 u +
      12 * negativeLaplaceBoundedExponentJet 0 u ^ 2 +
      48 * negativeLaplaceBoundedExponentJet 0 u *
        negativeLaplaceBoundedExponentJet 1 u +
      12 * negativeLaplaceBoundedExponentJet 0 u *
        negativeLaplaceBoundedExponentJet 2 u +
      6 * negativeLaplaceBoundedExponentJet 1 u ^ 2 +
      24 * negativeLaplaceBoundedExponentJet 1 u +
      20 * negativeLaplaceBoundedExponentJet 2 u +
      3 * negativeLaplaceBoundedExponentJet 3 u) / 24

/-- The first saddle correction in the bounded exponent jets.  This is the
same function as `fabiusFirstSaddleCorrection`, but in the parametrization
that makes the higher coefficients manageable. -/
theorem fabiusFirstSaddleCorrection_eq_jets (u : ℝ) :
    fabiusFirstSaddleCorrection u =
      -negativeLaplaceBoundedExponentJet 0 u ^ 2 / 2 -
        negativeLaplaceBoundedExponentJet 0 u -
        negativeLaplaceBoundedExponentJet 1 u / 2 - 1 / 12 := by
  have hL : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [negativeLaplaceBoundedExponentJet_zero,
    negativeLaplaceBoundedExponentJet_one]
  unfold fabiusFirstSaddleCorrection
  field_simp
  ring

namespace SaddleExpansion

variable {R : Type*} [CommRing R] [Algebra ℚ R]

private theorem algebraMap_mul_inv_smul {q : ℚ} (hq : q ≠ 0) (x : R) :
    algebraMap ℚ R q * (q⁻¹ • x) = x := by
  rw [Algebra.smul_def, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hq, map_one,
    one_mul]

private theorem eq_inv_smul_of_algebraMap_mul {q : ℚ} (hq : q ≠ 0) {x y : R}
    (h : algebraMap ℚ R q * x = y) : x = q⁻¹ • y := by
  rw [← h, Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hq,
    map_one, one_mul]

private theorem two_mul_inv_two_smul (x : R) :
    (2 : R) * (((2 : ℚ)⁻¹) • x) = x := by
  have hmap : algebraMap ℚ R (2 : ℚ) = (2 : R) := map_ofNat (algebraMap ℚ R) 2
  rw [← hmap]
  exact algebraMap_mul_inv_smul (q := (2 : ℚ)) (by norm_num) x

/-- The defining recurrence of `expCoeff` with the rational scalar cleared.
This is the form in which the low-order coefficients are unwound over a
commutative `ℚ`-algebra that need not be a field. -/
theorem natCast_succ_mul_expCoeff_succ (E : ℕ → R) (n : ℕ) :
    ((n : R) + 1) * expCoeff E (n + 1) =
      ∑ j ∈ Finset.range (n + 1),
        ((j : R) + 1) * E (j + 1) * expCoeff E (n - j) := by
  have hq : ((n : ℚ) + 1) ≠ 0 := by
    have hn : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n
    intro hzero
    linarith
  have hmap : algebraMap ℚ R ((n : ℚ) + 1) = ((n : R) + 1) := by
    rw [map_add, map_natCast, map_one]
  rw [expCoeff_succ, ← hmap, algebraMap_mul_inv_smul hq]

/-- Order one of the formal exponential. -/
theorem expCoeff_one (E : ℕ → R) : expCoeff E 1 = E 1 := by
  simpa [Finset.sum_range_one] using natCast_succ_mul_expCoeff_succ E 0

/-- Order two of the formal exponential, with the rational scalar cleared. -/
theorem two_mul_expCoeff_two (E : ℕ → R) :
    (2 : R) * expCoeff E 2 = 2 * E 2 + E 1 * E 1 := by
  have h := natCast_succ_mul_expCoeff_succ E 1
  norm_num [Finset.sum_range_succ, expCoeff_one] at h
  linear_combination h

/-- Order three of the formal exponential, with the rational scalar cleared. -/
theorem six_mul_expCoeff_three (E : ℕ → R) :
    (6 : R) * expCoeff E 3 =
      6 * E 3 + 6 * (E 1 * E 2) + E 1 * E 1 * E 1 := by
  have h2 := two_mul_expCoeff_two E
  have h := natCast_succ_mul_expCoeff_succ E 2
  norm_num [Finset.sum_range_succ, expCoeff_one] at h
  linear_combination 2 * h + E 1 * h2

/-- Order four of the formal exponential, with the rational scalar cleared. -/
theorem twentyFour_mul_expCoeff_four (E : ℕ → R) :
    (24 : R) * expCoeff E 4 =
      24 * E 4 + 24 * (E 1 * E 3) + 12 * (E 2 * E 2) +
        12 * (E 1 * E 1 * E 2) + E 1 * E 1 * E 1 * E 1 := by
  have h2 := two_mul_expCoeff_two E
  have h3 := six_mul_expCoeff_three E
  have h := natCast_succ_mul_expCoeff_succ E 3
  norm_num [Finset.sum_range_succ, expCoeff_one] at h
  linear_combination 6 * h + E 1 * h3 + 6 * E 2 * h2

/-- Order two of the formal exponential. -/
theorem expCoeff_two (E : ℕ → R) :
    expCoeff E 2 = ((2 : ℚ)⁻¹) • (2 * E 2 + E 1 * E 1) := by
  refine eq_inv_smul_of_algebraMap_mul (q := (2 : ℚ)) (by norm_num) ?_
  rw [show algebraMap ℚ R (2 : ℚ) = (2 : R) from map_ofNat (algebraMap ℚ R) 2]
  exact two_mul_expCoeff_two E

/-- Order three of the formal exponential. -/
theorem expCoeff_three (E : ℕ → R) :
    expCoeff E 3 =
      ((6 : ℚ)⁻¹) • (6 * E 3 + 6 * (E 1 * E 2) + E 1 * E 1 * E 1) := by
  refine eq_inv_smul_of_algebraMap_mul (q := (6 : ℚ)) (by norm_num) ?_
  rw [show algebraMap ℚ R (6 : ℚ) = (6 : R) from map_ofNat (algebraMap ℚ R) 6]
  exact six_mul_expCoeff_three E

/-- Order four of the formal exponential.  Written out, this is
`E 4 + E 3 * E 1 + (E 2)^2/2 + E 2 * (E 1)^2/2 + (E 1)^4/24`. -/
theorem expCoeff_four (E : ℕ → R) :
    expCoeff E 4 =
      ((24 : ℚ)⁻¹) • (24 * E 4 + 24 * (E 1 * E 3) + 12 * (E 2 * E 2) +
        12 * (E 1 * E 1 * E 2) + E 1 * E 1 * E 1 * E 1) := by
  refine eq_inv_smul_of_algebraMap_mul (q := (24 : ℚ)) (by norm_num) ?_
  rw [show algebraMap ℚ R (24 : ℚ) = (24 : R) from
    map_ofNat (algebraMap ℚ R) 24]
  exact twentyFour_mul_expCoeff_four E

/-- If the odd exponent coefficients carry a common square root `w` of `-1`
and the even ones carry none, then all powers of `w` cancel at order four:
the order-four exponential coefficient is a polynomial with integer
coefficients in the `w`-free parts alone. -/
theorem twentyFour_mul_expCoeff_four_of_sq_eq_neg_one
    (E : ℕ → R) (w a1 a2 a3 a4 : R) (hw : w * w = -1)
    (h1 : E 1 = w * a1) (h2 : E 2 = a2) (h3 : E 3 = w * a3)
    (h4 : E 4 = a4) :
    (24 : R) * expCoeff E 4 =
      24 * a4 - 24 * (a1 * a3) + 12 * (a2 * a2) - 12 * (a1 * a1 * a2) +
        a1 * a1 * a1 * a1 := by
  rw [twentyFour_mul_expCoeff_four, h1, h2, h3, h4]
  linear_combination (24 * (a1 * a3) + 12 * (a1 * a1 * a2) +
    (w * w - 1) * (a1 * a1 * a1 * a1)) * hw

/-- Order two of the formal logarithm, with the rational scalar cleared. -/
theorem two_mul_logCoeff_two (a : ℕ → R) :
    (2 : R) * logCoeff a 2 = 2 * a 2 - a 1 * a 1 := by
  rw [logCoeff_two, mul_sub, two_mul_inv_two_smul]

end SaddleExpansion

private def secondSaddleExponentQ1 (t : ℝ) : Polynomial ℂ :=
  C (negativeLaplaceBoundedExponentJet 0 t : ℂ) * X + C (1 / 3 : ℂ) * X ^ 3

private def secondSaddleExponentQ2 (t : ℝ) : Polynomial ℂ :=
  C (-(negativeLaplaceBoundedExponentJet 1 t : ℂ) / 2) * X ^ 2 +
    C (1 / 4 : ℂ) * X ^ 4

private def secondSaddleExponentQ3 (t : ℝ) : Polynomial ℂ :=
  C (-(negativeLaplaceBoundedExponentJet 2 t : ℂ) / 6) * X ^ 3 +
    C (-1 / 5 : ℂ) * X ^ 5

private def secondSaddleExponentQ4 (t : ℝ) : Polynomial ℂ :=
  C ((negativeLaplaceBoundedExponentJet 3 t : ℂ) / 24) * X ^ 4 +
    C (-1 / 6 : ℂ) * X ^ 6

private theorem secondSaddleExponent_one (t : ℝ) :
    negativeLaplaceExponentPolynomial 1 t = C I * secondSaddleExponentQ1 t := by
  refine (negativeLaplaceExponentPolynomial_succ_eq 0 t).trans ?_
  rw [show Nat.factorial (0 + 1) = 1 from rfl,
    show Complex.I ^ (0 + 1) = Complex.I from pow_one _]
  unfold secondSaddleExponentQ1
  apply Polynomial.funext
  intro z
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat]
  ring

private theorem secondSaddleExponent_two (t : ℝ) :
    negativeLaplaceExponentPolynomial 2 t = secondSaddleExponentQ2 t := by
  refine (negativeLaplaceExponentPolynomial_succ_eq 1 t).trans ?_
  rw [show Nat.factorial (1 + 1) = 2 from rfl,
    show Complex.I ^ (1 + 1) = -1 from Complex.I_sq]
  unfold secondSaddleExponentQ2
  apply Polynomial.funext
  intro z
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat]
  ring

private theorem secondSaddleExponent_three (t : ℝ) :
    negativeLaplaceExponentPolynomial 3 t = C I * secondSaddleExponentQ3 t := by
  have hI3 : Complex.I ^ (2 + 1) = -Complex.I := by
    rw [pow_succ, Complex.I_sq]
    ring
  refine (negativeLaplaceExponentPolynomial_succ_eq 2 t).trans ?_
  rw [show Nat.factorial (2 + 1) = 6 from rfl, hI3]
  unfold secondSaddleExponentQ3
  apply Polynomial.funext
  intro z
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat]
  ring

private theorem secondSaddleExponent_four (t : ℝ) :
    negativeLaplaceExponentPolynomial 4 t = secondSaddleExponentQ4 t := by
  refine (negativeLaplaceExponentPolynomial_succ_eq 3 t).trans ?_
  rw [show Nat.factorial (3 + 1) = 24 from rfl,
    show Complex.I ^ (3 + 1) = 1 from Complex.I_pow_four]
  unfold secondSaddleExponentQ4
  apply Polynomial.funext
  intro z
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat]
  ring

private theorem C_I_mul_C_I : (C I : Polynomial ℂ) * C I = -1 := by
  rw [← Polynomial.C_mul, Complex.I_mul_I, Polynomial.C_neg, Polynomial.C_1]

/-- The order-four exponential coefficient of the Fabius saddle exponent.
All odd powers of the Gaussian variable are absent and every coefficient is
real, which is what makes the contracted mass coefficient real. -/
theorem expCoeff_four_negativeLaplaceExponentPolynomial (t : ℝ) :
    expCoeff (fun m => negativeLaplaceExponentPolynomial m t) 4 =
      C ((negativeLaplaceBoundedExponentJet 0 t : ℂ) ^ 4 / 24 +
            (negativeLaplaceBoundedExponentJet 0 t : ℂ) ^ 2 *
              (negativeLaplaceBoundedExponentJet 1 t : ℂ) / 4 +
            (negativeLaplaceBoundedExponentJet 0 t : ℂ) *
              (negativeLaplaceBoundedExponentJet 2 t : ℂ) / 6 +
            (negativeLaplaceBoundedExponentJet 1 t : ℂ) ^ 2 / 8 +
            (negativeLaplaceBoundedExponentJet 3 t : ℂ) / 24) * X ^ 4 +
        C ((negativeLaplaceBoundedExponentJet 0 t : ℂ) ^ 3 / 18 -
            (negativeLaplaceBoundedExponentJet 0 t : ℂ) ^ 2 / 8 +
            (negativeLaplaceBoundedExponentJet 0 t : ℂ) *
              (negativeLaplaceBoundedExponentJet 1 t : ℂ) / 6 +
            (negativeLaplaceBoundedExponentJet 0 t : ℂ) / 5 -
            (negativeLaplaceBoundedExponentJet 1 t : ℂ) / 8 +
            (negativeLaplaceBoundedExponentJet 2 t : ℂ) / 18 - 1 / 6) * X ^ 6 +
        C ((negativeLaplaceBoundedExponentJet 0 t : ℂ) ^ 2 / 36 -
            (negativeLaplaceBoundedExponentJet 0 t : ℂ) / 12 +
            (negativeLaplaceBoundedExponentJet 1 t : ℂ) / 36 +
            47 / 480) * X ^ 8 +
        C ((negativeLaplaceBoundedExponentJet 0 t : ℂ) / 162 - 1 / 72) *
          X ^ 10 +
        C (1 / 1944 : ℂ) * X ^ 12 := by
  have hC24 : Polynomial.C (24 : ℂ) = (24 : Polynomial ℂ) :=
    map_ofNat Polynomial.C 24
  have h24 : (24 : Polynomial ℂ) ≠ 0 := by
    rw [← hC24]
    exact Polynomial.C_ne_zero.mpr (by norm_num)
  refine mul_left_cancel₀ h24
    ((twentyFour_mul_expCoeff_four_of_sq_eq_neg_one
        (fun m => negativeLaplaceExponentPolynomial m t) (C I)
        (secondSaddleExponentQ1 t) (secondSaddleExponentQ2 t)
        (secondSaddleExponentQ3 t) (secondSaddleExponentQ4 t) C_I_mul_C_I
        (secondSaddleExponent_one t) (secondSaddleExponent_two t)
        (secondSaddleExponent_three t) (secondSaddleExponent_four t)).trans ?_)
  unfold secondSaddleExponentQ1 secondSaddleExponentQ2 secondSaddleExponentQ3
    secondSaddleExponentQ4
  apply Polynomial.funext
  intro z
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow,
    Polynomial.eval_ofNat]
  ring

private theorem gaussianContraction_C_mul_X_pow (c : ℂ) (n : ℕ) :
    gaussianPolynomialContraction (C c * X ^ n) =
      c * normalizedGaussianMoment n := by
  rw [Polynomial.C_mul']
  simp

private theorem gaussianMoment_four : normalizedGaussianMoment 4 = 3 := by
  norm_num [normalizedGaussianMoment]

private theorem gaussianMoment_six : normalizedGaussianMoment 6 = 15 := by
  norm_num [normalizedGaussianMoment]

private theorem gaussianMoment_eight : normalizedGaussianMoment 8 = 105 := by
  norm_num [normalizedGaussianMoment]

private theorem gaussianMoment_ten : normalizedGaussianMoment 10 = 945 := by
  norm_num [normalizedGaussianMoment]

private theorem gaussianMoment_twelve :
    normalizedGaussianMoment 12 = 10395 := by
  norm_num [normalizedGaussianMoment]

/-- Contraction of the five-monomial even polynomial produced at order four.

The coefficients are taken as abstract variables on purpose.  Contracting the
concrete polynomial with `simp only [map_add, …]` does not work: `Polynomial.C`
is itself a ring homomorphism, so `map_add` rewrites `C (a + b)` into
`C a + C b` inside each coefficient, and the resulting `(C a + C b) * X ^ n` no
longer matches the monomial contraction lemma.  Splitting the sum here, where
the coefficients cannot be decomposed, avoids that entirely. -/
private theorem gaussianContraction_even_five (c4 c6 c8 c10 c12 : ℂ) :
    gaussianPolynomialContraction
        (C c4 * X ^ 4 + C c6 * X ^ 6 + C c8 * X ^ 8 + C c10 * X ^ 10 +
          C c12 * X ^ 12) =
      c4 * normalizedGaussianMoment 4 + c6 * normalizedGaussianMoment 6 +
        c8 * normalizedGaussianMoment 8 + c10 * normalizedGaussianMoment 10 +
          c12 * normalizedGaussianMoment 12 := by
  rw [map_add, map_add, map_add, map_add,
    gaussianContraction_C_mul_X_pow, gaussianContraction_C_mul_X_pow,
    gaussianContraction_C_mul_X_pow, gaussianContraction_C_mul_X_pow,
    gaussianContraction_C_mul_X_pow]

/-- The complex Gaussian mass coefficient of order `lambda^{-2}` in closed
form.  It is the image of a real number, as it must be. -/
theorem fabiusSaddleMassCoefficientComplex_two (t : ℝ) :
    fabiusSaddleMassCoefficientComplex 2 t =
      ((negativeLaplaceBoundedExponentJet 0 t ^ 4 / 8 +
          5 * negativeLaplaceBoundedExponentJet 0 t ^ 3 / 6 +
          3 * negativeLaplaceBoundedExponentJet 0 t ^ 2 *
            negativeLaplaceBoundedExponentJet 1 t / 4 +
          25 * negativeLaplaceBoundedExponentJet 0 t ^ 2 / 24 +
          5 * negativeLaplaceBoundedExponentJet 0 t *
            negativeLaplaceBoundedExponentJet 1 t / 2 +
          negativeLaplaceBoundedExponentJet 0 t *
            negativeLaplaceBoundedExponentJet 2 t / 2 +
          negativeLaplaceBoundedExponentJet 0 t / 12 +
          3 * negativeLaplaceBoundedExponentJet 1 t ^ 2 / 8 +
          25 * negativeLaplaceBoundedExponentJet 1 t / 24 +
          5 * negativeLaplaceBoundedExponentJet 2 t / 6 +
          negativeLaplaceBoundedExponentJet 3 t / 8 + 1 / 288 : ℝ) : ℂ) := by
  unfold fabiusSaddleMassCoefficientComplex
  rw [show 2 * 2 = 4 by omega,
    expCoeff_four_negativeLaplaceExponentPolynomial,
    gaussianContraction_even_five,
    gaussianMoment_four, gaussianMoment_six, gaussianMoment_eight,
    gaussianMoment_ten, gaussianMoment_twelve]
  push_cast
  ring

/-- The real Gaussian mass coefficient of order `lambda^{-2}` in closed
form. -/
theorem fabiusSaddleMassCoefficient_two (t : ℝ) :
    fabiusSaddleMassCoefficient 2 t =
      negativeLaplaceBoundedExponentJet 0 t ^ 4 / 8 +
        5 * negativeLaplaceBoundedExponentJet 0 t ^ 3 / 6 +
        3 * negativeLaplaceBoundedExponentJet 0 t ^ 2 *
          negativeLaplaceBoundedExponentJet 1 t / 4 +
        25 * negativeLaplaceBoundedExponentJet 0 t ^ 2 / 24 +
        5 * negativeLaplaceBoundedExponentJet 0 t *
          negativeLaplaceBoundedExponentJet 1 t / 2 +
        negativeLaplaceBoundedExponentJet 0 t *
          negativeLaplaceBoundedExponentJet 2 t / 2 +
        negativeLaplaceBoundedExponentJet 0 t / 12 +
        3 * negativeLaplaceBoundedExponentJet 1 t ^ 2 / 8 +
        25 * negativeLaplaceBoundedExponentJet 1 t / 24 +
        5 * negativeLaplaceBoundedExponentJet 2 t / 6 +
        negativeLaplaceBoundedExponentJet 3 t / 8 + 1 / 288 := by
  apply Complex.ofReal_injective
  rw [ofReal_fabiusSaddleMassCoefficient,
    fabiusSaddleMassCoefficientComplex_two]

/-- The second logarithmic saddle coefficient is the closed periodic function
`fabiusSecondSaddleCorrection`. -/
theorem fabiusSaddleLogCoefficient_two_eq_secondSaddleCorrection (t : ℝ) :
    fabiusSaddleLogCoefficient 2 t = fabiusSecondSaddleCorrection t := by
  have h : (2 : ℝ) * fabiusSaddleLogCoefficient 2 t =
      2 * fabiusSaddleMassCoefficient 2 t -
        fabiusSaddleMassCoefficient 1 t * fabiusSaddleMassCoefficient 1 t :=
    two_mul_logCoeff_two (fun k => fabiusSaddleMassCoefficient k t)
  rw [fabiusSaddleMassCoefficient_two, fabiusSaddleMassCoefficient_one,
    fabiusFirstSaddleCorrection_eq_jets] at h
  unfold fabiusSecondSaddleCorrection
  linear_combination h / 2

/-- The second saddle correction is one-periodic. -/
theorem fabiusSecondSaddleCorrection_periodic :
    Function.Periodic fabiusSecondSaddleCorrection 1 := by
  intro u
  unfold fabiusSecondSaddleCorrection
  rw [negativeLaplaceBoundedExponentJet_periodic 0 u,
    negativeLaplaceBoundedExponentJet_periodic 1 u,
    negativeLaplaceBoundedExponentJet_periodic 2 u,
    negativeLaplaceBoundedExponentJet_periodic 3 u]

/-- The second saddle correction is `C∞`. -/
theorem contDiff_infty_fabiusSecondSaddleCorrection :
    ContDiff ℝ ∞ fabiusSecondSaddleCorrection := by
  have h0 : ContDiff ℝ ∞ (negativeLaplaceBoundedExponentJet 0) :=
    contDiff_infty_negativeLaplaceBoundedExponentJet 0
  have h1 : ContDiff ℝ ∞ (negativeLaplaceBoundedExponentJet 1) :=
    contDiff_infty_negativeLaplaceBoundedExponentJet 1
  have h2 : ContDiff ℝ ∞ (negativeLaplaceBoundedExponentJet 2) :=
    contDiff_infty_negativeLaplaceBoundedExponentJet 2
  have h3 : ContDiff ℝ ∞ (negativeLaplaceBoundedExponentJet 3) :=
    contDiff_infty_negativeLaplaceBoundedExponentJet 3
  have t0 : ContDiff ℝ ∞ fun u : ℝ =>
      8 * negativeLaplaceBoundedExponentJet 0 u ^ 3 :=
    contDiff_const.mul (h0.pow 3)
  have t1 : ContDiff ℝ ∞ fun u : ℝ =>
      12 * negativeLaplaceBoundedExponentJet 0 u ^ 2 *
        negativeLaplaceBoundedExponentJet 1 u :=
    (contDiff_const.mul (h0.pow 2)).mul h1
  have t2 : ContDiff ℝ ∞ fun u : ℝ =>
      12 * negativeLaplaceBoundedExponentJet 0 u ^ 2 :=
    contDiff_const.mul (h0.pow 2)
  have t3 : ContDiff ℝ ∞ fun u : ℝ =>
      48 * negativeLaplaceBoundedExponentJet 0 u *
        negativeLaplaceBoundedExponentJet 1 u :=
    (contDiff_const.mul h0).mul h1
  have t4 : ContDiff ℝ ∞ fun u : ℝ =>
      12 * negativeLaplaceBoundedExponentJet 0 u *
        negativeLaplaceBoundedExponentJet 2 u :=
    (contDiff_const.mul h0).mul h2
  have t5 : ContDiff ℝ ∞ fun u : ℝ =>
      6 * negativeLaplaceBoundedExponentJet 1 u ^ 2 :=
    contDiff_const.mul (h1.pow 2)
  have t6 : ContDiff ℝ ∞ fun u : ℝ =>
      24 * negativeLaplaceBoundedExponentJet 1 u :=
    contDiff_const.mul h1
  have t7 : ContDiff ℝ ∞ fun u : ℝ =>
      20 * negativeLaplaceBoundedExponentJet 2 u :=
    contDiff_const.mul h2
  have t8 : ContDiff ℝ ∞ fun u : ℝ =>
      3 * negativeLaplaceBoundedExponentJet 3 u :=
    contDiff_const.mul h3
  unfold fabiusSecondSaddleCorrection
  exact ((((((((t0.add t1).add t2).add t3).add t4).add t5).add t6).add
    t7).add t8).div_const 24

/-- The second saddle correction is continuous. -/
theorem continuous_fabiusSecondSaddleCorrection :
    Continuous fabiusSecondSaddleCorrection :=
  contDiff_infty_fabiusSecondSaddleCorrection.continuous

/-- The second saddle correction has globally bounded range. -/
theorem isBounded_range_fabiusSecondSaddleCorrection :
    Bornology.IsBounded (Set.range fabiusSecondSaddleCorrection) :=
  fabiusSecondSaddleCorrection_periodic.isBounded_of_continuous one_ne_zero
    continuous_fabiusSecondSaddleCorrection

end

end Fabius
