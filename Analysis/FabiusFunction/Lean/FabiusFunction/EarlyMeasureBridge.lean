import FabiusFunction.EarlyApproximants

/-!
# The polynomial/convolution bridge in Theorem 2

This file proves that the atomic measure encoded by the generating
polynomial in equations (14)--(19) is the finite Bernoulli convolution
from equation (12).
-/

open scoped BigOperators ENNReal MeasureTheory
open Finset MeasureTheory

namespace Fabius

set_option autoImplicit false

noncomputable section

private lemma polynomialMeasure_charFun_eq_eval₂ (n : ℕ) (t : ℝ) :
    charFun (polynomialMeasure n) t =
      ((2 : ℂ) ^ ((n + 1).choose 2))⁻¹ *
        Complex.exp
          (-(t * (approximationDegree n : ℝ) / (2 : ℝ) ^ (n + 1)) *
            Complex.I) *
        (approximationPolynomial n).eval₂ (Nat.castRingHom ℂ)
          (Complex.exp (t / (2 : ℝ) ^ n * Complex.I)) := by
  rw [polynomialMeasure_charFun_sum, Polynomial.eval₂_eq_sum_range,
    approximationPolynomial_natDegree]
  rw [mul_assoc, mul_sum, mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hexp :
      Complex.exp (t * polynomialAtomLocation n m * Complex.I) =
        Complex.exp
            (-(t * (approximationDegree n : ℝ) / (2 : ℝ) ^ (n + 1)) *
              Complex.I) *
          Complex.exp (t / (2 : ℝ) ^ n * Complex.I) ^ m := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    dsimp [polynomialAtomLocation]
    push_cast
    field_simp
    ring
  rw [hexp]
  push_cast
  field_simp

private lemma centeredBinomialBase (x : ℝ) :
    (2 : ℂ)⁻¹ * Complex.exp (-(x : ℂ) * Complex.I) *
        (1 + Complex.exp (2 * (x : ℂ) * Complex.I)) =
      (Real.cos x : ℂ) := by
  rw [Complex.ofReal_cos, Complex.cos]
  have htwo :
      Complex.exp (2 * (x : ℂ) * Complex.I) =
        Complex.exp ((x : ℂ) * Complex.I) *
          Complex.exp ((x : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hcancel :
      Complex.exp (-(x : ℂ) * Complex.I) *
          Complex.exp ((x : ℂ) * Complex.I) = 1 := by
    calc
      _ = Complex.exp
          (-(x : ℂ) * Complex.I + (x : ℂ) * Complex.I) :=
        (Complex.exp_add _ _).symm
      _ = 1 := by rw [show -(x : ℂ) * Complex.I + x * Complex.I = 0 by ring,
        Complex.exp_zero]
  rw [htwo]
  have hprod :
      Complex.exp (-(x : ℂ) * Complex.I) *
          (1 + Complex.exp ((x : ℂ) * Complex.I) *
            Complex.exp ((x : ℂ) * Complex.I)) =
        Complex.exp (-(x : ℂ) * Complex.I) +
          Complex.exp ((x : ℂ) * Complex.I) := by
    rw [mul_add, mul_one, ← mul_assoc, hcancel, one_mul]
  rw [mul_assoc, hprod]
  field_simp
  ring

private lemma centeredBinomialFactor (r : ℕ) (x : ℝ) :
    ((2 : ℂ) ^ r)⁻¹ *
        Complex.exp (-((r : ℂ) * (x : ℂ)) * Complex.I) *
        (1 + Complex.exp (2 * (x : ℂ) * Complex.I)) ^ r =
      (Real.cos x : ℂ) ^ r := by
  have hexp :
      Complex.exp (-((r : ℂ) * (x : ℂ)) * Complex.I) =
        Complex.exp (-(x : ℂ) * Complex.I) ^ r := by
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  rw [← inv_pow, hexp, ← mul_pow, ← mul_pow, centeredBinomialBase]

private lemma approximationPolynomial_eval₂_succ (n : ℕ) (t : ℝ) :
    (approximationPolynomial (n + 1)).eval₂ (Nat.castRingHom ℂ)
        (Complex.exp (t / (2 : ℝ) ^ (n + 1) * Complex.I)) =
      (approximationPolynomial n).eval₂ (Nat.castRingHom ℂ)
          (Complex.exp (t / (2 : ℝ) ^ n * Complex.I)) *
        (1 + Complex.exp (t / (2 : ℝ) ^ (n + 1) * Complex.I)) ^
          (n + 1) := by
  have hzsq :
      Complex.exp (t / (2 : ℝ) ^ (n + 1) * Complex.I) ^ 2 =
        Complex.exp (t / (2 : ℝ) ^ n * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    rw [pow_succ]
    field_simp
  rw [approximationPolynomial_succ, Polynomial.eval₂_mul,
    Polynomial.eval₂_comp]
  simp only [Polynomial.eval₂_pow, Polynomial.eval₂_add,
    Polynomial.eval₂_one, Polynomial.eval₂_X]
  rw [hzsq]

/-- Successive polynomial measures acquire exactly the next centered
binomial characteristic-function factor. -/
lemma polynomialMeasure_charFun_succ (n : ℕ) (t : ℝ) :
    charFun (polynomialMeasure (n + 1)) t =
      charFun (polynomialMeasure n) t *
        (Real.cos (t / (2 : ℝ) ^ (n + 2)) : ℂ) ^ (n + 1) := by
  rw [polynomialMeasure_charFun_eq_eval₂ (n + 1) t,
    polynomialMeasure_charFun_eq_eval₂ n t,
    approximationPolynomial_eval₂_succ]
  have hchoose :
      (n + 1 + 1).choose 2 = (n + 1).choose 2 + (n + 1) := by
    rw [show n + 1 + 1 = (n + 1) + 1 by omega,
      show 2 = 1 + 1 by omega, Nat.choose_succ_succ]
    simp [Nat.add_comm]
  have hnorm :
      ((2 : ℂ) ^ ((n + 1 + 1).choose 2))⁻¹ =
        ((2 : ℂ) ^ ((n + 1).choose 2))⁻¹ *
          ((2 : ℂ) ^ (n + 1))⁻¹ := by
    rw [hchoose, pow_add, mul_inv_rev]
    ring
  have hz :
      Complex.exp (t / (2 : ℝ) ^ (n + 1) * Complex.I) =
        Complex.exp
          (2 * ((t / (2 : ℝ) ^ (n + 2) : ℝ) : ℂ) * Complex.I) := by
    congr 1
    push_cast
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
    field_simp
    rw [pow_succ, pow_succ]
    ring
  have hphase :
      Complex.exp
          (-(t * (approximationDegree (n + 1) : ℝ) /
              (2 : ℝ) ^ (n + 1 + 1)) * Complex.I) =
        Complex.exp
            (-(t * (approximationDegree n : ℝ) /
                (2 : ℝ) ^ (n + 1)) * Complex.I) *
          Complex.exp
            (-((n + 1 : ℂ) *
                ((t / (2 : ℝ) ^ (n + 2) : ℝ) : ℂ)) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    rw [approximationDegree_succ]
    push_cast
    rw [show n + 1 + 1 = n + 2 by omega,
      show n + 2 = (n + 1) + 1 by omega, pow_succ]
    field_simp
    ring
  have hbinomial := centeredBinomialFactor (n + 1)
    (t / (2 : ℝ) ^ (n + 2))
  have hbinomial' :
      ((2 : ℂ) ^ (n + 1))⁻¹ *
          Complex.exp
            (-((n + 1 : ℂ) *
              ((t / (2 : ℝ) ^ (n + 2) : ℝ) : ℂ)) * Complex.I) *
          (1 + Complex.exp
            (2 * ((t / (2 : ℝ) ^ (n + 2) : ℝ) : ℂ) * Complex.I)) ^
            (n + 1) =
        (Real.cos (t / (2 : ℝ) ^ (n + 2)) : ℂ) ^ (n + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hbinomial
  have hscalar :
      ((2 : ℂ) ^ ((n + 1 + 1).choose 2))⁻¹ *
          Complex.exp
            (-(t * (approximationDegree (n + 1) : ℝ) /
                (2 : ℝ) ^ (n + 1 + 1)) * Complex.I) *
          (1 + Complex.exp (t / (2 : ℝ) ^ (n + 1) * Complex.I)) ^
            (n + 1) =
        ((2 : ℂ) ^ ((n + 1).choose 2))⁻¹ *
          Complex.exp
            (-(t * (approximationDegree n : ℝ) /
                (2 : ℝ) ^ (n + 1)) * Complex.I) *
          (Real.cos (t / (2 : ℝ) ^ (n + 2)) : ℂ) ^ (n + 1) := by
    rw [hnorm, hphase, hz]
    calc
      _ = ((2 : ℂ) ^ ((n + 1).choose 2))⁻¹ *
          Complex.exp
            (-(t * (approximationDegree n : ℝ) /
                (2 : ℝ) ^ (n + 1)) * Complex.I) *
          (((2 : ℂ) ^ (n + 1))⁻¹ *
            Complex.exp
              (-((n + 1 : ℂ) *
                ((t / (2 : ℝ) ^ (n + 2) : ℝ) : ℂ)) * Complex.I) *
            (1 + Complex.exp
              (2 * ((t / (2 : ℝ) ^ (n + 2) : ℝ) : ℂ) *
                Complex.I)) ^ (n + 1)) := by ring
      _ = _ := by rw [hbinomial']
  calc
    _ = (((2 : ℂ) ^ ((n + 1 + 1).choose 2))⁻¹ *
          Complex.exp
            (-(t * (approximationDegree (n + 1) : ℝ) /
                (2 : ℝ) ^ (n + 1 + 1)) * Complex.I) *
          (1 + Complex.exp (t / (2 : ℝ) ^ (n + 1) * Complex.I)) ^
            (n + 1)) *
        (approximationPolynomial n).eval₂ (Nat.castRingHom ℂ)
          (Complex.exp (t / (2 : ℝ) ^ n * Complex.I)) := by ring
    _ = _ := by rw [hscalar]; ring

/-- The polynomial measure has the same finite weighted-cosine
characteristic function as the corrected convolution in equation (12). -/
theorem polynomialMeasure_charFun (n : ℕ) (t : ℝ) :
    charFun (polynomialMeasure n) t =
      ∏ k ∈ range n,
        (Real.cos (t / (2 : ℝ) ^ (k + 2)) : ℂ) ^ (k + 1) := by
  induction n with
  | zero =>
      rw [polynomialMeasure_charFun_eq_eval₂]
      simp
  | succ n ih =>
      rw [polynomialMeasure_charFun_succ, ih]
      simp [prod_range_succ]

/-- Characteristic-function form of the algebraic bridge between
equations (12) and (14). -/
theorem polynomialMeasure_charFun_eq_finiteConvolutionMeasure_charFun
    (n : ℕ) :
    charFun (polynomialMeasure n) = charFun (finiteConvolutionMeasure n) := by
  funext t
  rw [polynomialMeasure_charFun, finiteConvolutionMeasure_charFun]

/-- The exact bridge used in Theorem 2: the measure encoded by `p_n` is
the corrected finite Bernoulli convolution `μ_n`. -/
theorem polynomialMeasure_eq_finiteConvolutionMeasure (n : ℕ) :
    polynomialMeasure n = finiteConvolutionMeasure n := by
  apply Measure.ext_of_charFun
  exact polynomialMeasure_charFun_eq_finiteConvolutionMeasure_charFun n

/-- Base case of the bridge: the measure attached to `p_0` is the unit
point mass at `0`. -/
@[simp]
theorem polynomialMeasure_zero :
    polynomialMeasure 0 = Measure.dirac 0 := by
  rw [polynomialMeasure_eq_finiteConvolutionMeasure 0, finiteConvolutionMeasure]

/-- Exact convolution recurrence for the polynomial measures. -/
theorem polynomialMeasure_succ (n : ℕ) :
    polynomialMeasure (n + 1) = polynomialMeasure n ∗
      convolutionPow (centeredBernoulliMeasure (n + 1)) (n + 1) := by
  rw [polynomialMeasure_eq_finiteConvolutionMeasure (n + 1),
    polynomialMeasure_eq_finiteConvolutionMeasure n, finiteConvolutionMeasure]

end

end Fabius
