import FabiusFunction.SaddleExpansionAlgebra
import FabiusFunction.QuantitativeSaddle
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Gaussian moments and polynomial contraction

This module identifies normalized integration against the standard Gaussian
with a linear functional on complex polynomials.  It also records the basic
integrability and pointwise coefficient estimates reused by the Gaussian-tail
modules.
-/

set_option autoImplicit false

open scoped BigOperators Nat
open Filter MeasureTheory

namespace Fabius.SaddleExpansion

noncomputable section

/-- The `n`-th unnormalized moment of the standard real Gaussian kernel. -/
def realGaussianMoment (n : ℕ) : ℝ :=
  ∫ v : ℝ, Real.exp (-(v ^ 2) / 2) * v ^ n

/-- Every polynomial moment of the standard real Gaussian kernel is integrable. -/
theorem integrable_realGaussian_mul_pow (n : ℕ) :
    Integrable (fun v : ℝ => Real.exp (-(v ^ 2) / 2) * v ^ n) := by
  have hs : (-1 : ℝ) < (n : ℝ) := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h := integrable_rpow_mul_exp_neg_mul_sq
    (b := (1 / 2 : ℝ)) (s := (n : ℝ)) (by norm_num) hs
  convert h using 1
  funext v
  rw [Real.rpow_natCast]
  ring_nf

/-- Absolute polynomial moments of the standard real Gaussian kernel are
integrable. -/
theorem integrable_realGaussian_mul_abs_pow (n : ℕ) :
    Integrable (fun v : ℝ => Real.exp (-(v ^ 2) / 2) * |v| ^ n) := by
  have h := (integrable_realGaussian_mul_pow n).norm
  apply h.congr
  filter_upwards with v
  rw [Real.norm_eq_abs, abs_mul, abs_pow,
    abs_of_pos (Real.exp_pos _)]

/-- The norm of the complex-valued standard Gaussian is its real Gaussian
kernel. -/
theorem norm_standardGaussian (v : ℝ) :
    ‖QuantitativeSaddle.standardGaussian v‖ =
      Real.exp (-(v ^ 2) / 2) := by
  rw [QuantitativeSaddle.standardGaussian, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

theorem realGaussianMoment_zero :
    realGaussianMoment 0 = Real.sqrt (2 * Real.pi) := by
  unfold realGaussianMoment
  simp only [pow_zero, mul_one]
  have h := integral_gaussian (1 / 2 : ℝ)
  convert h using 1
  · apply integral_congr_ae
    filter_upwards with x
    congr 1
    ring
  · congr 1
    ring

theorem realGaussianMoment_odd (j : ℕ) :
    realGaussianMoment (2 * j + 1) = 0 := by
  apply neg_eq_self.mp
  have hinvariant := integral_neg_eq_self
    (fun v : ℝ => Real.exp (-(v ^ 2) / 2) * v ^ (2 * j + 1)) volume
  have hfun :
      (fun v : ℝ => Real.exp (-((-v) ^ 2) / 2) * (-v) ^ (2 * j + 1)) =
        -(fun v : ℝ => Real.exp (-(v ^ 2) / 2) * v ^ (2 * j + 1)) := by
    funext v
    rw [neg_sq, neg_pow]
    rw [show (-1 : ℝ) ^ (2 * j + 1) = -1 by
      rw [pow_add, pow_mul]
      norm_num]
    simp only [Pi.neg_apply]
    ring
  rw [hfun, integral_neg'] at hinvariant
  simpa only [realGaussianMoment] using hinvariant

theorem realGaussianMoment_add_two (n : ℕ) :
    realGaussianMoment (n + 2) = (n + 1 : ℝ) * realGaussianMoment n := by
  let u : ℝ → ℝ := fun x => x ^ (n + 1)
  let u' : ℝ → ℝ := fun x => (n + 1 : ℝ) * x ^ n
  let v : ℝ → ℝ := fun x => Real.exp (-(x ^ 2) / 2)
  let v' : ℝ → ℝ := fun x => -x * Real.exp (-(x ^ 2) / 2)
  have hu (x : ℝ) : HasDerivAt u (u' x) x := by
    simpa only [u, u', Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] using
      hasDerivAt_pow (n + 1) x
  have hv (x : ℝ) : HasDerivAt v (v' x) x := by
    have hinner : HasDerivAt (fun y : ℝ => -(y ^ 2) / 2) (-x) x := by
      convert! ((hasDerivAt_pow 2 x).neg.div_const 2) using 1
      all_goals ring_nf
    convert! (Real.hasDerivAt_exp (-(x ^ 2) / 2)).comp x hinner using 1
    dsimp [v']
    rw [neg_mul]
    ring
  have huv' : Integrable (u * v') := by
    have h := (integrable_realGaussian_mul_pow (n + 2)).neg
    apply h.congr
    filter_upwards with x
    dsimp [u, v']
    ring
  have hu'v : Integrable (u' * v) := by
    have h := (integrable_realGaussian_mul_pow n).const_mul (n + 1 : ℝ)
    apply h.congr
    filter_upwards with x
    dsimp [u', v]
    ring
  have huv : Integrable (u * v) := by
    have h := integrable_realGaussian_mul_pow (n + 1)
    apply h.congr
    filter_upwards with x
    dsimp [u, v]
    ring
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := u) (u' := u') (v := v) (v' := v')
    (fun x _ => hu x) (fun x _ => hv x) huv' hu'v huv
  have hleft : (∫ x : ℝ, u x * v' x) =
      -realGaussianMoment (n + 2) := by
    rw [realGaussianMoment, ← integral_neg]
    apply integral_congr_ae
    filter_upwards with x
    dsimp [u, v']
    ring
  have hright : (∫ x : ℝ, u' x * v x) =
      (n + 1 : ℝ) * realGaussianMoment n := by
    rw [realGaussianMoment, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    dsimp [u', v]
    ring
  rw [hleft, hright] at hibp
  linarith

/-- The normalized moments of the standard Gaussian.  This recurrence is a
computable version of Gaussian integration by parts. -/
def normalizedGaussianMoment : ℕ → ℂ
  | 0 => 1
  | 1 => 0
  | n + 2 => (n + 1 : ℂ) * normalizedGaussianMoment n

@[simp] theorem normalizedGaussianMoment_zero :
    normalizedGaussianMoment 0 = 1 := rfl

@[simp] theorem normalizedGaussianMoment_one :
    normalizedGaussianMoment 1 = 0 := rfl

@[simp] theorem normalizedGaussianMoment_add_two (n : ℕ) :
    normalizedGaussianMoment (n + 2) =
      (n + 1 : ℂ) * normalizedGaussianMoment n := rfl

@[simp] theorem normalizedGaussianMoment_odd (j : ℕ) :
    normalizedGaussianMoment (2 * j + 1) = 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by omega,
        normalizedGaussianMoment_add_two, ih, mul_zero]

@[simp] theorem normalizedGaussianMoment_even (j : ℕ) :
    normalizedGaussianMoment (2 * j) =
      (Nat.doubleFactorial (2 * j - 1) : ℂ) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [show 2 * (j + 1) = 2 * j + 2 by omega,
        normalizedGaussianMoment_add_two, ih]
      exact_mod_cast (Nat.doubleFactorial_add_one (2 * j)).symm

theorem realGaussianMoment_eq_normalizedGaussianMoment (n : ℕ) :
    (realGaussianMoment n : ℂ) =
      (Real.sqrt (2 * Real.pi) : ℂ) * normalizedGaussianMoment n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [realGaussianMoment_zero]
  | one =>
      simp only [normalizedGaussianMoment_one, mul_zero]
      exact_mod_cast realGaussianMoment_odd 0
  | more n hn _ =>
      rw [realGaussianMoment_add_two, normalizedGaussianMoment_add_two]
      push_cast
      rw [hn]
      ring

theorem normalizedGaussianMoment_conj (n : ℕ) :
    star (normalizedGaussianMoment n) = normalizedGaussianMoment n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n hn _ =>
      have hc : star (n + 1 : ℂ) = (n + 1 : ℂ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          (star_natCast (R := ℂ) (n + 1))
      rw [normalizedGaussianMoment_add_two, star_mul, hc, hn]
      ring

private def monomialGaussianContraction (n : ℕ) : ℂ →ₗ[ℂ] ℂ where
  toFun c := c * normalizedGaussianMoment n
  map_add' a b := by ring
  map_smul' a b := by simp [smul_eq_mul]; ring

/-- Algebraic normalized Gaussian integration on complex polynomials. -/
noncomputable def gaussianPolynomialContraction : Polynomial ℂ →ₗ[ℂ] ℂ :=
  Polynomial.lsum monomialGaussianContraction

/-- Coefficientwise complex conjugation of a polynomial. -/
def conjugatePolynomial (p : Polynomial ℂ) : Polynomial ℂ :=
  p.map (starRingEnd ℂ)

@[simp] theorem gaussianPolynomialContraction_monomial (n : ℕ) (c : ℂ) :
    gaussianPolynomialContraction (Polynomial.monomial n c) =
      c * normalizedGaussianMoment n := by
  simp [gaussianPolynomialContraction, monomialGaussianContraction]

@[simp] theorem gaussianPolynomialContraction_C (c : ℂ) :
    gaussianPolynomialContraction (Polynomial.C c) = c := by
  rw [← Polynomial.monomial_zero_left,
    gaussianPolynomialContraction_monomial, normalizedGaussianMoment_zero, mul_one]

@[simp] theorem gaussianPolynomialContraction_X_pow (n : ℕ) :
    gaussianPolynomialContraction (Polynomial.X ^ n) =
      normalizedGaussianMoment n := by
  rw [← Polynomial.monomial_one_right_eq_X_pow,
    gaussianPolynomialContraction_monomial, one_mul]

@[simp] theorem gaussianPolynomialContraction_X_pow_odd (j : ℕ) :
    gaussianPolynomialContraction (Polynomial.X ^ (2 * j + 1)) = 0 := by
  simp

@[simp] theorem gaussianPolynomialContraction_X_pow_even (j : ℕ) :
    gaussianPolynomialContraction (Polynomial.X ^ (2 * j)) =
      (Nat.doubleFactorial (2 * j - 1) : ℂ) := by
  simp

theorem integrable_standardGaussian_mul_pow (n : ℕ) :
    Integrable (fun x : ℝ =>
      QuantitativeSaddle.standardGaussian x * (x : ℂ) ^ n) := by
  have h : Integrable (fun x : ℝ =>
      ((Real.exp (-(x ^ 2) / 2) * x ^ n : ℝ) : ℂ)) :=
    (integrable_realGaussian_mul_pow n).ofReal
  apply h.congr
  filter_upwards with x
  simp only [QuantitativeSaddle.standardGaussian, Complex.ofReal_mul,
    Complex.ofReal_pow]

theorem integrable_standardGaussian_mul_eval (p : Polynomial ℂ) :
    Integrable (fun x : ℝ =>
      QuantitativeSaddle.standardGaussian x * p.eval (x : ℂ)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      apply hp.add hq |>.congr
      filter_upwards with x
      simp only [Pi.add_apply, Polynomial.eval_add]
      ring
  | monomial n c =>
      apply (integrable_standardGaussian_mul_pow n).mul_const c |>.congr
      filter_upwards with x
      simp only [Polynomial.eval_monomial]
      ring

/-- Pointwise coefficient bound for a polynomial multiplied by the standard
Gaussian. -/
theorem norm_standardGaussian_mul_eval_le (p : Polynomial ℂ) (v : ℝ) :
    ‖QuantitativeSaddle.standardGaussian v * p.eval (v : ℂ)‖ ≤
      ∑ k ∈ p.support,
        ‖p.coeff k‖ * (Real.exp (-(v ^ 2) / 2) * |v| ^ k) := by
  rw [norm_mul, norm_standardGaussian, Polynomial.eval_eq_sum]
  calc
    Real.exp (-(v ^ 2) / 2) *
        ‖p.sum fun k c => c * (v : ℂ) ^ k‖ ≤
      Real.exp (-(v ^ 2) / 2) *
        ∑ k ∈ p.support, ‖p.coeff k * (v : ℂ) ^ k‖ := by
          gcongr
          exact norm_sum_le _ _
    _ = ∑ k ∈ p.support,
        ‖p.coeff k‖ * (Real.exp (-(v ^ 2) / 2) * |v| ^ k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      simp only [norm_mul, norm_pow, Complex.norm_real,
        Real.norm_eq_abs]
      ring

theorem integral_standardGaussian_mul_pow (n : ℕ) :
    (∫ x : ℝ, QuantitativeSaddle.standardGaussian x * (x : ℂ) ^ n) =
      (Real.sqrt (2 * Real.pi) : ℂ) * normalizedGaussianMoment n := by
  rw [← realGaussianMoment_eq_normalizedGaussianMoment]
  calc
    (∫ x : ℝ, QuantitativeSaddle.standardGaussian x * (x : ℂ) ^ n) =
        ∫ x : ℝ, ((Real.exp (-(x ^ 2) / 2) * x ^ n : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [QuantitativeSaddle.standardGaussian, Complex.ofReal_mul,
        Complex.ofReal_pow]
    _ = Complex.ofReal (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ n) :=
      integral_ofReal
    _ = (realGaussianMoment n : ℂ) := by
      rfl

theorem integral_standardGaussian_mul_eval (p : Polynomial ℂ) :
    (∫ x : ℝ, QuantitativeSaddle.standardGaussian x * p.eval (x : ℂ)) =
      (Real.sqrt (2 * Real.pi) : ℂ) * gaussianPolynomialContraction p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, mul_add, ← hp, ← hq]
      rw [← integral_add (integrable_standardGaussian_mul_eval p)
        (integrable_standardGaussian_mul_eval q)]
      apply integral_congr_ae
      filter_upwards with x
      simp only [Polynomial.eval_add]
      ring
  | monomial n c =>
      rw [gaussianPolynomialContraction_monomial]
      calc
        (∫ x : ℝ, QuantitativeSaddle.standardGaussian x *
            (Polynomial.monomial n c).eval (x : ℂ)) =
            ∫ x : ℝ,
              (QuantitativeSaddle.standardGaussian x * (x : ℂ) ^ n) * c := by
          apply integral_congr_ae
          filter_upwards with x
          simp only [Polynomial.eval_monomial]
          ring
        _ = (∫ x : ℝ,
              QuantitativeSaddle.standardGaussian x * (x : ℂ) ^ n) * c :=
          integral_mul_const c (fun x : ℝ =>
            QuantitativeSaddle.standardGaussian x * (x : ℂ) ^ n)
        _ = ((Real.sqrt (2 * Real.pi) : ℂ) * normalizedGaussianMoment n) * c := by
          rw [integral_standardGaussian_mul_pow]
        _ = (Real.sqrt (2 * Real.pi) : ℂ) *
            (c * normalizedGaussianMoment n) := by ring

/-- The algebraic contraction agrees with normalized Bochner integration
against the standard Gaussian on the real line. -/
theorem gaussianPolynomialContraction_eq_integral (p : Polynomial ℂ) :
    gaussianPolynomialContraction p =
      (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ *
        ∫ x : ℝ, QuantitativeSaddle.standardGaussian x * p.eval (x : ℂ) := by
  rw [integral_standardGaussian_mul_eval]
  have hsqrt : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (mul_pos (by norm_num) Real.pi_pos)).ne'
  symm
  calc
    _ = ((Real.sqrt (2 * Real.pi) : ℂ)⁻¹ *
        (Real.sqrt (2 * Real.pi) : ℂ)) * gaussianPolynomialContraction p := by
      rw [mul_assoc]
    _ = gaussianPolynomialContraction p := by rw [inv_mul_cancel₀ hsqrt, one_mul]

theorem gaussianPolynomialContraction_conjugate (p : Polynomial ℂ) :
    star (gaussianPolynomialContraction p) =
      gaussianPolynomialContraction (conjugatePolynomial p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, star_add, hp, hq]
      simp only [conjugatePolynomial, Polynomial.map_add, map_add]
  | monomial n c =>
      rw [gaussianPolynomialContraction_monomial, star_mul,
        normalizedGaussianMoment_conj]
      simp only [conjugatePolynomial, Polynomial.map_monomial,
        starRingEnd_apply, gaussianPolynomialContraction_monomial]
      ring

theorem gaussianPolynomialContraction_star_eq_self
    {p : Polynomial ℂ} (hp : conjugatePolynomial p = p) :
    star (gaussianPolynomialContraction p) = gaussianPolynomialContraction p := by
  rw [gaussianPolynomialContraction_conjugate, hp]

end

end Fabius.SaddleExpansion
