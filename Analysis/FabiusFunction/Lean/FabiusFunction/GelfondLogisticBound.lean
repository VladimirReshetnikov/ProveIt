import FabiusFunction.LacunaryRieszIntegral

/-!
# The Gelfond bound via a logistic-orbit telescope

The sharp exponential rate of the sup-norm of dyadic sine products —
the constant behind the extremal exponent `κ∞` of the Fourier-decay
audit — is governed by a single algebraic inequality for the full
logistic map `v ↦ 4v(1-v)`.  This file formalizes that mechanism in a
form more general than the sine products themselves: the bound holds
along **every** orbit of the logistic map, and the sine products enter
only because squared sines at doubling angles form such orbits.

* `logistic_prod_le` — along any orbit `u (j+1) = 4·u j·(1 - u j)` in
  `[0,1]`, the running product satisfies
  `∏_{j<n} u j ≤ (5/3)·(3/4)ⁿ`.  The proof telescopes the potential
  `V v = 1 + 2v/3` through the exact identity
  `3·V v - 4v·V (4v(1-v)) = (2v+1)(4v-3)²/3 ≥ 0`
  (Document 2's subaction, audited in the comparative audit).
* `prod_sin_sq_two_pow_le` — the **Gelfond bound**
  `∏_{j<n} sin (π 2ʲ t)² ≤ (5/3)·(3/4)ⁿ` for every real `t`.
* `prod_sin_sq_two_pow_third` — **sharpness**: at `t = 1/3` every
  factor equals `3/4`, so the product is exactly `(3/4)ⁿ`; the binary
  cycle `1/3 ↔ 2/3` realizes the extremal rate.
* `abs_prod_sin_two_pow_le` — the unsquared form
  `∏_{j<n} |sin (π 2ʲ t)| ≤ √(5/3)·(√3/2)ⁿ`.
* `le_mul_integral_prod_abs_sin_two_pow` — combining the Gelfond bound
  with the exact `L²` identity of `LacunaryRieszIntegral`:
  `(1/2)ⁿ ≤ √(5/3)·(√3/2)ⁿ · ∫ t in 0..1, ∏_{j<n} |sin (π 2ʲ t)|`,
  i.e. the mean of the sine product is at least `√(3/5)·3^{-n/2}`.
  This is the elementary lower bracket `ϱ₁ ≥ 3^{-1/2} > 1/2` used by
  the audit to prove that the transfer-operator eigenmeasure is
  singular (impossibility of the exact Cesàro limit).
-/

set_option autoImplicit false

open Finset intervalIntegral Real

namespace Fabius

/-- The subaction step: for `v ∈ [0,1]`,
`4v·(1 + 2·(4v(1-v))/3) ≤ 3·(1 + 2v/3)`, by the exact identity
`3·V v - 4v·V (4v(1-v)) = (2v+1)(4v-3)²/3`. -/
theorem logistic_subaction_step (v : ℝ) (h0 : 0 ≤ v) :
    4 * v * (1 + 2 * (4 * v * (1 - v)) / 3) ≤ 3 * (1 + 2 * v / 3) := by
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 * v + 1) (sq_nonneg (4 * v - 3)),
    sq_nonneg (4 * v - 3)]

/-- Telescoped form: along a logistic orbit, the weighted running
product is controlled at every step. -/
theorem logistic_prod_mul_le (u : ℕ → ℝ) (h0 : ∀ j, 0 ≤ u j)
    (hrec : ∀ j, u (j + 1) = 4 * u j * (1 - u j)) :
    ∀ n : ℕ, (∏ j ∈ range n, u j) * (1 + 2 * u n / 3) ≤
      (3 / 4 : ℝ) ^ n * (1 + 2 * u 0 / 3) := by
  intro n
  induction n with
  | zero => simp
  | succ n ihn =>
      have hstep : u n * (1 + 2 * u (n + 1) / 3) ≤
          (3 / 4) * (1 + 2 * u n / 3) := by
        have h := logistic_subaction_step (u n) (h0 n)
        rw [hrec n]
        linarith
      have hprod0 : 0 ≤ ∏ j ∈ range n, u j :=
        Finset.prod_nonneg fun j _ => h0 j
      calc (∏ j ∈ range (n + 1), u j) * (1 + 2 * u (n + 1) / 3)
          = (∏ j ∈ range n, u j) * (u n * (1 + 2 * u (n + 1) / 3)) := by
            rw [Finset.prod_range_succ]; ring
        _ ≤ (∏ j ∈ range n, u j) * ((3 / 4) * (1 + 2 * u n / 3)) :=
            mul_le_mul_of_nonneg_left hstep hprod0
        _ = (3 / 4) * ((∏ j ∈ range n, u j) * (1 + 2 * u n / 3)) := by ring
        _ ≤ (3 / 4) * ((3 / 4 : ℝ) ^ n * (1 + 2 * u 0 / 3)) := by
            have h34 : (0:ℝ) ≤ 3 / 4 := by norm_num
            exact mul_le_mul_of_nonneg_left ihn h34
        _ = (3 / 4 : ℝ) ^ (n + 1) * (1 + 2 * u 0 / 3) := by ring

/-- **Logistic-orbit product bound**: along any orbit of the full
logistic map `v ↦ 4v(1-v)` in `[0,1]`,
`∏_{j<n} u j ≤ (5/3)·(3/4)ⁿ`. -/
theorem logistic_prod_le (u : ℕ → ℝ) (h0 : ∀ j, 0 ≤ u j) (h1 : ∀ j, u j ≤ 1)
    (hrec : ∀ j, u (j + 1) = 4 * u j * (1 - u j)) (n : ℕ) :
    ∏ j ∈ range n, u j ≤ 5 / 3 * (3 / 4 : ℝ) ^ n := by
  have hprod0 : 0 ≤ ∏ j ∈ range n, u j := Finset.prod_nonneg fun j _ => h0 j
  have hV : (1:ℝ) ≤ 1 + 2 * u n / 3 := by have := h0 n; linarith
  have h := logistic_prod_mul_le u h0 hrec n
  have hup : (∏ j ∈ range n, u j) ≤
      (∏ j ∈ range n, u j) * (1 + 2 * u n / 3) := by
    nlinarith
  have hV0 : 1 + 2 * u 0 / 3 ≤ 5 / 3 := by have := h1 0; linarith
  have hpow : (0:ℝ) ≤ (3 / 4 : ℝ) ^ n := by positivity
  nlinarith

/-- Squared sines at doubling angles form a logistic orbit:
`sin (2x)² = 4·sin x²·(1 - sin x²)`. -/
theorem sin_sq_two_mul (x : ℝ) :
    Real.sin (2 * x) ^ 2 = 4 * Real.sin x ^ 2 * (1 - Real.sin x ^ 2) := by
  rw [Real.sin_two_mul]
  have h := Real.sin_sq_add_cos_sq x
  nlinarith [h]

/-- **The Gelfond bound**, squared form: for every real `t`,
`∏_{j<n} sin (π 2ʲ t)² ≤ (5/3)·(3/4)ⁿ`.  This is the sup-norm rate of
the dyadic sine product; it forces the extremal power `κ∞` of the
Fourier-decay spectrum. -/
theorem prod_sin_sq_two_pow_le (t : ℝ) (n : ℕ) :
    ∏ j ∈ range n, Real.sin (π * 2 ^ j * t) ^ 2 ≤ 5 / 3 * (3 / 4 : ℝ) ^ n := by
  refine logistic_prod_le (fun j => Real.sin (π * 2 ^ j * t) ^ 2)
    (fun j => sq_nonneg _) (fun j => Real.sin_sq_le_one _) (fun j => ?_) n
  have harg : π * 2 ^ (j + 1) * t = 2 * (π * 2 ^ j * t) := by ring
  rw [harg, sin_sq_two_mul]

/-- **Sharpness of the Gelfond bound**: every factor of the dyadic sine
product at `t = 1/3` equals `3/4`. -/
theorem sin_sq_two_pow_third (j : ℕ) :
    Real.sin (π * 2 ^ j * (1 / 3 : ℝ)) ^ 2 = 3 / 4 := by
  induction j with
  | zero =>
      have harg : π * 2 ^ 0 * (1 / 3 : ℝ) = π / 3 := by ring
      rw [harg, Real.sin_pi_div_three]
      rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
      norm_num
  | succ j ihj =>
      have harg : π * 2 ^ (j + 1) * (1 / 3 : ℝ) =
          2 * (π * 2 ^ j * (1 / 3 : ℝ)) := by ring
      rw [harg, sin_sq_two_mul, ihj]
      norm_num

/-- At `t = 1/3` the dyadic sine product attains the Gelfond rate
exactly: `∏_{j<n} sin (π 2ʲ/3)² = (3/4)ⁿ`. -/
theorem prod_sin_sq_two_pow_third (n : ℕ) :
    ∏ j ∈ range n, Real.sin (π * 2 ^ j * (1 / 3 : ℝ)) ^ 2 = (3 / 4 : ℝ) ^ n := by
  rw [Finset.prod_congr rfl fun j _ => sin_sq_two_pow_third j,
    Finset.prod_const, Finset.card_range]

/-- The Gelfond bound, unsquared form:
`∏_{j<n} |sin (π 2ʲ t)| ≤ √(5/3)·(√3/2)ⁿ`. -/
theorem abs_prod_sin_two_pow_le (t : ℝ) (n : ℕ) :
    ∏ j ∈ range n, |Real.sin (π * 2 ^ j * t)| ≤
      Real.sqrt (5 / 3) * (Real.sqrt 3 / 2) ^ n := by
  set A : ℝ := ∏ j ∈ range n, |Real.sin (π * 2 ^ j * t)| with hA
  have hA0 : 0 ≤ A := Finset.prod_nonneg fun j _ => abs_nonneg _
  have hAsq : A ^ 2 = ∏ j ∈ range n, Real.sin (π * 2 ^ j * t) ^ 2 := by
    rw [hA, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun j _ => sq_abs _
  set B : ℝ := Real.sqrt (5 / 3) * (Real.sqrt 3 / 2) ^ n with hB
  have hB0 : 0 ≤ B := by positivity
  have hBsq : B ^ 2 = 5 / 3 * (3 / 4 : ℝ) ^ n := by
    rw [hB, mul_pow, ← pow_mul, mul_comm n 2, pow_mul, div_pow,
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5 / 3),
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    norm_num
  have hle : A ^ 2 ≤ B ^ 2 := by
    rw [hAsq, hBsq]
    exact prod_sin_sq_two_pow_le t n
  calc A = Real.sqrt (A ^ 2) := (Real.sqrt_sq hA0).symm
    _ ≤ Real.sqrt (B ^ 2) := Real.sqrt_le_sqrt hle
    _ = B := Real.sqrt_sq hB0

/-- **Lower bracket for the mean of the dyadic sine product.**
Combining the exact `L²` identity `∫ ∏ sin² = (1/2)ⁿ` with the Gelfond
sup bound gives
`(1/2)ⁿ ≤ √(5/3)·(√3/2)ⁿ · ∫ t in 0..1, ∏_{j<n} |sin (π 2ʲ t)|`.
Equivalently, `I₁(n) ≥ √(3/5)·3^{-n/2}`: the per-level `L¹` rate of
the sine product is at least `3^{-1/2} > 1/2`.  This is the fully
elementary input that makes the transfer-operator eigenmeasure of the
decay audit singular. -/
theorem le_mul_integral_prod_abs_sin_two_pow (n : ℕ) :
    (1 / 2 : ℝ) ^ n ≤ (Real.sqrt (5 / 3) * (Real.sqrt 3 / 2) ^ n) *
      ∫ t in (0:ℝ)..1, ∏ j ∈ range n, |Real.sin (π * 2 ^ j * t)| := by
  set B : ℝ := Real.sqrt (5 / 3) * (Real.sqrt 3 / 2) ^ n with hB
  have hB0 : 0 ≤ B := by positivity
  have hQcont : Continuous fun t : ℝ =>
      ∏ j ∈ range n, |Real.sin (π * 2 ^ j * t)| := by
    refine continuous_finsetProd _ fun j _ => ?_
    fun_prop
  have hQsqcont : Continuous fun t : ℝ =>
      ∏ j ∈ range n, Real.sin (π * 2 ^ j * t) ^ 2 := by
    refine continuous_finsetProd _ fun j _ => ?_
    fun_prop
  have hpoint : ∀ t ∈ Set.Icc (0:ℝ) 1,
      ∏ j ∈ range n, Real.sin (π * 2 ^ j * t) ^ 2 ≤
        B * ∏ j ∈ range n, |Real.sin (π * 2 ^ j * t)| := by
    intro t _
    have hQ0 : 0 ≤ ∏ j ∈ range n, |Real.sin (π * 2 ^ j * t)| :=
      Finset.prod_nonneg fun j _ => abs_nonneg _
    have hQle : ∏ j ∈ range n, |Real.sin (π * 2 ^ j * t)| ≤ B :=
      abs_prod_sin_two_pow_le t n
    have hsq : ∏ j ∈ range n, Real.sin (π * 2 ^ j * t) ^ 2 =
        (∏ j ∈ range n, |Real.sin (π * 2 ^ j * t)|) ^ 2 := by
      rw [← Finset.prod_pow]
      exact Finset.prod_congr rfl fun j _ => (sq_abs _).symm
    rw [hsq, sq]
    exact mul_le_mul_of_nonneg_right hQle hQ0
  have hgcont : Continuous fun t : ℝ =>
      B * ∏ j ∈ range n, |Real.sin (π * 2 ^ j * t)| := hQcont.const_mul B
  have hmono := intervalIntegral.integral_mono_on
    (μ := MeasureTheory.volume) (by norm_num : (0:ℝ) ≤ 1)
    (hQsqcont.intervalIntegrable 0 1)
    (hgcont.intervalIntegrable 0 1) hpoint
  rw [intervalIntegral.integral_const_mul] at hmono
  calc (1 / 2 : ℝ) ^ n
      = ∫ t in (0:ℝ)..1, ∏ j ∈ range n, Real.sin (π * 2 ^ j * t) ^ 2 :=
        (integral_prod_sin_sq_two_pow n).symm
    _ ≤ B * ∫ t in (0:ℝ)..1, ∏ j ∈ range n, |Real.sin (π * 2 ^ j * t)| := hmono

end Fabius
