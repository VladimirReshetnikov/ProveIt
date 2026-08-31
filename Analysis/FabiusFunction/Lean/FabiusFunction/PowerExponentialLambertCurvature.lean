import FabiusFunction.PowerExponentialLambertCalculus
import Mathlib.Analysis.Convex.Deriv

/-!
# Curvature of scaled power--exponential Lambert phases

This module differentiates the inverse-profile formula from
`PowerExponentialLambertCalculus.lean` one more time.  If `lambda` is either
smooth inverse branch of

`x = A * lambda ^ m * exp (-beta * lambda)`, then

`lambda''(x) = lambda(x) * (m - (m - beta * lambda(x)) ^ 2) /
  (x ^ 2 * (m - beta * lambda(x)) ^ 3)`.

The formula is valid on the common smooth profile-value interval
`(0, powerExponentialPeak m A beta)`.  It is deliberately stated before any
branch-specific sign analysis: for general `m`, both branches can change
curvature when the squared distance from the turning point equals `m`.
-/

set_option autoImplicit false

open Filter Set Topology

namespace Fabius

noncomputable section

/-- The derivative of the principal scaled Lambert phase is differentiable
on the smooth profile-value interval, with the exact inverse-profile second
derivative. -/
theorem deriv_principalPowerExponentialPhase_hasDerivAt
    {m : ℕ} (hm : m ≠ 0) {A beta x : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta)
    (hx : x ∈ Ioo 0 (powerExponentialPeak m A beta)) :
    HasDerivAt (deriv (principalPowerExponentialPhase m A beta))
      (principalPowerExponentialPhase m A beta x *
        ((m : ℝ) - ((m : ℝ) - beta *
          principalPowerExponentialPhase m A beta x) ^ 2) /
        (x ^ 2 * ((m : ℝ) - beta *
          principalPowerExponentialPhase m A beta x) ^ 3)) x := by
  let f : ℝ → ℝ := principalPowerExponentialPhase m A beta
  let lambda : ℝ := f x
  let delta : ℝ := (m : ℝ) - beta * lambda
  have hx0 : x ≠ 0 := hx.1.ne'
  have hdelta_pos : 0 < delta := by
    have hturn := principalPowerExponentialPhase_lt_turningPoint hm hA hbeta hx
    have hscaled := (lt_div_iff₀ hbeta).mp hturn
    dsimp only [delta, lambda, f]
    linarith
  have hdelta0 : delta ≠ 0 := hdelta_pos.ne'
  have hf : HasDerivAt f (lambda / (x * delta)) x := by
    simpa only [f, lambda, delta] using
      (principalPowerExponentialPhase_hasDerivAt hm hA hbeta hx)
  have hdelta : HasDerivAt (fun y : ℝ ↦ (m : ℝ) - beta * f y)
      (-beta * (lambda / (x * delta))) x := by
    simpa only [neg_mul] using (hf.const_mul beta).const_sub (m : ℝ)
  have hden : HasDerivAt (fun y : ℝ ↦ y * ((m : ℝ) - beta * f y))
      (delta + x * (-beta * (lambda / (x * delta)))) x := by
    have hraw := (hasDerivAt_id' x).mul hdelta
    have hfun : ((fun y : ℝ ↦ y) *
        (fun y : ℝ ↦ (m : ℝ) - beta * f y)) =
        (fun y : ℝ ↦ y * ((m : ℝ) - beta * f y)) := by
      funext y
      rfl
    rw [hfun] at hraw
    simpa only [one_mul, delta, lambda] using hraw
  have hquot := hf.div hden (mul_ne_zero hx0 hdelta0)
  have heq : deriv f =ᶠ[𝓝 x]
      (fun y : ℝ ↦ f y / (y * ((m : ℝ) - beta * f y))) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact deriv_principalPowerExponentialPhase hm hA hbeta hy
  have hsecond := hquot.congr_of_eventuallyEq heq
  have hformula :
      ((lambda / (x * delta)) * (x * delta) -
          lambda * (delta + x * (-beta * (lambda / (x * delta))))) /
            (x * delta) ^ 2 =
        lambda * ((m : ℝ) - delta ^ 2) / (x ^ 2 * delta ^ 3) := by
    dsimp only [delta]
    field_simp [hx0, hdelta0]
    ring
  simpa only [f, lambda, delta] using hsecond.congr_deriv hformula

/-- Exact second derivative of the principal scaled Lambert phase on the
smooth profile-value interval. -/
theorem deriv_deriv_principalPowerExponentialPhase
    {m : ℕ} (hm : m ≠ 0) {A beta x : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta)
    (hx : x ∈ Ioo 0 (powerExponentialPeak m A beta)) :
    deriv (deriv (principalPowerExponentialPhase m A beta)) x =
      principalPowerExponentialPhase m A beta x *
        ((m : ℝ) - ((m : ℝ) - beta *
          principalPowerExponentialPhase m A beta x) ^ 2) /
        (x ^ 2 * ((m : ℝ) - beta *
          principalPowerExponentialPhase m A beta x) ^ 3) :=
  (deriv_principalPowerExponentialPhase_hasDerivAt hm hA hbeta hx).deriv

/-- The derivative of the lower scaled Lambert phase is differentiable on
the smooth profile-value interval, with the same algebraic inverse-profile
second derivative. -/
theorem deriv_lowerPowerExponentialPhase_hasDerivAt
    {m : ℕ} (hm : m ≠ 0) {A beta x : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta)
    (hx : x ∈ Ioo 0 (powerExponentialPeak m A beta)) :
    HasDerivAt (deriv (lowerPowerExponentialPhase m A beta))
      (lowerPowerExponentialPhase m A beta x *
        ((m : ℝ) - ((m : ℝ) - beta *
          lowerPowerExponentialPhase m A beta x) ^ 2) /
        (x ^ 2 * ((m : ℝ) - beta *
          lowerPowerExponentialPhase m A beta x) ^ 3)) x := by
  let f : ℝ → ℝ := lowerPowerExponentialPhase m A beta
  let lambda : ℝ := f x
  let delta : ℝ := (m : ℝ) - beta * lambda
  have hx0 : x ≠ 0 := hx.1.ne'
  have hdelta_neg : delta < 0 := by
    have hturn := turningPoint_lt_lowerPowerExponentialPhase hm hA hbeta hx
    have hscaled := (div_lt_iff₀ hbeta).mp hturn
    dsimp only [delta, lambda, f]
    linarith
  have hdelta0 : delta ≠ 0 := hdelta_neg.ne
  have hf : HasDerivAt f (lambda / (x * delta)) x := by
    simpa only [f, lambda, delta] using
      (lowerPowerExponentialPhase_hasDerivAt hm hA hbeta hx)
  have hdelta : HasDerivAt (fun y : ℝ ↦ (m : ℝ) - beta * f y)
      (-beta * (lambda / (x * delta))) x := by
    simpa only [neg_mul] using (hf.const_mul beta).const_sub (m : ℝ)
  have hden : HasDerivAt (fun y : ℝ ↦ y * ((m : ℝ) - beta * f y))
      (delta + x * (-beta * (lambda / (x * delta)))) x := by
    have hraw := (hasDerivAt_id' x).mul hdelta
    have hfun : ((fun y : ℝ ↦ y) *
        (fun y : ℝ ↦ (m : ℝ) - beta * f y)) =
        (fun y : ℝ ↦ y * ((m : ℝ) - beta * f y)) := by
      funext y
      rfl
    rw [hfun] at hraw
    simpa only [one_mul, delta, lambda] using hraw
  have hquot := hf.div hden (mul_ne_zero hx0 hdelta0)
  have heq : deriv f =ᶠ[𝓝 x]
      (fun y : ℝ ↦ f y / (y * ((m : ℝ) - beta * f y))) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact deriv_lowerPowerExponentialPhase hm hA hbeta hy
  have hsecond := hquot.congr_of_eventuallyEq heq
  have hformula :
      ((lambda / (x * delta)) * (x * delta) -
          lambda * (delta + x * (-beta * (lambda / (x * delta))))) /
            (x * delta) ^ 2 =
        lambda * ((m : ℝ) - delta ^ 2) / (x ^ 2 * delta ^ 3) := by
    dsimp only [delta]
    field_simp [hx0, hdelta0]
    ring
  simpa only [f, lambda, delta] using hsecond.congr_deriv hformula

/-- Exact second derivative of the lower scaled Lambert phase on the smooth
profile-value interval. -/
theorem deriv_deriv_lowerPowerExponentialPhase
    {m : ℕ} (hm : m ≠ 0) {A beta x : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta)
    (hx : x ∈ Ioo 0 (powerExponentialPeak m A beta)) :
    deriv (deriv (lowerPowerExponentialPhase m A beta)) x =
      lowerPowerExponentialPhase m A beta x *
        ((m : ℝ) - ((m : ℝ) - beta *
          lowerPowerExponentialPhase m A beta x) ^ 2) /
        (x ^ 2 * ((m : ℝ) - beta *
          lowerPowerExponentialPhase m A beta x) ^ 3) :=
  (deriv_lowerPowerExponentialPhase_hasDerivAt hm hA hbeta hx).deriv

end

end Fabius
