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

The differentiation itself is branch-free
(`deriv_powerExponentialPhase_hasDerivAt_of_formula`): it uses only the
first-derivative law at and near `x`, together with `x ≠ 0` and the
nonvanishing of `m - beta * lambda(x)`.  Each branch supplies those two
facts from its own side of the turning point.
-/

set_option autoImplicit false

open Filter Set Topology

namespace Fabius

noncomputable section

/-- **Branch-free second derivative.**  If `f` satisfies the
inverse-profile law `f' = f / (x (m - beta f))` at `x` and on a
neighbourhood of `x`, with `x ≠ 0` and `m - beta f x ≠ 0`, then `f'` is
differentiable at `x` with the inverse-profile second derivative. -/
theorem deriv_powerExponentialPhase_hasDerivAt_of_formula
    {m : ℕ} {beta x : ℝ} {f : ℝ → ℝ}
    (hx0 : x ≠ 0) (hd0 : (m : ℝ) - beta * f x ≠ 0)
    (hf : HasDerivAt f (f x / (x * ((m : ℝ) - beta * f x))) x)
    (hderiv : deriv f =ᶠ[𝓝 x]
      fun y : ℝ ↦ f y / (y * ((m : ℝ) - beta * f y))) :
    HasDerivAt (deriv f)
      (f x * ((m : ℝ) - ((m : ℝ) - beta * f x) ^ 2) /
        (x ^ 2 * ((m : ℝ) - beta * f x) ^ 3)) x := by
  let lambda : ℝ := f x
  let delta : ℝ := (m : ℝ) - beta * lambda
  have hdelta0 : delta ≠ 0 := by
    dsimp only [delta, lambda]
    exact hd0
  have hf' : HasDerivAt f (lambda / (x * delta)) x := by
    dsimp only [delta, lambda]
    exact hf
  have hdelta : HasDerivAt (fun y : ℝ ↦ (m : ℝ) - beta * f y)
      (-beta * (lambda / (x * delta))) x := by
    simpa only [neg_mul] using (hf'.const_mul beta).const_sub (m : ℝ)
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
  have hquot := hf'.div hden (mul_ne_zero hx0 hdelta0)
  have hsecond := hquot.congr_of_eventuallyEq hderiv
  have hformula :
      ((lambda / (x * delta)) * (x * delta) -
          lambda * (delta + x * (-beta * (lambda / (x * delta))))) /
            (x * delta) ^ 2 =
        lambda * ((m : ℝ) - delta ^ 2) / (x ^ 2 * delta ^ 3) := by
    dsimp only [delta]
    field_simp [hx0, hdelta0]
    ring
  simpa only [lambda, delta] using hsecond.congr_deriv hformula

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
  have hx0 : x ≠ 0 := hx.1.ne'
  have hdelta_pos : 0 < (m : ℝ) - beta *
      principalPowerExponentialPhase m A beta x := by
    have hturn :=
      principalPowerExponentialPhase_lt_turningPoint hm hA hbeta hx
    have hscaled := (lt_div_iff₀ hbeta).mp hturn
    linarith
  refine deriv_powerExponentialPhase_hasDerivAt_of_formula
    (f := principalPowerExponentialPhase m A beta) hx0 hdelta_pos.ne'
    (principalPowerExponentialPhase_hasDerivAt hm hA hbeta hx) ?_
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  exact deriv_principalPowerExponentialPhase hm hA hbeta hy

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
  have hx0 : x ≠ 0 := hx.1.ne'
  have hdelta_neg : (m : ℝ) - beta *
      lowerPowerExponentialPhase m A beta x < 0 := by
    have hturn :=
      turningPoint_lt_lowerPowerExponentialPhase hm hA hbeta hx
    have hscaled := (div_lt_iff₀ hbeta).mp hturn
    linarith
  refine deriv_powerExponentialPhase_hasDerivAt_of_formula
    (f := lowerPowerExponentialPhase m A beta) hx0 hdelta_neg.ne
    (lowerPowerExponentialPhase_hasDerivAt hm hA hbeta hx) ?_
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  exact deriv_lowerPowerExponentialPhase hm hA hbeta hy

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
