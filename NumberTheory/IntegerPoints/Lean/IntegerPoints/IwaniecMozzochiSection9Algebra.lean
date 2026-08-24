import IntegerPoints.GKLemma33
import IntegerPoints.IwaniecMozzochi

/-!
# Algebraic normalizations for Iwaniec--Mozzochi Section 9

This file records the exact algebra behind the approximate modular relation
(9.6).  It deliberately does **not** assert the analytic estimate (9.7).

The two potentially delicate normalizations are:

* completing the square in the Fourier integral produced by Poisson
  summation; and
* identifying the paper's factor `(i / (2 beta))^(1/2)` with the Fresnel
  normalization already proved in `GKLemma33`.

Keeping these identities separate leaves the future proof of (9.6)/(9.7)
with an explicit analytic obligation: estimate the translated-amplitude
remainder uniformly and then sum it over one congruence class.
-/

open Real

namespace LeanProofs.IntegerPoints

/-- The complex square root in (9.6) is exactly the normalization used by
the proved Graham--Kolesnik Fresnel estimate.  Both powers use Mathlib's
principal branch. -/
theorem section9_fresnelConstant_eq {beta : ℝ} (hbeta : 0 < beta) :
    (Complex.I / (2 * beta)) ^ ((1 : ℂ) / 2) =
      e (1 / 8) / ((Real.sqrt (2 * beta) : ℝ) : ℂ) := by
  rw [← GK33.limit_value hbeta]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hbetaC : (beta : ℂ) ≠ 0 := by
    exact_mod_cast hbeta.ne'
  unfold GK33.bε
  push_cast
  field_simp [hpi, hbetaC, Complex.I_ne_zero, Complex.I_mul_I]
  rw [zero_sub, mul_neg]
  calc
    -(Complex.I * (Complex.I * 2 * (beta : ℂ) * (Real.pi : ℂ))) =
        -((Complex.I * Complex.I) *
          (2 * (beta : ℂ) * (Real.pi : ℂ))) := by ring
    _ = 2 * (beta : ℂ) * (Real.pi : ℂ) := by
      rw [Complex.I_mul_I]
      ring

/-- Exact completion of the quadratic phase occurring after Poisson
summation.  The Fourier variable is written as a real number `ell`; in the
application it is the coercion of an integer satisfying `ell == b (mod c)`. -/
theorem section9_quadraticPhase_completeSquare
    {beta c : ℝ} (hbeta : beta ≠ 0) (hc : c ≠ 0) (ell eta t : ℝ) :
    beta * t ^ 2 - (ell + eta) * t / c =
      beta * (t - (ell + eta) / (2 * beta * c)) ^ 2 -
        (ell + eta) ^ 2 / (4 * beta * c ^ 2) := by
  field_simp [hbeta, hc]
  ring

/-- Exponentiating the completed square separates the stationary value from
the centered Fresnel phase. -/
theorem section9_e_quadraticPhase_completeSquare
    {beta c : ℝ} (hbeta : beta ≠ 0) (hc : c ≠ 0) (ell eta t : ℝ) :
    e (beta * t ^ 2 - (ell + eta) * t / c) =
      e (-(ell + eta) ^ 2 / (4 * beta * c ^ 2)) *
        e (beta * (t - (ell + eta) / (2 * beta * c)) ^ 2) := by
  rw [section9_quadraticPhase_completeSquare hbeta hc]
  have hphase :
      beta * (t - (ell + eta) / (2 * beta * c)) ^ 2 -
          (ell + eta) ^ 2 / (4 * beta * c ^ 2) =
        -(ell + eta) ^ 2 / (4 * beta * c ^ 2) +
          beta * (t - (ell + eta) / (2 * beta * c)) ^ 2 := by
    ring
  rw [hphase, KL.e_add]

/-- The stationary phase splits into the displayed phase of (9.6) and the
small `eta^2` correction that is absorbed into (9.7). -/
theorem section9_stationaryPhase_split
    {beta c : ℝ} (hbeta : beta ≠ 0) (hc : c ≠ 0) (ell eta : ℝ) :
    -(ell + eta) ^ 2 / (4 * beta * c ^ 2) =
      (-ell ^ 2 - 2 * eta * ell) / (4 * beta * c ^ 2) -
        eta ^ 2 / (4 * beta * c ^ 2) := by
  field_simp [hbeta, hc]
  ring

/-- Multiplicative form of `section9_stationaryPhase_split`, convenient for
estimating the phase replacement by `norm_e_sub_one_le`. -/
theorem section9_e_stationaryPhase_split
    {beta c : ℝ} (hbeta : beta ≠ 0) (hc : c ≠ 0) (ell eta : ℝ) :
    e (-(ell + eta) ^ 2 / (4 * beta * c ^ 2)) =
      e ((-ell ^ 2 - 2 * eta * ell) / (4 * beta * c ^ 2)) *
        e (-eta ^ 2 / (4 * beta * c ^ 2)) := by
  rw [section9_stationaryPhase_split hbeta hc]
  have hphase :
      (-ell ^ 2 - 2 * eta * ell) / (4 * beta * c ^ 2) -
          eta ^ 2 / (4 * beta * c ^ 2) =
        (-ell ^ 2 - 2 * eta * ell) / (4 * beta * c ^ 2) +
          (-eta ^ 2 / (4 * beta * c ^ 2)) := by
    ring
  rw [hphase, KL.e_add]

end LeanProofs.IntegerPoints
