import FabiusFunction.LogSineMeanZero
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The Gordin observable is centered: `∫₀¹ log |tan πt| dt = 0`

Document 6's Gordin decomposition works with the coboundary-corrected
observable `d(t) = log |tan πt| = 2ψ(t) − ψ(Tt)` of
`DoublingCocycleIdentities`, where `ψ = log (2 sin π·)`.  There the
*pointwise* annihilation `𝒫d = 0` was proved; here we prove the
*measure-level* centering `∫₀¹ d = 0` — the zeroth moment that
normalizes the martingale fluctuation theory (variance `π²/4`,
`σ = π/2`).

Route: `log ∘ sin ∘ (π·)` is `1`-periodic because `Real.log` is even,
so the log-cosine mean equals the log-sine mean by the half-period
shift `cos πt = sin π(t + 1/2)`, and `log tan = log sin − log cos`
almost everywhere on the fundamental interval.

* `periodic_log_sin_pi_mul` — `1`-periodicity of `log (sin π·)`.
* `intervalIntegrable_log_sin_pi_mul'` — integrability on every
  interval.
* `intervalIntegrable_log_cos_pi_mul`, `integral_log_cos_pi_mul` —
  `∫₀¹ log (cos πt) dt = −log 2`.
* `integral_log_tan_pi_mul`, `integral_log_abs_tan_pi_mul` —
  `∫₀¹ log |tan πt| dt = 0`.
-/

set_option autoImplicit false

open intervalIntegral Real MeasureTheory

namespace Fabius

/-- `t ↦ log (sin πt)` is `1`-periodic: `sin π(t+1) = −sin πt` and
`Real.log` is even. -/
theorem periodic_log_sin_pi_mul :
    Function.Periodic (fun t => Real.log (Real.sin (π * t))) 1 := by
  intro t
  show Real.log (Real.sin (π * (t + 1))) = Real.log (Real.sin (π * t))
  rw [show π * (t + 1) = π * t + π by ring, Real.sin_add_pi,
    Real.log_neg_eq_log]

/-- `t ↦ log (sin πt)` is interval integrable on every interval. -/
theorem intervalIntegrable_log_sin_pi_mul' (a b : ℝ) :
    IntervalIntegrable (fun t => Real.log (Real.sin (π * t)))
      MeasureTheory.volume a b :=
  periodic_log_sin_pi_mul.intervalIntegrable₀ one_ne_zero
    intervalIntegrable_log_sin_pi_mul a b

/-- `t ↦ log (cos πt)` is interval integrable on `[0,1]`. -/
theorem intervalIntegrable_log_cos_pi_mul :
    IntervalIntegrable (fun t => Real.log (Real.cos (π * t)))
      MeasureTheory.volume 0 1 := by
  have hshift : (fun t => Real.log (Real.cos (π * t))) =
      fun t => Real.log (Real.sin (π * (t + 1 / 2))) := by
    funext t
    rw [show π * (t + 1 / 2) = π * t + π / 2 by ring,
      Real.sin_add_pi_div_two]
  have h : IntervalIntegrable
      (fun t => Real.log (Real.sin (π * (t + 1 / 2))))
      MeasureTheory.volume (1 / 2 - 1 / 2) (3 / 2 - 1 / 2) :=
    (intervalIntegrable_log_sin_pi_mul' (1 / 2) (3 / 2)).comp_add_right
      (1 / 2)
  rw [hshift]
  convert h using 2 <;> norm_num

/-- **The log-cosine mean**: `∫₀¹ log (cos πt) dt = −log 2` — equal
to the log-sine mean by the half-period shift and `1`-periodicity. -/
theorem integral_log_cos_pi_mul :
    ∫ t in (0:ℝ)..1, Real.log (Real.cos (π * t)) = -Real.log 2 := by
  calc ∫ t in (0:ℝ)..1, Real.log (Real.cos (π * t))
      = ∫ t in (0:ℝ)..1, Real.log (Real.sin (π * (t + 1 / 2))) :=
        intervalIntegral.integral_congr (fun t _ => by
          show Real.log (Real.cos (π * t)) =
            Real.log (Real.sin (π * (t + 1 / 2)))
          rw [show π * (t + 1 / 2) = π * t + π / 2 by ring,
            Real.sin_add_pi_div_two])
    _ = ∫ u in (0 + 1 / 2 : ℝ)..(1 + 1 / 2 : ℝ),
          Real.log (Real.sin (π * u)) :=
        intervalIntegral.integral_comp_add_right
          (f := fun u => Real.log (Real.sin (π * u))) (1 / 2)
    _ = ∫ u in (1 / 2 : ℝ)..(1 / 2 + 1 : ℝ),
          Real.log (Real.sin (π * u)) := by norm_num
    _ = ∫ u in (0 : ℝ)..(0 + 1 : ℝ), Real.log (Real.sin (π * u)) :=
        periodic_log_sin_pi_mul.intervalIntegral_add_eq (1 / 2) 0
    _ = ∫ u in (0 : ℝ)..1, Real.log (Real.sin (π * u)) := by norm_num
    _ = -Real.log 2 := integral_log_sin_pi_mul

/-- **The Gordin observable is centered**:
`∫₀¹ log (tan πt) dt = 0` — the log-sine and log-cosine means cancel
exactly. -/
theorem integral_log_tan_pi_mul :
    ∫ t in (0:ℝ)..1, Real.log (Real.tan (π * t)) = 0 := by
  have hsplit : ∫ t in (0:ℝ)..1, Real.log (Real.tan (π * t)) =
      ∫ t in (0:ℝ)..1,
        (Real.log (Real.sin (π * t)) - Real.log (Real.cos (π * t))) := by
    apply intervalIntegral.integral_congr_ae
    have hhalf : ∀ᵐ t : ℝ, t ≠ (1 / 2 : ℝ) := by
      rw [MeasureTheory.ae_iff]
      simp
    have h1ae : ∀ᵐ t : ℝ, t ≠ (1 : ℝ) := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [hhalf, h1ae] with t hthalf ht1 hmem
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hmem
    have htpos : 0 < t := hmem.1
    have htlt : t < 1 := lt_of_le_of_ne hmem.2 ht1
    have hs : 0 < Real.sin (π * t) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · positivity
      · nlinarith [Real.pi_pos]
    have hc : Real.cos (π * t) ≠ 0 := by
      intro hc0
      obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp hc0
      have hcan : π * t = π * ((2 * (k:ℝ) + 1) / 2) := by
        linear_combination hk
      have ht : t = (2 * (k:ℝ) + 1) / 2 :=
        mul_left_cancel₀ Real.pi_ne_zero hcan
      have hk0 : (0:ℝ) < 2 * (k:ℝ) + 1 := by
        rw [ht] at htpos
        linarith
      have hk2 : (2 * (k:ℝ) + 1) < 2 := by
        rw [ht] at htlt
        linarith
      have hk0' : (0:ℤ) < 2 * k + 1 := by exact_mod_cast hk0
      have hk2' : (2 * k + 1 : ℤ) < 2 := by exact_mod_cast hk2
      have hkz : k = 0 := by omega
      rw [hkz] at ht
      norm_num at ht
      exact hthalf ht
    rw [Real.tan_eq_sin_div_cos, Real.log_div (ne_of_gt hs) hc]
  rw [hsplit,
    intervalIntegral.integral_sub intervalIntegrable_log_sin_pi_mul
      intervalIntegrable_log_cos_pi_mul,
    integral_log_sin_pi_mul, integral_log_cos_pi_mul]
  ring

/-- The audit's normalization `d(t) = log |tan πt|` has mean zero. -/
theorem integral_log_abs_tan_pi_mul :
    ∫ t in (0:ℝ)..1, Real.log |Real.tan (π * t)| = 0 := by
  simp only [Real.log_abs]
  exact integral_log_tan_pi_mul

end Fabius
