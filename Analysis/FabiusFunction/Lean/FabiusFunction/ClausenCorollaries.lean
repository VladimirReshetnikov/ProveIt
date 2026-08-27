import FabiusFunction.GordinParseval

/-!
# Corollaries of the Clausen values

Numerical closures now available for free:

* `intervalIntegrable_log_two_sin_pi_mul_self` — `ψ ∈ L¹`.
* `integral_cocycle_correlation_eq` — the first covariance **number**:
  `c₁ = ∫₀¹ ψ·(ψ∘T) = π²/24` (halving mechanism × Clausen value).
* `integral_sq_log_sin_pi_mul` — the classical
  `∫₀¹ log² (sin πt) dt = π²/12 + log² 2`.
* `integral_sq_log_tan_pi_mul` — the variance without the absolute
  value, `∫₀¹ log² (tan πt) dt = π²/4`.
-/

set_option autoImplicit false

open Filter Topology intervalIntegral Real MeasureTheory

namespace Fabius

/-- The cocycle itself is interval integrable on `[0,1]`. -/
theorem intervalIntegrable_log_two_sin_pi_mul_self :
    IntervalIntegrable (fun t => Real.log (2 * Real.sin (π * t)))
      MeasureTheory.volume 0 1 := by
  have hdom : IntervalIntegrable
      (fun t => (1 + Real.log (2 * Real.sin (π * t)) ^ 2) / 2)
      MeasureTheory.volume 0 1 :=
    (intervalIntegrable_const.add
      intervalIntegrable_sq_log_two_sin_pi_mul).div_const 2
  apply hdom.mono_fun
  · exact measurable_log_two_sin_pi_mul.aestronglyMeasurable
  · filter_upwards with t
    set A := Real.log (2 * Real.sin (π * t))
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 + A ^ 2) / 2)]
    nlinarith [sq_nonneg (|A| - 1), sq_abs A, abs_nonneg A]

/-- **The first covariance number**: `c₁ = ∫₀¹ ψ·(ψ∘T) = π²/24`
(branchwise) — the halving mechanism times the Clausen value. -/
theorem integral_cocycle_correlation_eq :
    ((∫ t in (0:ℝ)..(1/2:ℝ), Real.log (2 * Real.sin (π * t)) *
        Real.log (2 * Real.sin (π * (2 * t)))) +
      ∫ t in (1/2:ℝ)..1, Real.log (2 * Real.sin (π * t)) *
        Real.log (2 * Real.sin (π * (2 * t - 1)))) = π ^ 2 / 24 := by
  rw [integral_log_two_sin_mul_comp_doubling,
    integral_sq_log_two_sin_pi_mul]
  ring

/-- **The classical log-sine square integral**:
`∫₀¹ log² (sin πt) dt = π²/12 + log² 2`. -/
theorem integral_sq_log_sin_pi_mul :
    ∫ t in (0:ℝ)..1, Real.log (Real.sin (π * t)) ^ 2 =
      π ^ 2 / 12 + Real.log 2 ^ 2 := by
  have hsplit : ∫ t in (0:ℝ)..1, Real.log (Real.sin (π * t)) ^ 2 =
      ∫ t in (0:ℝ)..1, (Real.log (2 * Real.sin (π * t)) ^ 2 -
        2 * Real.log 2 * Real.log (2 * Real.sin (π * t)) +
        Real.log 2 ^ 2) := by
    apply intervalIntegral.integral_congr_ae
    have h1ae : ∀ᵐ t : ℝ, t ≠ (1:ℝ) := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [h1ae] with t ht1 hmem
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hmem
    have hs : 0 < Real.sin (π * t) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · have := hmem.1
        positivity
      · nlinarith [Real.pi_pos, hmem.1, lt_of_le_of_ne hmem.2 ht1]
    have hlog : Real.log (2 * Real.sin (π * t)) =
        Real.log 2 + Real.log (Real.sin (π * t)) :=
      Real.log_mul two_ne_zero (ne_of_gt hs)
    rw [hlog]
    ring
  rw [hsplit,
    intervalIntegral.integral_add
      (intervalIntegrable_sq_log_two_sin_pi_mul.sub
        (intervalIntegrable_log_two_sin_pi_mul_self.const_mul
          (2 * Real.log 2)))
      intervalIntegrable_const,
    intervalIntegral.integral_sub
      intervalIntegrable_sq_log_two_sin_pi_mul
      (intervalIntegrable_log_two_sin_pi_mul_self.const_mul
        (2 * Real.log 2)),
    intervalIntegral.integral_const_mul,
    integral_sq_log_two_sin_pi_mul, integral_log_two_sin_pi_mul,
    intervalIntegral.integral_const]
  simp

/-- The variance without the absolute value:
`∫₀¹ log² (tan πt) dt = π²/4`. -/
theorem integral_sq_log_tan_pi_mul :
    ∫ t in (0:ℝ)..1, Real.log (Real.tan (π * t)) ^ 2 = π ^ 2 / 4 := by
  have h : (fun t => Real.log (Real.tan (π * t)) ^ 2) =
      fun t => Real.log |Real.tan (π * t)| ^ 2 := by
    funext t
    rw [Real.log_abs]
  rw [h]
  exact integral_sq_log_abs_tan_pi_mul

end Fabius
