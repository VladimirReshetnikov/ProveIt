import FabiusFunction.LogTanMeanZero
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The Gordin observable is square-integrable: `d ∈ L²`

The audits' variance layer (Document 6's Gordin decomposition,
`c₀ = ∫₀¹ d² = π²/4`, variance `(π²/4)·n + O(1)`) presupposes that
`d(t) = log |tan πt|` is square-integrable on `[0,1]`.  This module
proves it, quantitatively: the logarithmic singularities at
`t = 0, 1/2, 1` are dominated by the integrable power `t^{-1/2}`
through the explicit barrier `(log t)² ≤ 48·t^{-1/2}`.

Chain: `(log t)²` is integrable on `[0,1]` (barrier + `rpow`
integrability); the Jordan bracket `2t ≤ sin πt ≤ πt` on `[0,1/2]`
transfers this to `(log sin πt)²` with additive constant `(log π)²`;
reflection `sin π(1−t) = sin πt` covers `[1/2,1]`; the half-period
shift covers the cosine; and
`(log tan)² = (log sin − log cos)² ≤ 2(log sin)² + 2(log cos)²`
almost everywhere finishes.

* `sq_log_le_rpow` — the barrier `(log t)² ≤ 48·t^{-1/2}` on `(0,1]`.
* `intervalIntegrable_sq_log` — `(log t)² ∈ L¹(0,1)`.
* `sq_log_sin_le` — `(log sin πt)² ≤ (log t)² + (log π)²` on
  `(0,1/2]`.
* `intervalIntegrable_sq_log_sin_pi_mul`,
  `intervalIntegrable_sq_log_cos_pi_mul` — the two halves.
* `intervalIntegrable_sq_log_tan_pi_mul`,
  `intervalIntegrable_sq_log_abs_tan_pi_mul` — **`d ∈ L²([0,1])`**.
-/

set_option autoImplicit false

open intervalIntegral Real MeasureTheory

namespace Fabius

/-- Quantitative log-square barrier: `(log t)² ≤ 48·t^{-1/2}` on
`(0,1]`, from the cubic Taylor bound `x³/6 ≤ eˣ`. -/
theorem sq_log_le_rpow {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    Real.log t ^ 2 ≤ 48 * t ^ (-(1 / 2) : ℝ) := by
  set u : ℝ := -Real.log t with hu
  have hu0 : 0 ≤ u := by
    rw [hu, neg_nonneg]
    exact Real.log_nonpos ht.le ht1
  have hlog : Real.log t = -u := by rw [hu]; ring
  have hrpow : t ^ (-(1 / 2) : ℝ) = Real.exp (u / 2) := by
    rw [Real.rpow_def_of_pos ht, hlog]
    congr 1
    ring
  have hexp1 : (1:ℝ) ≤ Real.exp (u / 2) := Real.one_le_exp (by linarith)
  have hcube : (u / 2) ^ 3 / 6 ≤ Real.exp (u / 2) := by
    have h := Real.pow_div_factorial_le_exp (x := u / 2) (by linarith) 3
    norm_num [Nat.factorial] at h
    linarith [h]
  have hsq : Real.log t ^ 2 = u ^ 2 := by rw [hlog]; ring
  rw [hsq, hrpow]
  rcases le_or_gt (u ^ 2) 48 with hc | hc
  · nlinarith [hexp1]
  · have hu1 : 1 < u := by nlinarith
    nlinarith [hcube, mul_nonneg (sub_nonneg.mpr hu1.le) (sq_nonneg u)]

/-- `t ↦ (log t)²` is interval integrable on `[0,1]`. -/
theorem intervalIntegrable_sq_log :
    IntervalIntegrable (fun t : ℝ => Real.log t ^ 2)
      MeasureTheory.volume 0 1 := by
  have hdom : IntervalIntegrable (fun t : ℝ => 48 * t ^ (-(1 / 2) : ℝ))
      MeasureTheory.volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul 48
  apply hdom.mono_fun
  · exact (Real.measurable_log.pow_const 2).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc]
      with t ht
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    have h := sq_log_le_rpow ht.1 ht.2
    have h2 : (0:ℝ) < t ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos ht.1 _
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 48 * t ^ (-(1 / 2) : ℝ))]
    exact h

/-- The Jordan bracket `2t ≤ sin πt ≤ πt` pins the shell log-sine to
within `log π` of `log t`: on `(0, 1/2]`,
`(log sin πt)² ≤ (log t)² + (log π)²`. -/
theorem sq_log_sin_le {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 1 / 2) :
    Real.log (Real.sin (π * t)) ^ 2 ≤
      Real.log t ^ 2 + Real.log π ^ 2 := by
  have hπ := Real.pi_pos
  have hlow : 2 * t ≤ Real.sin (π * t) := by
    have h := Real.mul_le_sin (x := π * t) (by positivity) (by nlinarith)
    calc 2 * t = 2 / π * (π * t) := by field_simp
      _ ≤ Real.sin (π * t) := h
  have hup : Real.sin (π * t) ≤ π * t := (Real.sin_lt (by positivity)).le
  have hs0 : 0 < Real.sin (π * t) := by linarith
  have hL : Real.log 2 + Real.log t ≤ Real.log (Real.sin (π * t)) := by
    calc Real.log 2 + Real.log t = Real.log (2 * t) :=
          (Real.log_mul two_ne_zero (ne_of_gt ht)).symm
      _ ≤ Real.log (Real.sin (π * t)) :=
          Real.log_le_log (by positivity) hlow
  have hU : Real.log (Real.sin (π * t)) ≤ Real.log π + Real.log t := by
    calc Real.log (Real.sin (π * t)) ≤ Real.log (π * t) :=
          Real.log_le_log hs0 hup
      _ = Real.log π + Real.log t :=
          Real.log_mul (ne_of_gt hπ) (ne_of_gt ht)
  have hlt0 : Real.log t ≤ 0 := Real.log_nonpos ht.le (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set s := Real.log (Real.sin (π * t)) with hs
  have hδ0 : 0 ≤ s - Real.log t := by linarith
  have hδu : s - Real.log t ≤ Real.log π := by linarith
  have hδsq : (s - Real.log t) ^ 2 ≤ Real.log π ^ 2 := by nlinarith
  nlinarith [mul_nonneg (neg_nonneg.mpr hlt0) hδ0]

/-- `t ↦ (log sin πt)²` is interval integrable on `[0, 1/2]`. -/
theorem intervalIntegrable_sq_log_sin_pi_mul_half :
    IntervalIntegrable (fun t => Real.log (Real.sin (π * t)) ^ 2)
      MeasureTheory.volume 0 (1 / 2) := by
  have hdom : IntervalIntegrable
      (fun t : ℝ => Real.log t ^ 2 + Real.log π ^ 2)
      MeasureTheory.volume 0 (1 / 2) := by
    refine IntervalIntegrable.add ?_ intervalIntegrable_const
    refine intervalIntegrable_sq_log.mono_set ?_
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1 / 2),
      Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Set.Icc_subset_Icc le_rfl (by norm_num)
  apply hdom.mono_fun
  · exact ((Real.measurable_log.comp (Real.measurable_sin.comp
      (measurable_const_mul π))).pow_const 2).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc]
      with t ht
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1 / 2)] at ht
    have h := sq_log_sin_le ht.1 ht.2
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (by positivity :
        (0:ℝ) ≤ Real.log t ^ 2 + Real.log π ^ 2)]
    exact h

/-- `t ↦ (log sin πt)²` is interval integrable on `[0,1]`: the
reflection `sin π(1−t) = sin πt` transfers the left half to the
right half. -/
theorem intervalIntegrable_sq_log_sin_pi_mul :
    IntervalIntegrable (fun t => Real.log (Real.sin (π * t)) ^ 2)
      MeasureTheory.volume 0 1 := by
  apply intervalIntegrable_sq_log_sin_pi_mul_half.trans
  have h : IntervalIntegrable
      (fun x => Real.log (Real.sin (π * (1 - x))) ^ 2)
      MeasureTheory.volume (1 - 0) (1 - 1 / 2) :=
    intervalIntegrable_sq_log_sin_pi_mul_half.comp_sub_left 1
  have heq : (fun x => Real.log (Real.sin (π * (1 - x))) ^ 2) =
      fun x => Real.log (Real.sin (π * x)) ^ 2 := by
    funext x
    rw [show π * (1 - x) = π - π * x by ring, Real.sin_pi_sub]
  rw [heq] at h
  have h2 := h.symm
  convert h2 using 2 <;> norm_num

/-- `t ↦ (log cos πt)²` is interval integrable on `[0,1]` (half-period
shift of the sine version). -/
theorem intervalIntegrable_sq_log_cos_pi_mul :
    IntervalIntegrable (fun t => Real.log (Real.cos (π * t)) ^ 2)
      MeasureTheory.volume 0 1 := by
  have hper : Function.Periodic
      (fun t => Real.log (Real.sin (π * t)) ^ 2) 1 :=
    periodic_log_sin_pi_mul.comp (fun s => s ^ 2)
  have hall : ∀ a b : ℝ, IntervalIntegrable
      (fun t => Real.log (Real.sin (π * t)) ^ 2)
      MeasureTheory.volume a b :=
    fun a b => hper.intervalIntegrable₀ one_ne_zero
      intervalIntegrable_sq_log_sin_pi_mul a b
  have hshift : (fun t => Real.log (Real.cos (π * t)) ^ 2) =
      fun t => Real.log (Real.sin (π * (t + 1 / 2))) ^ 2 := by
    funext t
    rw [show π * (t + 1 / 2) = π * t + π / 2 by ring,
      Real.sin_add_pi_div_two]
  have h : IntervalIntegrable
      (fun t => Real.log (Real.sin (π * (t + 1 / 2))) ^ 2)
      MeasureTheory.volume (1 / 2 - 1 / 2) (3 / 2 - 1 / 2) :=
    (hall (1 / 2) (3 / 2)).comp_add_right (1 / 2)
  rw [hshift]
  convert h using 2 <;> norm_num

/-- **The Gordin observable is square-integrable**: `d ∈ L²([0,1])`
for `d(t) = log (tan πt)` — the standing integrability hypothesis of
the audits' variance layer. -/
theorem intervalIntegrable_sq_log_tan_pi_mul :
    IntervalIntegrable (fun t => Real.log (Real.tan (π * t)) ^ 2)
      MeasureTheory.volume 0 1 := by
  have hdom : IntervalIntegrable
      (fun t => 2 * Real.log (Real.sin (π * t)) ^ 2 +
        2 * Real.log (Real.cos (π * t)) ^ 2)
      MeasureTheory.volume 0 1 :=
    (intervalIntegrable_sq_log_sin_pi_mul.const_mul 2).add
      (intervalIntegrable_sq_log_cos_pi_mul.const_mul 2)
  apply hdom.mono_fun
  · have hm : Measurable fun t : ℝ => Real.tan (π * t) := by
      have h := (Real.measurable_sin.comp (measurable_const_mul π)).div
        (Real.measurable_cos.comp (measurable_const_mul π))
      have heq : (fun t : ℝ => Real.tan (π * t)) =
          fun t => Real.sin (π * t) / Real.cos (π * t) := by
        funext t
        exact Real.tan_eq_sin_div_cos (π * t)
      rw [heq]
      exact h
    exact ((Real.measurable_log.comp hm).pow_const 2).aestronglyMeasurable
  · have hhalf : ∀ᵐ t : ℝ, t ≠ (1 / 2 : ℝ) := by
      rw [MeasureTheory.ae_iff]
      simp
    have h1ae : ∀ᵐ t : ℝ, t ≠ (1 : ℝ) := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [MeasureTheory.ae_restrict_of_ae hhalf,
      MeasureTheory.ae_restrict_of_ae h1ae,
      MeasureTheory.ae_restrict_mem measurableSet_uIoc]
      with t hthalf ht1 hmem
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
    simp only [Real.norm_eq_abs]
    rw [Real.tan_eq_sin_div_cos, Real.log_div (ne_of_gt hs) hc,
      abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (by positivity :
        (0:ℝ) ≤ 2 * Real.log (Real.sin (π * t)) ^ 2 +
          2 * Real.log (Real.cos (π * t)) ^ 2)]
    nlinarith [sq_nonneg (Real.log (Real.sin (π * t)) +
      Real.log (Real.cos (π * t)))]

/-- The audit's normalization: `t ↦ (log |tan πt|)²` is interval
integrable on `[0,1]`. -/
theorem intervalIntegrable_sq_log_abs_tan_pi_mul :
    IntervalIntegrable (fun t => Real.log |Real.tan (π * t)| ^ 2)
      MeasureTheory.volume 0 1 := by
  simpa only [Real.log_abs] using intervalIntegrable_sq_log_tan_pi_mul

end Fabius
