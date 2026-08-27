import FabiusFunction.SquareLogIntegrable
import FabiusFunction.DoublingTransferAdjoint
import FabiusFunction.DoublingCocycleIdentities

/-!
# Martingale orthogonality of the Gordin observable: `c₁ = 0`

Document 6's Gordin decomposition rests on `d(t) = log |tan πt|` being
a *martingale difference* for the doubling map: `𝒫d = 0` pointwise
(`DoublingCocycleIdentities.log_abs_tan_half_add`) forces every
correlation of `d` with a pullback `g ∘ T` to vanish, so the Birkhoff
variance is exactly additive, `Var(Σ_{k<n} d∘Tᵏ) = n·∫d²` — the
mechanism behind the audit's `σ² = π²/4`.

This module supplies the integrability plumbing (branch products of
two log-singular factors, dominated by squares via AM–GM and the `L²`
bound of `SquareLogIntegrable`) and proves the correlation identity in
branchwise form:

`∫₀^½ d(t)·d(2t) dt + ∫_½^1 d(t)·d(2t−1) dt = 0`,

i.e. `c₁ = ∫₀¹ d·(d∘T) = 0` with the doubling map written without a
fractional part.

* `measurable_log_abs_tan_pi_mul` — measurability of `d`.
* `intervalIntegrable_sq_log_abs_tan_half`, `…_shift` — the two branch
  squares `d(u/2)²`, `d((u+1)/2)²` on `[0,1]`.
* `intervalIntegrable_branch_product_left`, `…_right` — the branch
  products `d(u/2)·d(u)`, `d((u+1)/2)·d(u)` (AM–GM domination).
* `integral_mul_comp_doubling_of_annihilated` — the abstract
  annihilation: a.e. `𝒫f = 0` kills the pairing `∫ f·(g∘T)`.
* `integral_log_abs_tan_mul_comp_doubling` — **`c₁ = 0`**.
-/

set_option autoImplicit false

open intervalIntegral Real MeasureTheory

namespace Fabius

/-- The Gordin observable `d = log |tan π·|` is measurable. -/
theorem measurable_log_abs_tan_pi_mul :
    Measurable fun t : ℝ => Real.log |Real.tan (π * t)| := by
  have htan : Measurable fun t : ℝ => Real.tan (π * t) := by
    have h := (Real.measurable_sin.comp (measurable_const_mul π)).div
      (Real.measurable_cos.comp (measurable_const_mul π))
    have heq : (fun t : ℝ => Real.tan (π * t)) =
        fun t => Real.sin (π * t) / Real.cos (π * t) := by
      funext t
      exact Real.tan_eq_sin_div_cos (π * t)
    rw [heq]
    exact h
  exact Real.measurable_log.comp (continuous_abs.measurable.comp htan)

/-- The left branch square `u ↦ d(u/2)²` is integrable on `[0,1]`. -/
theorem intervalIntegrable_sq_log_abs_tan_half :
    IntervalIntegrable (fun u => Real.log |Real.tan (π * (u / 2))| ^ 2)
      MeasureTheory.volume 0 1 := by
  have hbase : IntervalIntegrable
      (fun t => Real.log |Real.tan (π * t)| ^ 2)
      MeasureTheory.volume 0 (1 / 2) := by
    refine intervalIntegrable_sq_log_abs_tan_pi_mul.mono_set ?_
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1 / 2),
      Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Set.Icc_subset_Icc le_rfl (by norm_num)
  have h : IntervalIntegrable
      (fun u => Real.log |Real.tan (π * (u * (1 / 2)))| ^ 2)
      MeasureTheory.volume (0 / (1 / 2)) ((1 / 2) / (1 / 2)) :=
    hbase.comp_mul_right
  have heq : (fun u => Real.log |Real.tan (π * (u * (1 / 2)))| ^ 2) =
      fun u => Real.log |Real.tan (π * (u / 2))| ^ 2 := by
    funext u
    rw [show π * (u * (1 / 2)) = π * (u / 2) by ring]
  rw [heq] at h
  convert h using 2 <;> norm_num

/-- The right branch square `u ↦ d((u+1)/2)²` is integrable on
`[0,1]`. -/
theorem intervalIntegrable_sq_log_abs_tan_shift :
    IntervalIntegrable
      (fun u => Real.log |Real.tan (π * ((u + 1) / 2))| ^ 2)
      MeasureTheory.volume 0 1 := by
  have hbase : IntervalIntegrable
      (fun t => Real.log |Real.tan (π * t)| ^ 2)
      MeasureTheory.volume (1 / 2) 1 := by
    refine intervalIntegrable_sq_log_abs_tan_pi_mul.mono_set ?_
    rw [Set.uIcc_of_le (by norm_num : (1:ℝ) / 2 ≤ 1),
      Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Set.Icc_subset_Icc (by norm_num) le_rfl
  have h1 : IntervalIntegrable
      (fun u => Real.log |Real.tan (π * (u * (1 / 2)))| ^ 2)
      MeasureTheory.volume ((1 / 2) / (1 / 2)) (1 / (1 / 2)) :=
    hbase.comp_mul_right
  have heq1 : (fun u => Real.log |Real.tan (π * (u * (1 / 2)))| ^ 2) =
      fun u => Real.log |Real.tan (π * (u / 2))| ^ 2 := by
    funext u
    rw [show π * (u * (1 / 2)) = π * (u / 2) by ring]
  rw [heq1] at h1
  have h2 : IntervalIntegrable
      (fun u => Real.log |Real.tan (π * ((u + 1) / 2))| ^ 2)
      MeasureTheory.volume ((1 / 2) / (1 / 2) - 1) (1 / (1 / 2) - 1) :=
    h1.comp_add_right 1
  convert h2 using 2 <;> norm_num

/-- The left branch product `u ↦ d(u/2)·d(u)` is integrable on
`[0,1]` (AM–GM domination by the branch squares). -/
theorem intervalIntegrable_branch_product_left :
    IntervalIntegrable (fun u => Real.log |Real.tan (π * (u / 2))| *
      Real.log |Real.tan (π * u)|) MeasureTheory.volume 0 1 := by
  have hdom : IntervalIntegrable
      (fun u => (1 / 2 : ℝ) *
        (Real.log |Real.tan (π * (u / 2))| ^ 2 +
          Real.log |Real.tan (π * u)| ^ 2))
      MeasureTheory.volume 0 1 :=
    (intervalIntegrable_sq_log_abs_tan_half.add
      intervalIntegrable_sq_log_abs_tan_pi_mul).const_mul (1 / 2)
  apply hdom.mono_fun
  · exact ((measurable_log_abs_tan_pi_mul.comp
      (measurable_id.div_const 2)).mul
      measurable_log_abs_tan_pi_mul).aestronglyMeasurable
  · filter_upwards with u
    set A := Real.log |Real.tan (π * (u / 2))| with hA
    set B := Real.log |Real.tan (π * u)| with hB
    simp only [Real.norm_eq_abs]
    rw [abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / 2 * (A ^ 2 + B ^ 2))]
    nlinarith [sq_nonneg (|A| - |B|), sq_abs A, sq_abs B,
      abs_nonneg A, abs_nonneg B]

/-- The right branch product `u ↦ d((u+1)/2)·d(u)` is integrable on
`[0,1]`. -/
theorem intervalIntegrable_branch_product_right :
    IntervalIntegrable
      (fun u => Real.log |Real.tan (π * ((u + 1) / 2))| *
        Real.log |Real.tan (π * u)|) MeasureTheory.volume 0 1 := by
  have hdom : IntervalIntegrable
      (fun u => (1 / 2 : ℝ) *
        (Real.log |Real.tan (π * ((u + 1) / 2))| ^ 2 +
          Real.log |Real.tan (π * u)| ^ 2))
      MeasureTheory.volume 0 1 :=
    (intervalIntegrable_sq_log_abs_tan_shift.add
      intervalIntegrable_sq_log_abs_tan_pi_mul).const_mul (1 / 2)
  apply hdom.mono_fun
  · exact ((measurable_log_abs_tan_pi_mul.comp
      ((measurable_id.add_const 1).div_const 2)).mul
      measurable_log_abs_tan_pi_mul).aestronglyMeasurable
  · filter_upwards with u
    set A := Real.log |Real.tan (π * ((u + 1) / 2))| with hA
    set B := Real.log |Real.tan (π * u)| with hB
    simp only [Real.norm_eq_abs]
    rw [abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / 2 * (A ^ 2 + B ^ 2))]
    nlinarith [sq_nonneg (|A| - |B|), sq_abs A, sq_abs B,
      abs_nonneg A, abs_nonneg B]

/-- **Abstract martingale annihilation**: if the Perron average of `f`
vanishes a.e. on the fundamental interval, the pairing of `f` with any
pullback `g ∘ T` vanishes (given the branch products are
integrable). -/
theorem integral_mul_comp_doubling_of_annihilated (f g : ℝ → ℝ)
    (hint1 : IntervalIntegrable (fun u => f (u / 2) * g u)
      MeasureTheory.volume 0 1)
    (hint2 : IntervalIntegrable (fun u => f ((u + 1) / 2) * g u)
      MeasureTheory.volume 0 1)
    (hzero : ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Set.uIoc (0:ℝ) 1 → f (t / 2) + f ((t + 1) / 2) = 0) :
    ((∫ t in (0:ℝ)..(1/2:ℝ), f t * g (2 * t)) +
      ∫ t in (1/2:ℝ)..1, f t * g (2 * t - 1)) = 0 := by
  rw [integral_mul_comp_doubling' f g hint1 hint2]
  have hcongr : ∫ t in (0:ℝ)..1, (f (t / 2) + f ((t + 1) / 2)) / 2 * g t =
      ∫ t in (0:ℝ)..1, (0:ℝ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hzero] with t ht hmem
    rw [ht hmem]
    ring
  rw [hcongr]
  simp

/-- **Martingale orthogonality of the Gordin observable, `c₁ = 0`**:

`∫₀^½ d(t)·d(2t) dt + ∫_½^1 d(t)·d(2t−1) dt = 0`

for `d = log |tan π·|` — the correlation of `d` with its own doubling
pullback vanishes, so the Birkhoff variance of `d` is exactly additive
(`Var = n·∫d²`), as the audit's Gordin argument requires. -/
theorem integral_log_abs_tan_mul_comp_doubling :
    ((∫ t in (0:ℝ)..(1/2:ℝ), Real.log |Real.tan (π * t)| *
        Real.log |Real.tan (π * (2 * t))|) +
      ∫ t in (1/2:ℝ)..1, Real.log |Real.tan (π * t)| *
        Real.log |Real.tan (π * (2 * t - 1))|) = 0 := by
  apply integral_mul_comp_doubling_of_annihilated
    (fun t => Real.log |Real.tan (π * t)|)
    (fun t => Real.log |Real.tan (π * t)|)
    intervalIntegrable_branch_product_left
    intervalIntegrable_branch_product_right
  have h1ae : ∀ᵐ t : ℝ, t ≠ (1:ℝ) := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [h1ae] with t ht1 hmem
  rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hmem
  have ht0 : 0 < t := hmem.1
  have htl : t < 1 := lt_of_le_of_ne hmem.2 ht1
  have hs : Real.sin (π * t / 2) ≠ 0 := by
    have h : 0 < Real.sin (π * t / 2) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · positivity
      · nlinarith [Real.pi_pos]
    exact ne_of_gt h
  have hc : Real.cos (π * t / 2) ≠ 0 := by
    have h : 0 < Real.cos (π * t / 2) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · nlinarith [Real.pi_pos]
      · nlinarith [Real.pi_pos]
    exact ne_of_gt h
  have h := log_abs_tan_half_add t hs hc
  show Real.log |Real.tan (π * (t / 2))| +
    Real.log |Real.tan (π * ((t + 1) / 2))| = 0
  rw [show π * (t / 2) = π * t / 2 by ring,
    show π * ((t + 1) / 2) = π * (t + 1) / 2 by ring]
  exact h

end Fabius
