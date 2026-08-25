import FabiusFunction.MellinFinitePart
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The finite-part integral of the logarithmic Bose kernel

The Mellin transform of `log (1 - exp (-x))` has a double pole at the origin.
This module realizes its finite part as a convergent split integral.  Near zero
the singular `log x` term is removed with `negativeLaplaceKernel`; near infinity
the original logarithmic kernel is divided by `x` and controlled by exponential
decay.  Dominated convergence then identifies the split integral with
`gammaZetaConstant`.

The definitions `boseFinitePartSmallKernel` and
`boseFinitePartLargeKernel` are also the kernel interface used by the later
periodic-mean and Fourier-coefficient calculations.
-/

set_option autoImplicit false

open scoped BigOperators Topology Interval
open Set Filter MeasureTheory Asymptotics

namespace Fabius

/-- The logarithmic Bose kernel `log (1 - exp (-x))`. -/
noncomputable def boseLogKernel (x : ℝ) : ℝ :=
  Real.log (1 - Real.exp (-x))

/-- The regularized kernel near zero, obtained after removing `log x`. -/
noncomputable def boseFinitePartSmallKernel (x : ℝ) : ℝ :=
  negativeLaplaceKernel x / x

/-- The integrable large-`x` kernel `log (1 - exp (-x)) / x`. -/
noncomputable def boseFinitePartLargeKernel (x : ℝ) : ℝ :=
  boseLogKernel x / x

/-- The logarithmic Bose kernel is continuous on the positive half-line. -/
lemma continuousOn_boseLogKernel :
    ContinuousOn boseLogKernel (Ioi 0) := by
  intro x hx
  change 0 < x at hx
  unfold boseLogKernel
  apply ContinuousAt.continuousWithinAt
  have hnum : 1 - Real.exp (-x) ≠ 0 := by
    exact (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))).ne'
  fun_prop (disch := assumption)

lemma continuousOn_boseFinitePartSmallKernel :
    ContinuousOn boseFinitePartSmallKernel (Ioi 0) := by
  intro x hx
  change 0 < x at hx
  unfold boseFinitePartSmallKernel negativeLaplaceKernel
  apply ContinuousAt.continuousWithinAt
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hnum : 1 - Real.exp (-x) ≠ 0 := by
    apply (sub_pos.mpr ?_).ne'
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hratio : (1 - Real.exp (-x)) / x ≠ 0 := div_ne_zero hnum hx0
  fun_prop (disch := assumption)

/-- The small finite-part kernel is bounded by one at every positive argument.
The upper cutoff used in the split integral is not needed for this estimate. -/
lemma abs_boseFinitePartSmallKernel_le_one_of_pos
    (x : ℝ) (hx : 0 < x) :
    |boseFinitePartSmallKernel x| ≤ 1 := by
  unfold boseFinitePartSmallKernel
  rw [abs_div, abs_of_pos hx]
  exact (div_le_one hx).mpr (abs_negativeLaplaceKernel_le x hx)

lemma integrableOn_boseFinitePartSmallKernel :
    IntegrableOn boseFinitePartSmallKernel (Ioc 0 1) := by
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 0 1) :=
    integrableOn_const (measure_Ioc_lt_top.ne)
  change Integrable boseFinitePartSmallKernel (volume.restrict (Ioc 0 1))
  change Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioc 0 1)) at hone
  apply hone.mono
  · exact (continuousOn_boseFinitePartSmallKernel.mono
      (Ioc_subset_Ioi_self : Ioc (0 : ℝ) 1 ⊆ Ioi 0)).aestronglyMeasurable
        measurableSet_Ioc
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs]
    simpa only [norm_one] using
      abs_boseFinitePartSmallKernel_le_one_of_pos x hx.1

/-- Compatibility form of `abs_boseFinitePartSmallKernel_le_one_of_pos` on the
small integration interval. -/
lemma abs_boseFinitePartSmallKernel_le_one
    (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) :
    |boseFinitePartSmallKernel x| ≤ 1 :=
  abs_boseFinitePartSmallKernel_le_one_of_pos x hx.1

lemma continuousOn_boseFinitePartLargeKernel :
    ContinuousOn boseFinitePartLargeKernel (Ioi 0) := by
  intro x hx
  change 0 < x at hx
  unfold boseFinitePartLargeKernel boseLogKernel
  apply ContinuousAt.continuousWithinAt
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hnum : 1 - Real.exp (-x) ≠ 0 := by
    apply (sub_pos.mpr ?_).ne'
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  fun_prop (disch := assumption)

/-- Exponential domination of the Bose kernel beyond an arbitrary positive
cutoff. -/
lemma abs_boseLogKernel_le_const_exp_of_le
    (c x : ℝ) (hc : 0 < c) (hx : c ≤ x) :
    |boseLogKernel x| ≤
      (1 / (1 - Real.exp (-c))) * Real.exp (-x) := by
  have hx0 : 0 < x := hc.trans_le hx
  have hH : |boseLogKernel x| ≤
      Real.exp (-x) / (1 - Real.exp (-x)) := by
    have h := abs_negativeLaplaceForwardTerm_le x hx0 0
    simpa [negativeLaplaceForwardTerm, boseLogKernel] using h
  have he : Real.exp (-x) ≤ Real.exp (-c) :=
    Real.exp_le_exp.mpr (by linarith)
  have hd0 : 0 < 1 - Real.exp (-c) := by
    rw [sub_pos, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hd : 1 - Real.exp (-c) ≤ 1 - Real.exp (-x) :=
    sub_le_sub_left he 1
  calc
    |boseLogKernel x| ≤ Real.exp (-x) / (1 - Real.exp (-x)) := hH
    _ ≤ 1 / (1 - Real.exp (-c)) * Real.exp (-x) := by
      rw [one_div_mul_eq_div]
      exact div_le_div_of_nonneg_left (Real.exp_nonneg _) hd0 hd

/-- Exponential domination beyond the unit cutoff. -/
lemma abs_boseLogKernel_le_const_exp (x : ℝ) (hx : 1 ≤ x) :
    |boseLogKernel x| ≤
      (1 / (1 - Real.exp (-1))) * Real.exp (-x) := by
  exact abs_boseLogKernel_le_const_exp_of_le 1 x (by norm_num) hx

lemma integrableOn_boseLogKernel_Ioi_one :
    IntegrableOn boseLogKernel (Ioi 1) := by
  let c : ℝ := 1 / (1 - Real.exp (-1))
  have hc0 : 0 ≤ c := by
    dsimp [c]
    exact (one_div_pos.mpr
      (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num)))).le
  have hg : IntegrableOn (fun x : ℝ => c * Real.exp (-x)) (Ioi 1) :=
    (integrableOn_exp_neg_Ioi 1).const_mul c
  change Integrable boseLogKernel (volume.restrict (Ioi 1))
  change Integrable (fun x : ℝ => c * Real.exp (-x))
    (volume.restrict (Ioi 1)) at hg
  apply hg.mono
  · have hsubset : Ioi (1 : ℝ) ⊆ Ioi 0 := by
      intro x hx
      change 1 < x at hx
      exact zero_lt_one.trans hx
    exact (continuousOn_boseLogKernel.mono hsubset).aestronglyMeasurable
      measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change 1 < x at hx
    rw [Real.norm_eq_abs]
    refine (abs_boseLogKernel_le_const_exp x hx.le).trans_eq ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc0 (Real.exp_nonneg _))]

lemma integrableOn_boseFinitePartLargeKernel :
    IntegrableOn boseFinitePartLargeKernel (Ioi 1) := by
  let c : ℝ := 1 / (1 - Real.exp (-1))
  have hc0 : 0 ≤ c := by
    dsimp [c]
    exact (one_div_pos.mpr
      (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num)))).le
  have hg : IntegrableOn (fun x : ℝ => c * Real.exp (-x)) (Ioi 1) :=
    (integrableOn_exp_neg_Ioi 1).const_mul c
  change Integrable boseFinitePartLargeKernel (volume.restrict (Ioi 1))
  change Integrable (fun x : ℝ => c * Real.exp (-x))
    (volume.restrict (Ioi 1)) at hg
  apply hg.mono
  · exact (continuousOn_boseFinitePartLargeKernel.mono
      (fun x hx => by
        change 1 < x at hx
        change 0 < x
        linarith)).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change 1 < x at hx
    rw [Real.norm_eq_abs]
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hH : |boseLogKernel x| ≤ c * Real.exp (-x) := by
      simpa only [c] using abs_boseLogKernel_le_const_exp x hx.le
    calc
      |boseFinitePartLargeKernel x| = |boseLogKernel x| / x := by
        rw [boseFinitePartLargeKernel, abs_div, abs_of_pos hx0]
      _ ≤ |boseLogKernel x| := div_le_self (abs_nonneg _) (by linarith)
      _ ≤ c * Real.exp (-x) := hH
      _ = ‖c * Real.exp (-x)‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc0 (Real.exp_nonneg _))]

theorem tendsto_small_regularized_bose_integral :
    Tendsto (fun a : ℝ => ∫ x : ℝ in Ioc 0 1,
      x ^ a * boseFinitePartSmallKernel x) (𝓝[>] 0)
      (𝓝 (∫ x : ℝ in Ioc 0 1, boseFinitePartSmallKernel x)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ : ℝ => (1 : ℝ))
  · filter_upwards with a
    exact ((continuousOn_id.rpow_const (fun x hx => Or.inl hx.1.ne')).mul
      (continuousOn_boseFinitePartSmallKernel.mono
        (Ioc_subset_Ioi_self : Ioc (0 : ℝ) 1 ⊆ Ioi 0))).aestronglyMeasurable
          measurableSet_Ioc
  · filter_upwards [self_mem_nhdsWithin] with a ha0
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs, abs_mul]
    have hxa : 0 ≤ x ^ a := (Real.rpow_pos_of_pos hx.1 _).le
    rw [abs_of_nonneg hxa]
    calc
      x ^ a * |boseFinitePartSmallKernel x| ≤ x ^ a * 1 :=
        mul_le_mul_of_nonneg_left (abs_boseFinitePartSmallKernel_le_one x hx) hxa
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_right
        (Real.rpow_le_one hx.1.le hx.2 ha0.le) zero_le_one
      _ = 1 := by ring
  · change Integrable (fun _ : ℝ => (1 : ℝ))
      (volume.restrict (Ioc (0 : ℝ) 1))
    exact integrableOn_const (measure_Ioc_lt_top.ne)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hp : Tendsto (fun a : ℝ => x ^ a) (𝓝[>] 0) (𝓝 1) := by
      simpa using (Real.continuousAt_const_rpow (a := x) (b := 0) hx.1.ne').tendsto.mono_left
        nhdsWithin_le_nhds
    simpa using hp.mul_const (boseFinitePartSmallKernel x)

theorem tendsto_large_regularized_bose_integral :
    Tendsto (fun a : ℝ => ∫ x : ℝ in Ioi 1,
      x ^ (a - 1) * boseLogKernel x) (𝓝[>] 0)
      (𝓝 (∫ x : ℝ in Ioi 1, boseFinitePartLargeKernel x)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (bound := fun x : ℝ => |boseLogKernel x|)
  · filter_upwards with a
    exact ((continuousOn_id.rpow_const (fun x hx => Or.inl (by
      change 1 < x at hx
      exact (zero_lt_one.trans hx).ne'))).mul
        (((continuousOn_const.sub
          (Real.continuous_exp.comp_continuousOn continuousOn_neg)).log
            (fun x hx => by
              change 1 < x at hx
              apply (sub_pos.mpr ?_).ne'
              rw [← Real.exp_zero]
              exact Real.exp_lt_exp.mpr (by linarith))))).aestronglyMeasurable
                measurableSet_Ioi
  · filter_upwards [(eventually_le_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        nhdsWithin_le_nhds] with a ha
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change 1 < x at hx
    rw [Real.norm_eq_abs, abs_mul]
    have hp0 : 0 ≤ x ^ (a - 1) := Real.rpow_nonneg (by linarith) _
    rw [abs_of_nonneg hp0]
    calc
      x ^ (a - 1) * |boseLogKernel x| ≤ 1 * |boseLogKernel x| :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_one_of_one_le_of_nonpos hx.le (by linarith)) (abs_nonneg _)
      _ = |boseLogKernel x| := by ring
  · exact integrableOn_boseLogKernel_Ioi_one.norm
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change 1 < x at hx
    have hp : Tendsto (fun a : ℝ => x ^ (a - 1)) (𝓝[>] 0)
        (𝓝 x⁻¹) := by
      have hc : ContinuousAt (fun a : ℝ => x ^ (a - 1)) 0 := by
        fun_prop (disch := positivity)
      simpa [Real.rpow_neg_one] using hc.tendsto.mono_left nhdsWithin_le_nhds
    have hm := hp.mul_const (boseLogKernel x)
    simpa [boseFinitePartLargeKernel, div_eq_inv_mul, mul_comm] using hm

lemma integrableOn_small_weighted_kernel (a : ℝ) (ha : 0 ≤ a) :
    IntegrableOn (fun x : ℝ => x ^ a * boseFinitePartSmallKernel x) (Ioc 0 1) := by
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 0 1) :=
    integrableOn_const (measure_Ioc_lt_top.ne)
  change Integrable (fun x : ℝ => x ^ a * boseFinitePartSmallKernel x)
    (volume.restrict (Ioc 0 1))
  change Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioc 0 1)) at hone
  apply hone.mono
  · exact ((continuousOn_id.rpow_const (fun x hx => Or.inl hx.1.ne')).mul
      (continuousOn_boseFinitePartSmallKernel.mono
        (Ioc_subset_Ioi_self : Ioc (0 : ℝ) 1 ⊆ Ioi 0))).aestronglyMeasurable
          measurableSet_Ioc
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs, abs_mul]
    have hxa : 0 ≤ x ^ a := (Real.rpow_pos_of_pos hx.1 _).le
    rw [abs_of_nonneg hxa]
    calc
      x ^ a * |boseFinitePartSmallKernel x| ≤ x ^ a * 1 :=
        mul_le_mul_of_nonneg_left (abs_boseFinitePartSmallKernel_le_one x hx) hxa
      _ ≤ 1 := by simpa using Real.rpow_le_one hx.1.le hx.2 ha
      _ = ‖(1 : ℝ)‖ := by norm_num

lemma integrableOn_large_weighted_kernel (a : ℝ) (ha : a ≤ 1) :
    IntegrableOn (fun x : ℝ => x ^ (a - 1) * boseLogKernel x) (Ioi 1) := by
  have hH := integrableOn_boseLogKernel_Ioi_one.norm
  change Integrable (fun x : ℝ => x ^ (a - 1) * boseLogKernel x)
    (volume.restrict (Ioi 1))
  change Integrable (fun x : ℝ => ‖boseLogKernel x‖)
    (volume.restrict (Ioi 1)) at hH
  apply hH.mono
  · exact ((continuousOn_id.rpow_const (fun x hx => Or.inl (by
      change 1 < x at hx
      exact (zero_lt_one.trans hx).ne'))).mul
        (((continuousOn_const.sub
          (Real.continuous_exp.comp_continuousOn continuousOn_neg)).log
            (fun x hx => by
              change 1 < x at hx
              apply (sub_pos.mpr ?_).ne'
              rw [← Real.exp_zero]
              exact Real.exp_lt_exp.mpr (by linarith))))).aestronglyMeasurable
                measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change 1 < x at hx
    rw [Real.norm_eq_abs, abs_mul]
    have hp0 : 0 ≤ x ^ (a - 1) := Real.rpow_nonneg (by linarith) _
    rw [abs_of_nonneg hp0, Real.norm_eq_abs]
    calc
      x ^ (a - 1) * |boseLogKernel x| ≤ 1 * |boseLogKernel x| :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_one_of_one_le_of_nonpos hx.le (by linarith)) (abs_nonneg _)
      _ = |boseLogKernel x| := one_mul _
      _ = ‖‖boseLogKernel x‖‖ := by simp [Real.norm_eq_abs]

lemma integrableOn_rpow_sub_one_mul_log_Ioc (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => x ^ (a - 1) * Real.log x) (Ioc 0 1) := by
  have hg0 : IntegrableOn (fun x : ℝ => x ^ (a / 2 - 1)) (Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num)).mpr (by linarith)
  have hg := hg0.const_mul (2 / a)
  change Integrable (fun x : ℝ => (2 / a) * x ^ (a / 2 - 1))
    (volume.restrict (Ioo 0 1)) at hg
  have hfIoo : IntegrableOn (fun x : ℝ => x ^ (a - 1) * Real.log x)
      (Ioo 0 1) := by
    change Integrable (fun x : ℝ => x ^ (a - 1) * Real.log x)
      (volume.restrict (Ioo 0 1))
    apply hg.mono
    · have hclog : ContinuousOn Real.log (Ioo (0 : ℝ) 1) := by
        intro x hx
        exact (Real.continuousAt_log hx.1.ne').continuousWithinAt
      exact ((continuousOn_id.rpow_const (fun x hx => Or.inl hx.1.ne')).mul
        hclog).aestronglyMeasurable measurableSet_Ioo
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      rw [Real.norm_eq_abs, abs_mul]
      have hp0 : 0 ≤ x ^ (a - 1) := Real.rpow_nonneg hx.1.le _
      rw [abs_of_nonneg hp0]
      have hlog0 : Real.log x ≤ 0 := Real.log_nonpos hx.1.le hx.2.le
      rw [abs_of_nonpos hlog0]
      have hlog := Real.log_le_rpow_div (inv_nonneg.mpr hx.1.le)
        (show 0 < a / 2 by positivity)
      rw [Real.log_inv] at hlog
      have hpow : x ^ (a - 1) * ((x⁻¹) ^ (a / 2) / (a / 2)) =
          (2 / a) * x ^ (a / 2 - 1) := by
        rw [Real.inv_rpow hx.1.le]
        rw [← Real.rpow_neg hx.1.le]
        calc
          x ^ (a - 1) * (x ^ (-(a / 2)) / (a / 2)) =
              (2 / a) * (x ^ (a - 1) * x ^ (-(a / 2))) := by
            field_simp [ha.ne']
          _ = (2 / a) * x ^ ((a - 1) + (-(a / 2))) := by
            rw [Real.rpow_add hx.1]
          _ = (2 / a) * x ^ (a / 2 - 1) := by
            congr 2
            ring
      calc
        x ^ (a - 1) * -Real.log x ≤
            x ^ (a - 1) * ((x⁻¹) ^ (a / 2) / (a / 2)) :=
          mul_le_mul_of_nonneg_left hlog hp0
        _ = (2 / a) * x ^ (a / 2 - 1) := hpow
        _ = ‖(2 / a) * x ^ (a / 2 - 1)‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg]
          exact mul_nonneg (div_nonneg (by norm_num) ha.le)
            (Real.rpow_nonneg hx.1.le _)
  exact IntegrableOn.congr_set_ae hfIoo Ioo_ae_eq_Ioc.symm

lemma tendsto_rpow_nhdsGT_zero_of_pos (a : ℝ) (ha : 0 < a) :
    Tendsto (fun x : ℝ => x ^ a) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop ha).comp tendsto_inv_nhdsGT_zero
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  change 0 < x at hx
  simp only [Function.comp_apply]
  rw [Real.inv_rpow hx.le, Real.rpow_neg hx.le]
  simp

lemma integral_rpow_sub_one_mul_log_Ioc (a : ℝ) (ha : 0 < a) :
    ∫ x : ℝ in Ioc 0 1, x ^ (a - 1) * Real.log x = -1 / a ^ 2 := by
  let F : ℝ → ℝ := fun x => x ^ a * (Real.log x / a - 1 / a ^ 2)
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt F (x ^ (a - 1) * Real.log x) x := by
    intro x hx
    have hp := Real.hasDerivAt_rpow_const (x := x) (p := a) (Or.inl hx.1.ne')
    have hl := (Real.hasDerivAt_log hx.1.ne').div_const a
    have hinner := hl.sub_const (1 / a ^ 2)
    dsimp [F]
    refine (hp.mul hinner).congr_deriv ?_
    have hxpow : x ^ a * x⁻¹ = x ^ (a - 1) := by
      rw [← Real.rpow_neg_one x, ← Real.rpow_add hx.1]
      congr 1
    have hxterm : x ^ a * (x⁻¹ / a) = x ^ (a - 1) / a := by
      calc
        x ^ a * (x⁻¹ / a) = (x ^ a * x⁻¹) / a := by ring
        _ = x ^ (a - 1) / a := by rw [hxpow]
    rw [hxterm]
    field_simp [ha.ne']
    ring
  have hint : IntervalIntegrable (fun x : ℝ =>
      x ^ (a - 1) * Real.log x) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      (integrableOn_rpow_sub_one_mul_log_Ioc a ha)
  have hzero : Tendsto F (𝓝[>] 0) (𝓝 0) := by
    have hlogpow := tendsto_log_mul_rpow_nhdsGT_zero ha
    have hterm1 : Tendsto (fun x : ℝ =>
        x ^ a * Real.log x / a) (𝓝[>] 0) (𝓝 0) := by
      simpa [mul_comm, mul_div_assoc] using hlogpow.div_const a
    have hterm2 : Tendsto (fun x : ℝ => x ^ a / a ^ 2)
        (𝓝[>] 0) (𝓝 0) := by
      simpa using (tendsto_rpow_nhdsGT_zero_of_pos a ha).div_const (a ^ 2)
    convert hterm1.sub hterm2 using 1
    · funext x
      dsimp [F]
      ring
    · ring_nf
  have hone : Tendsto F (𝓝[<] 1) (𝓝 (-1 / a ^ 2)) := by
    have hc : ContinuousAt F 1 := by
      dsimp [F]
      fun_prop (disch := norm_num)
    have ht : Tendsto F (𝓝[<] (1 : ℝ)) (𝓝 (F 1)) :=
      hc.tendsto.mono_left nhdsWithin_le_nhds
    convert ht using 1
    simp [F]
    ring
  have hres := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (a := 0) (b := 1) zero_lt_one hderiv hint hzero hone
  rw [intervalIntegral.integral_of_le zero_le_one] at hres
  simpa using hres

/-- On the positive half-line, the Bose kernel splits into its regularized
small-scale part and the explicit logarithmic singularity. -/
lemma boseLogKernel_eq_negativeLaplaceKernel_add_log
    (x : ℝ) (hx : 0 < x) :
    boseLogKernel x = negativeLaplaceKernel x + Real.log x := by
  have hnum : 1 - Real.exp (-x) ≠ 0 := by
    apply (sub_pos.mpr ?_).ne'
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  rw [boseLogKernel, negativeLaplaceKernel, Real.log_div hnum hx.ne']
  ring

/-- The two finite-part kernels differ exactly by `log x / x` on the positive
half-line. -/
lemma boseFinitePartLargeKernel_eq_small_add_log_div
    (x : ℝ) (hx : 0 < x) :
    boseFinitePartLargeKernel x =
      boseFinitePartSmallKernel x + Real.log x / x := by
  unfold boseFinitePartLargeKernel boseFinitePartSmallKernel
  rw [boseLogKernel_eq_negativeLaplaceKernel_add_log x hx]
  ring

/-- Weighted form of the small-scale Bose decomposition used to split its
Mellin integral at one. -/
lemma small_weighted_bose_decomposition (a x : ℝ) (hx : 0 < x) :
    x ^ (a - 1) * boseLogKernel x =
      x ^ a * boseFinitePartSmallKernel x +
        x ^ (a - 1) * Real.log x := by
  rw [boseLogKernel_eq_negativeLaplaceKernel_add_log x hx]
  have hxpow : x ^ a / x = x ^ (a - 1) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one x, ← Real.rpow_add hx]
    congr 1
  unfold boseFinitePartSmallKernel
  have hterm : x ^ a * (negativeLaplaceKernel x / x) =
      x ^ (a - 1) * negativeLaplaceKernel x := by
    calc
      x ^ a * (negativeLaplaceKernel x / x) =
          (x ^ a / x) * negativeLaplaceKernel x := by ring
      _ = x ^ (a - 1) * negativeLaplaceKernel x := by rw [hxpow]
  rw [hterm]
  ring

lemma integrableOn_small_weighted_bose (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => x ^ (a - 1) * boseLogKernel x) (Ioc 0 1) := by
  have hsum := (integrableOn_small_weighted_kernel a ha.le).add
    (integrableOn_rpow_sub_one_mul_log_Ioc a ha)
  apply hsum.congr_fun
  · intro x hx
    exact (small_weighted_bose_decomposition a x hx.1).symm
  · exact measurableSet_Ioc

/-- Split the regularized Mellin integral at one.  The double-pole subtraction
is exactly the elementary integral of `x^(a-1) log x` over `(0,1]`. -/
lemma bose_mellin_regularized_split (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    (∫ x : ℝ in Ioi 0, x ^ (a - 1) * boseLogKernel x) + 1 / a ^ 2 =
      (∫ x : ℝ in Ioc 0 1, x ^ a * boseFinitePartSmallKernel x) +
        ∫ x : ℝ in Ioi 1, x ^ (a - 1) * boseLogKernel x := by
  let f : ℝ → ℝ := fun x => x ^ (a - 1) * boseLogKernel x
  have hfsmall : IntegrableOn f (Ioc 0 1) := by
    simpa [f] using integrableOn_small_weighted_bose a ha
  have hflarge : IntegrableOn f (Ioi 1) := by
    simpa [f] using integrableOn_large_weighted_kernel a ha1
  have hdis : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) := by
    rw [Set.disjoint_left]
    intro x hxsmall hxlarge
    exact (not_lt_of_ge hxsmall.2) hxlarge
  have hsplit := setIntegral_union₀ hdis.aedisjoint
    measurableSet_Ioi.nullMeasurableSet hfsmall hflarge
  rw [Ioc_union_Ioi_eq_Ioi zero_le_one] at hsplit
  have hsmall : (∫ x : ℝ in Ioc 0 1, f x) =
      (∫ x : ℝ in Ioc 0 1, x ^ a * boseFinitePartSmallKernel x) +
        ∫ x : ℝ in Ioc 0 1, x ^ (a - 1) * Real.log x := by
    rw [show (∫ x : ℝ in Ioc 0 1, f x) =
        ∫ x : ℝ in Ioc 0 1,
          x ^ a * boseFinitePartSmallKernel x +
            x ^ (a - 1) * Real.log x by
      exact setIntegral_congr_fun measurableSet_Ioc (fun x hx => by
        dsimp [f]
        exact small_weighted_bose_decomposition a x hx.1)]
    exact integral_add
      (integrableOn_small_weighted_kernel a ha.le)
      (integrableOn_rpow_sub_one_mul_log_Ioc a ha)
  rw [hsmall, integral_rpow_sub_one_mul_log_Ioc a ha] at hsplit
  dsimp [f] at hsplit
  rw [hsplit]
  ring

/-- For `0 < a ≤ 1`, the Gamma--zeta finite part equals the two convergent
regularized integrals before taking the limit `a → 0+`. -/
lemma gamma_zeta_finitePart_eq_regularized_integrals
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    -Real.Gamma a * (riemannZeta ((1 + a : ℝ) : ℂ)).re + 1 / a ^ 2 =
      (∫ x : ℝ in Ioc 0 1, x ^ a * boseFinitePartSmallKernel x) +
        ∫ x : ℝ in Ioi 1, x ^ (a - 1) * boseLogKernel x := by
  rw [show (1 + a : ℝ) = a + 1 by ring]
  rw [← bose_mellin_regularized_split a ha ha1]
  rw [show (fun x : ℝ => x ^ (a - 1) * boseLogKernel x) =
      fun x : ℝ => x ^ (a - 1) * Real.log (1 - Real.exp (-x)) by
    funext x
    rfl]
  rw [bose_mellin_integral_zeta a ha]

/-- The real finite-part integral of the logarithmic Bose kernel. -/
theorem boseFinitePartIntegral_eq_gammaZetaConstant :
    (∫ x : ℝ in Ioc 0 1, boseFinitePartSmallKernel x) +
        ∫ x : ℝ in Ioi 1, boseFinitePartLargeKernel x =
      gammaZetaConstant := by
  let J : ℝ → ℝ := fun a =>
    (∫ x : ℝ in Ioc 0 1, x ^ a * boseFinitePartSmallKernel x) +
      ∫ x : ℝ in Ioi 1, x ^ (a - 1) * boseLogKernel x
  have hJ : Tendsto J (𝓝[>] 0)
      (𝓝 ((∫ x : ℝ in Ioc 0 1, boseFinitePartSmallKernel x) +
        ∫ x : ℝ in Ioi 1, boseFinitePartLargeKernel x)) := by
    simpa [J] using tendsto_small_regularized_bose_integral.add
      tendsto_large_regularized_bose_integral
  have heq : (fun a : ℝ =>
      -Real.Gamma a * (riemannZeta ((1 + a : ℝ) : ℂ)).re + 1 / a ^ 2) =ᶠ[𝓝[>] 0]
      J := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        nhdsWithin_le_nhds] with a ha ha1
    exact gamma_zeta_finitePart_eq_regularized_integrals a ha ha1
  have hJ' : Tendsto J (𝓝[>] 0) (𝓝 gammaZetaConstant) :=
    tendsto_realGamma_mul_zeta_finitePart.congr' heq
  exact tendsto_nhds_unique hJ hJ'

end Fabius
