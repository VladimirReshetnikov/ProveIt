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
periodic-mean and Fourier-coefficient calculations. Their integrability is
recorded for arbitrary cutoffs, together with the exact logarithmic correction
incurred when the cutoff moves.  In particular, the cutoff-indexed finite part
defined below is independent of every positive choice of split point and is
always equal to `gammaZetaConstant`.  Both finite-part kernels are strictly
negative on the positive half-line, and the small-kernel integral is strictly
negative up to every positive cutoff.  The finite-part identity also proves
the strict sign of `gammaZetaConstant` and an unconditional strict upper bound
for the first Stieltjes constant.
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

/-- The regularized small-scale finite-part kernel is strictly negative at
every positive argument. -/
theorem boseFinitePartSmallKernel_neg (x : ℝ) (hx : 0 < x) :
    boseFinitePartSmallKernel x < 0 := by
  unfold boseFinitePartSmallKernel
  exact div_neg_of_neg_of_pos (negativeLaplaceKernel_neg x hx) hx

/-- The logarithmic Bose kernel is strictly negative at every positive
argument. -/
theorem boseLogKernel_neg (x : ℝ) (hx : 0 < x) :
    boseLogKernel x < 0 := by
  unfold boseLogKernel
  exact Real.log_neg
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hx)))
    (sub_lt_self 1 (Real.exp_pos (-x)))

/-- The large-scale finite-part kernel is strictly negative at every positive
argument. -/
theorem boseFinitePartLargeKernel_neg (x : ℝ) (hx : 0 < x) :
    boseFinitePartLargeKernel x < 0 := by
  unfold boseFinitePartLargeKernel
  exact div_neg_of_neg_of_pos (boseLogKernel_neg x hx) hx

/-- The uncorrected split integral at the cutoff `c`.  Changing `c` moves a
compact interval from the large kernel to the small kernel, so this quantity
itself changes by an explicit logarithmic square. -/
noncomputable def boseFinitePartSplitIntegral (c : ℝ) : ℝ :=
  (∫ x : ℝ in Ioc 0 c, boseFinitePartSmallKernel x) +
    ∫ x : ℝ in Ioi c, boseFinitePartLargeKernel x

/-- The cutoff-normalized finite part of the logarithmic Bose kernel.  The
added `log(c)² / 2` is exactly the correction that makes this independent of
the positive cutoff `c`. -/
noncomputable def boseFinitePartIntegralAtCutoff (c : ℝ) : ℝ :=
  boseFinitePartSplitIntegral c + (Real.log c) ^ 2 / 2

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

/-- The regularized small-scale kernel is continuous on the positive
half-line. -/
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

/-- The small finite-part kernel is integrable up to every real cutoff. When
the cutoff is nonpositive the interval is empty; no positivity hypothesis is
therefore needed. -/
lemma integrableOn_boseFinitePartSmallKernel_Ioc (c : ℝ) :
    IntegrableOn boseFinitePartSmallKernel (Ioc 0 c) := by
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 0 c) :=
    integrableOn_const (measure_Ioc_lt_top.ne)
  change Integrable boseFinitePartSmallKernel (volume.restrict (Ioc 0 c))
  change Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioc 0 c)) at hone
  apply hone.mono
  · exact (continuousOn_boseFinitePartSmallKernel.mono
      (Ioc_subset_Ioi_self : Ioc (0 : ℝ) c ⊆ Ioi 0)).aestronglyMeasurable
        measurableSet_Ioc
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs]
    simpa only [norm_one] using
      abs_boseFinitePartSmallKernel_le_one_of_pos x hx.1

/-- Unit-cutoff compatibility form of
`integrableOn_boseFinitePartSmallKernel_Ioc`. -/
lemma integrableOn_boseFinitePartSmallKernel :
    IntegrableOn boseFinitePartSmallKernel (Ioc 0 1) := by
  simpa using integrableOn_boseFinitePartSmallKernel_Ioc 1

/-- The regularized small-kernel integral is strictly negative up to every
positive cutoff. -/
lemma integral_boseFinitePartSmallKernel_Ioc_neg
    (c : ℝ) (hc : 0 < c) :
    (∫ x : ℝ in Ioc 0 c, boseFinitePartSmallKernel x) < 0 := by
  have hint : IntegrableOn boseFinitePartSmallKernel (Ioc (0 : ℝ) c) :=
    integrableOn_boseFinitePartSmallKernel_Ioc c
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) c)]
      (fun x : ℝ ↦ -boseFinitePartSmallKernel x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact neg_nonneg.mpr (boseFinitePartSmallKernel_neg x hx.1).le
  have hpos : 0 < ∫ x : ℝ in Ioc 0 c, -boseFinitePartSmallKernel x := by
    rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hnonneg hint.neg]
    have hsubset : Ioc (0 : ℝ) c ⊆
        Function.support (fun x : ℝ ↦ -boseFinitePartSmallKernel x) ∩ Ioc 0 c := by
      intro x hx
      refine ⟨?_, hx⟩
      exact (neg_pos.mpr (boseFinitePartSmallKernel_neg x hx.1)).ne'
    calc
      0 < volume (Ioc (0 : ℝ) c) := by
        rw [Real.volume_Ioc, ENNReal.ofReal_pos]
        simpa using hc
      _ ≤ volume (Function.support (fun x : ℝ ↦ -boseFinitePartSmallKernel x) ∩
          Ioc 0 c) := measure_mono hsubset
  rw [MeasureTheory.integral_neg] at hpos
  exact neg_pos.mp hpos

/-- Compatibility form of `abs_boseFinitePartSmallKernel_le_one_of_pos` on the
small integration interval. -/
lemma abs_boseFinitePartSmallKernel_le_one
    (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) :
    |boseFinitePartSmallKernel x| ≤ 1 :=
  abs_boseFinitePartSmallKernel_le_one_of_pos x hx.1

/-- The large-scale finite-part kernel is continuous on the positive
half-line. -/
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

/-- The logarithmic Bose kernel is integrable beyond every positive cutoff. -/
lemma integrableOn_boseLogKernel_Ioi_of_pos (c : ℝ) (hc : 0 < c) :
    IntegrableOn boseLogKernel (Ioi c) := by
  let C : ℝ := 1 / (1 - Real.exp (-c))
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact (one_div_pos.mpr
      (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))).le
  have hg : IntegrableOn (fun x : ℝ => C * Real.exp (-x)) (Ioi c) :=
    (integrableOn_exp_neg_Ioi c).const_mul C
  change Integrable boseLogKernel (volume.restrict (Ioi c))
  change Integrable (fun x : ℝ => C * Real.exp (-x))
    (volume.restrict (Ioi c)) at hg
  apply hg.mono
  · have hsubset : Ioi c ⊆ Ioi 0 := by
      intro x hx
      exact hc.trans hx
    exact (continuousOn_boseLogKernel.mono hsubset).aestronglyMeasurable
      measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs]
    refine (abs_boseLogKernel_le_const_exp_of_le c x hc hx.le).trans_eq ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC0 (Real.exp_nonneg _))]

/-- Unit-cutoff compatibility form of
`integrableOn_boseLogKernel_Ioi_of_pos`. -/
lemma integrableOn_boseLogKernel_Ioi_one :
    IntegrableOn boseLogKernel (Ioi 1) := by
  simpa using integrableOn_boseLogKernel_Ioi_of_pos 1 (by norm_num)

/-- The large finite-part kernel is integrable beyond every positive cutoff. -/
lemma integrableOn_boseFinitePartLargeKernel_Ioi_of_pos
    (c : ℝ) (hc : 0 < c) :
    IntegrableOn boseFinitePartLargeKernel (Ioi c) := by
  let C : ℝ := 1 / (1 - Real.exp (-c))
  let D : ℝ := C / c
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact (one_div_pos.mpr
      (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))).le
  have hD0 : 0 ≤ D := div_nonneg hC0 hc.le
  have hg : IntegrableOn (fun x : ℝ => D * Real.exp (-x)) (Ioi c) :=
    (integrableOn_exp_neg_Ioi c).const_mul D
  change Integrable boseFinitePartLargeKernel (volume.restrict (Ioi c))
  change Integrable (fun x : ℝ => D * Real.exp (-x))
    (volume.restrict (Ioi c)) at hg
  apply hg.mono
  · exact (continuousOn_boseFinitePartLargeKernel.mono
      (fun x hx => by
        exact hc.trans hx)).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs]
    have hx0 : 0 < x := hc.trans hx
    have hH : |boseLogKernel x| ≤ C * Real.exp (-x) := by
      simpa only [C] using abs_boseLogKernel_le_const_exp_of_le c x hc hx.le
    calc
      |boseFinitePartLargeKernel x| = |boseLogKernel x| / x := by
        rw [boseFinitePartLargeKernel, abs_div, abs_of_pos hx0]
      _ ≤ (C * Real.exp (-x)) / x :=
        (div_le_div_iff_of_pos_right hx0).2 hH
      _ ≤ (C * Real.exp (-x)) / c :=
        div_le_div_of_nonneg_left (mul_nonneg hC0 (Real.exp_nonneg _)) hc hx.le
      _ = D * Real.exp (-x) := by
        dsimp [D]
        ring
      _ = ‖D * Real.exp (-x)‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hD0 (Real.exp_nonneg _))]

/-- Unit-cutoff compatibility form of
`integrableOn_boseFinitePartLargeKernel_Ioi_of_pos`. -/
lemma integrableOn_boseFinitePartLargeKernel :
    IntegrableOn boseFinitePartLargeKernel (Ioi 1) := by
  simpa using integrableOn_boseFinitePartLargeKernel_Ioi_of_pos 1 (by norm_num)

/-- As the Mellin exponent tends to zero from the right, the small weighted
integral converges to the unweighted small finite-part integral. -/
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

/-- As the Mellin exponent tends to zero from the right, the large weighted
integral converges to the unweighted large finite-part integral. -/
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

/-- For every nonnegative exponent `a`, the small regularized kernel weighted
by `x ^ a` is integrable on `(0, 1]`. -/
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

/-- For every exponent `a ≤ 1`, the large Bose Mellin integrand is
integrable on `(1, ∞)`. -/
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

/-- For `a > 0`, the elementary singular term
`x ^ (a - 1) * log x` is integrable on `(0, 1]`. -/
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

/-- For `a > 0`, the function `x ↦ x ^ a` tends to zero as `x` tends to
zero from the right. -/
lemma tendsto_rpow_nhdsGT_zero_of_pos (a : ℝ) (ha : 0 < a) :
    Tendsto (fun x : ℝ => x ^ a) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop ha).comp tendsto_inv_nhdsGT_zero
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  change 0 < x at hx
  simp only [Function.comp_apply]
  rw [Real.inv_rpow hx.le, Real.rpow_neg hx.le]
  simp

/-- For `a > 0`, the elementary logarithmic Mellin integral over `(0, 1]`
equals `-1 / a ^ 2`. -/
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
  rw [boseLogKernel, negativeLaplaceKernel_eq_log_sub_log x hx, sub_add_cancel]

/-- The two finite-part kernels differ exactly by `log x / x` on the positive
half-line. -/
lemma boseFinitePartLargeKernel_eq_small_add_log_div
    (x : ℝ) (hx : 0 < x) :
    boseFinitePartLargeKernel x =
      boseFinitePartSmallKernel x + Real.log x / x := by
  unfold boseFinitePartLargeKernel boseFinitePartSmallKernel
  rw [boseLogKernel_eq_negativeLaplaceKernel_add_log x hx]
  ring

/-- The elementary transition term between two positive cutoffs. The formula
also covers the degenerate endpoint `a = b`. -/
lemma integral_log_div_Ioc (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∫ x : ℝ in Ioc a b, Real.log x / x =
      (Real.log b) ^ 2 / 2 - (Real.log a) ^ 2 / 2 := by
  have hpos : ∀ x ∈ uIcc a b, 0 < x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact ha.trans_le hx.1
  have hderiv : ∀ x ∈ uIcc a b,
      HasDerivAt (fun y : ℝ => (Real.log y) ^ 2 / 2) (Real.log x / x) x := by
    intro x hx
    refine (((Real.hasDerivAt_log (hpos x hx).ne').pow 2).div_const 2).congr_deriv ?_
    ring
  have hcont : ContinuousOn (fun x : ℝ => Real.log x / x) (uIcc a b) := by
    intro x hx
    have hx0 := hpos x hx
    exact ((Real.continuousAt_log hx0.ne').div continuousAt_id hx0.ne').continuousWithinAt
  rw [← intervalIntegral.integral_of_le hab]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    hderiv hcont.intervalIntegrable

/-- Moving the split point across a positive compact interval changes the
large-minus-small kernel integral by the explicit logarithmic square term. -/
lemma integral_boseFinitePartLargeKernel_sub_small_Ioc
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∫ x : ℝ in Ioc a b,
        (boseFinitePartLargeKernel x - boseFinitePartSmallKernel x) =
      (Real.log b) ^ 2 / 2 - (Real.log a) ^ 2 / 2 := by
  calc
    (∫ x : ℝ in Ioc a b,
        (boseFinitePartLargeKernel x - boseFinitePartSmallKernel x)) =
        ∫ x : ℝ in Ioc a b, Real.log x / x := by
      exact setIntegral_congr_fun measurableSet_Ioc (fun x hx => by
        rw [boseFinitePartLargeKernel_eq_small_add_log_div x
          (ha.trans hx.1)]
        ring)
    _ = (Real.log b) ^ 2 / 2 - (Real.log a) ^ 2 / 2 :=
      integral_log_div_Ioc a b ha hab

/-- Splitting the small-kernel integral at a positive intermediate cutoff. -/
lemma integral_boseFinitePartSmallKernel_Ioc_split
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ x : ℝ in Ioc 0 b, boseFinitePartSmallKernel x) =
      (∫ x : ℝ in Ioc 0 a, boseFinitePartSmallKernel x) +
        ∫ x : ℝ in Ioc a b, boseFinitePartSmallKernel x := by
  have h0a := integrableOn_boseFinitePartSmallKernel_Ioc a
  have hab' : IntegrableOn boseFinitePartSmallKernel (Ioc a b) :=
    (integrableOn_boseFinitePartSmallKernel_Ioc b).mono_set (fun x hx =>
      ⟨ha.trans hx.1, hx.2⟩)
  have hsplit := setIntegral_union
    (Ioc_disjoint_Ioc_of_le (a := (0 : ℝ)) (b := a) (c := a) (d := b) le_rfl)
    measurableSet_Ioc h0a hab'
  rwa [Ioc_union_Ioc_eq_Ioc ha.le hab] at hsplit

/-- Splitting the large-kernel tail at a later positive cutoff. -/
lemma integral_boseFinitePartLargeKernel_Ioi_split
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ x : ℝ in Ioi a, boseFinitePartLargeKernel x) =
      (∫ x : ℝ in Ioc a b, boseFinitePartLargeKernel x) +
        ∫ x : ℝ in Ioi b, boseFinitePartLargeKernel x := by
  have ha' := integrableOn_boseFinitePartLargeKernel_Ioi_of_pos a ha
  have hab' : IntegrableOn boseFinitePartLargeKernel (Ioc a b) :=
    ha'.mono_set Ioc_subset_Ioi_self
  have hb' := integrableOn_boseFinitePartLargeKernel_Ioi_of_pos b
    (ha.trans_le hab)
  have hsplit := setIntegral_union
    (Ioc_disjoint_Ioi_same (a := a) (b := b))
    measurableSet_Ioi hab' hb'
  rwa [Ioc_union_Ioi_eq_Ioi hab] at hsplit

/-- Exact change in the uncorrected split integral when a positive cutoff is
moved to the right. -/
theorem boseFinitePartSplitIntegral_change_of_le
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    boseFinitePartSplitIntegral b - boseFinitePartSplitIntegral a =
      (Real.log a) ^ 2 / 2 - (Real.log b) ^ 2 / 2 := by
  have hsmall := integral_boseFinitePartSmallKernel_Ioc_split a b ha hab
  have hlarge := integral_boseFinitePartLargeKernel_Ioi_split a b ha hab
  have hsmallab : IntegrableOn boseFinitePartSmallKernel (Ioc a b) :=
    (integrableOn_boseFinitePartSmallKernel_Ioc b).mono_set (fun x hx =>
      ⟨ha.trans hx.1, hx.2⟩)
  have hlargeab : IntegrableOn boseFinitePartLargeKernel (Ioc a b) :=
    (integrableOn_boseFinitePartLargeKernel_Ioi_of_pos a ha).mono_set
      Ioc_subset_Ioi_self
  have htransition :=
    integral_boseFinitePartLargeKernel_sub_small_Ioc a b ha hab
  rw [integral_sub hlargeab hsmallab] at htransition
  unfold boseFinitePartSplitIntegral
  rw [hsmall, hlarge]
  linarith

/-- Exact change in the uncorrected split integral between any two positive
cutoffs, with no ordering hypothesis. -/
theorem boseFinitePartSplitIntegral_change
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    boseFinitePartSplitIntegral b - boseFinitePartSplitIntegral a =
      (Real.log a) ^ 2 / 2 - (Real.log b) ^ 2 / 2 := by
  rcases le_total a b with hab | hba
  · exact boseFinitePartSplitIntegral_change_of_le a b ha hab
  · have h := boseFinitePartSplitIntegral_change_of_le b a hb hba
    linarith

/-- The normalized logarithmic Bose finite part is independent of the choice
of positive cutoff. -/
theorem boseFinitePartIntegralAtCutoff_eq
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    boseFinitePartIntegralAtCutoff a =
      boseFinitePartIntegralAtCutoff b := by
  have h := boseFinitePartSplitIntegral_change a b ha hb
  unfold boseFinitePartIntegralAtCutoff
  linarith

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

/-- For every positive exponent, the unsplit Bose Mellin integrand is
integrable on `(0, 1]`. -/
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

/-- The Euler--Stieltjes combination represented by the finite-part integral
is strictly negative. -/
theorem gammaZetaConstant_neg : gammaZetaConstant < 0 := by
  rw [← boseFinitePartIntegral_eq_gammaZetaConstant]
  exact add_neg_of_neg_of_nonpos
    (integral_boseFinitePartSmallKernel_Ioc_neg 1 (by norm_num))
    (MeasureTheory.setIntegral_nonpos measurableSet_Ioi
      (fun x hx ↦ (boseFinitePartLargeKernel_neg x (zero_lt_one.trans hx)).le))

/-- The strict unconditional bound
`γ₁ < π² / 12 - γ² / 2` for the first Stieltjes constant. -/
theorem firstStieltjesConstant_lt :
    firstStieltjesConstant <
      Real.pi ^ 2 / 12 - Real.eulerMascheroniConstant ^ 2 / 2 := by
  have h := gammaZetaConstant_neg
  unfold gammaZetaConstant at h
  linarith

/-- Every positive cutoff gives the same finite part, namely the
Euler--Stieltjes constant `gammaZetaConstant`. -/
theorem boseFinitePartIntegralAtCutoff_eq_gammaZetaConstant
    (c : ℝ) (hc : 0 < c) :
    boseFinitePartIntegralAtCutoff c = gammaZetaConstant := by
  calc
    boseFinitePartIntegralAtCutoff c =
        boseFinitePartIntegralAtCutoff 1 :=
      boseFinitePartIntegralAtCutoff_eq c 1 hc (by norm_num)
    _ = (∫ x : ℝ in Ioc 0 1, boseFinitePartSmallKernel x) +
        ∫ x : ℝ in Ioi 1, boseFinitePartLargeKernel x := by
      simp [boseFinitePartIntegralAtCutoff, boseFinitePartSplitIntegral]
    _ = gammaZetaConstant := boseFinitePartIntegral_eq_gammaZetaConstant

/-- The raw split integral at a positive cutoff `c` differs from
`gammaZetaConstant` by exactly `-log(c)² / 2`. -/
theorem boseFinitePartSplitIntegral_eq_gammaZetaConstant_sub
    (c : ℝ) (hc : 0 < c) :
    boseFinitePartSplitIntegral c =
      gammaZetaConstant - (Real.log c) ^ 2 / 2 := by
  have h := boseFinitePartIntegralAtCutoff_eq_gammaZetaConstant c hc
  unfold boseFinitePartIntegralAtCutoff at h
  linarith

/-- Expanded arbitrary-cutoff form of the logarithmic Bose finite-part
identity.  The logarithmic square is the exact correction for moving the split
away from one. -/
theorem boseFinitePartIntegral_eq_gammaZetaConstant_of_pos
    (c : ℝ) (hc : 0 < c) :
    (∫ x : ℝ in Ioc 0 c, boseFinitePartSmallKernel x) +
        (∫ x : ℝ in Ioi c, boseFinitePartLargeKernel x) +
          (Real.log c) ^ 2 / 2 = gammaZetaConstant := by
  simpa [boseFinitePartIntegralAtCutoff, boseFinitePartSplitIntegral] using
    boseFinitePartIntegralAtCutoff_eq_gammaZetaConstant c hc

end Fabius
