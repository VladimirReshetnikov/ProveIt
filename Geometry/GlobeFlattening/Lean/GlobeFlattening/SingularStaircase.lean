import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Instances.CantorSet

/-!
# Singular staircases close to the identity

Measuring preimages of lower intervals under a measurable injection into
the null Cantor set gives a continuous distribution function. It is locally
constant off the Cantor set. Finite sums of scaled copies approximate the
clamped identity and have derivative zero almost everywhere.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal NNReal Pointwise

namespace GlobeFlattening

noncomputable section

private theorem volume_cantorSet : volume cantorSet = 0 := by
  have hsplit : (3 : ℝ≥0) • cantorSet = cantorSet ∪ ((2 + · : ℝ → ℝ) '' cantorSet) := by
    nth_rw 1 [cantorSet_eq_union_halves, smul_set_union]
    simp only [← image_smul, image_image, NNReal.smul_def, NNReal.coe_ofNat, smul_eq_mul,
      mul_div_cancel₀ _ (by norm_num : (3 : ℝ) ≠ 0), image_id']
  have hle : (3 : ℝ≥0∞) * volume cantorSet ≤ 2 * volume cantorSet := by
    rw [← (by simp : volume ((3 : ℝ≥0) • cantorSet) = 3 * volume cantorSet), hsplit]
    simpa [image_add_left, measure_preimage_add, two_mul] using
      measure_union_le (μ := volume) cantorSet ((2 + · : ℝ → ℝ) '' cantorSet)
  by_contra hn
  exact (not_lt_of_ge hle) (ENNReal.mul_lt_mul_left hn isCompact_cantorSet.measure_lt_top.ne (by norm_num))

theorem exists_singular_staircase : ∃ f : ℝ → ℝ,
    Continuous f ∧ Monotone f ∧ (∀ x ≤ 0, f x = 0) ∧ (∀ x ≥ 1, f x = 1) ∧
      (∀ᵐ x ∂volume, HasDerivAt f 0 x) := by
  obtain ⟨code, hcode, hcode_inj⟩ := MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated ℝ
  let embed (x : ℝ) : ℝ := (cantorSetHomeomorphNatToBool.symm (code x) : cantorSet)
  have hm : Measurable embed :=
    (continuous_subtype_val.comp cantorSetHomeomorphNatToBool.symm.continuous).measurable.comp hcode
  have hi : Function.Injective embed :=
    Subtype.val_injective.comp (cantorSetHomeomorphNatToBool.symm.injective.comp hcode_inj)
  let ν := volume.restrict (Ico (0 : ℝ) 1)
  letI : IsProbabilityMeasure ν := ⟨by simp [ν, Real.volume_Ico]⟩
  have hnull (x : ℝ) : ν (embed ⁻¹' {x}) = 0 := (subsingleton_singleton.preimage hi).measure_zero ν
  have hs (x : ℝ) : embed x ∈ cantorSet := (cantorSetHomeomorphNatToBool.symm (code x)).2
  let F (x : ℝ) := ν.real (embed ⁻¹' Iic x)
  refine ⟨F, continuous_iff_continuousAt.2 fun x => ?_,
    fun _ _ h => measureReal_mono (preimage_mono (Iic_subset_Iic.2 h)), ?_, ?_, ?_⟩
  · refine (ENNReal.tendsto_toReal (measure_ne_top ν _)).comp ?_
    apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure _ (hm measurableSet_Iic) (fun _ => hm measurableSet_Iic)
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hnull x)] with t ht
    filter_upwards [Metric.ball_mem_nhds x (dist_pos.mpr (Ne.symm ht))] with y hy
    grind only [Metric.mem_ball, Real.dist_eq, abs_lt, abs_eq_max_neg, max_def, mem_preimage, mem_Iic]
  · refine fun x hx => (measureReal_eq_zero_iff (measure_ne_top ν _)).2 (measure_mono_null ?_ (hnull 0))
    exact fun t ht => ((mem_Iic.mp ht).trans hx).antisymm (cantorSet_subset_unitInterval (hs t)).1
  · refine fun x hx => (congrArg ν.real (eq_univ_of_forall ?_)).trans probReal_univ
    exact fun t => (cantorSet_subset_unitInterval (hs t)).2.trans hx
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 volume_cantorSet] with x hx
    obtain ⟨a, b, hx', hab⟩ := mem_nhds_iff_exists_Ioo_subset.1 (isClosed_cantorSet.isOpen_compl.mem_nhds hx)
    apply (hasDerivAt_const x (F x)).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hx'.1 hx'.2] with y hy
    refine congrArg ν.real (Set.ext fun t => (show embed t ≤ y ↔ embed t ≤ x from ?_))
    have hgap : embed t ∉ Ioo a b := fun ht => hab ht (hs t)
    grind only [mem_Ioo]

/-- Monotone singular approximants to the identity on a compact interval. -/
theorem exists_singular_approx {a b ε : ℝ} (hab : a < b) (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, Continuous g ∧ Monotone g ∧ (∀ x, g x ∈ Icc a b) ∧
      (∀ x, |g x - max a (min b x)| ≤ ε) ∧ (∀ᵐ x ∂volume, HasDerivAt g 0 x) := by
  obtain ⟨f, hfc, hfm, hf₀, hf₁, hfd⟩ := exists_singular_staircase
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / ε)
  have hn₀ : (0 : ℝ) < n := (by positivity : 0 ≤ (b - a) / ε).trans_lt hn
  let w := (b - a) / (n : ℝ)
  have hw : 0 < w := div_pos (sub_pos.mpr hab) hn₀
  have hwε : w ≤ ε := (div_le_comm₀ hn₀ hε).2 hn.le
  have hwidth : w * n + a = b := by simp [w, hn₀.ne']
  let H (m : ℕ) (y : ℝ) := ∑ j ∈ Finset.range m, f (y - j)
  have hHm (m : ℕ) : Monotone (H m) :=
    fun _ _ hy => Finset.sum_le_sum fun _ _ => hfm (sub_le_sub_right hy _)
  -- Only the translate containing `y` can differ from its linear ramp.
  have hH (m : ℕ) (y : ℝ) :
      H m y ∈ Icc 0 (m : ℝ) ∧ ((m : ℝ) ≤ y → H m y = m) ∧
        |H m y - max 0 (min (m : ℝ) y)| ≤ 1 := by
    induction m with
    | zero => simp [H]
    | succ m ih =>
      simp only [H, Nat.cast_succ, Finset.sum_range_succ] at ih ⊢
      grind [abs_le, Nat.cast_nonneg,
        hfm (min_le_left (y - m) 0), hfm (le_max_left (y - m) 1)]
  let B := (OrderIso.mulLeft₀ w hw).trans (OrderIso.addRight a)
  have hB (x : ℝ) : B x = w * x + a := rfl
  have hHc : Continuous (H n) := by unfold H; fun_prop
  refine ⟨B ∘ H n ∘ B.symm, B.continuous.comp (hHc.comp B.symm.continuous),
    B.monotone.comp ((hHm n).comp B.symm.monotone), ?_, ?_, ?_⟩
  · intro x
    simpa [hB, hwidth] using B.monotone.mapsTo_Icc (hH n (B.symm x)).1
  · intro x
    have hclip : B (max 0 (min (n : ℝ) (B.symm x))) = max a (min b x) := by
      simp only [B.monotone.map_max, B.monotone.map_min, B.apply_symm_apply, hB, mul_zero, zero_add, hwidth]
    simp only [Function.comp_apply, ← hclip, hB, add_sub_add_right_eq_sub, ← mul_sub, abs_mul, abs_of_pos hw]
    exact (mul_le_of_le_one_right hw.le (hH n (B.symm x)).2.2).trans hwε
  · have htranslate (t : ℝ) := (measurePreserving_sub_right volume t).quasiMeasurePreserving
    have hqmp := (Measure.quasiMeasurePreserving_smul volume (inv_ne_zero hw.ne')).comp (htranslate a)
    filter_upwards [hqmp.ae (ae_all_iff.2 fun j : ℕ => (htranslate (j : ℝ)).ae hfd)] with x hx
    have hAx : HasDerivAt B.symm _ x := ((hasDerivAt_id x).sub_const a).const_mul w⁻¹
    have hs := HasDerivAt.fun_sum (u := Finset.range n) fun j _ => (hx j).comp x (hAx.sub_const (j : ℝ))
    simpa [H, Function.comp_def, hB] using (hs.const_mul w).add_const a

end

end GlobeFlattening
