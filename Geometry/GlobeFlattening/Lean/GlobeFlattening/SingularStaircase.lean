import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Instances.CantorSet

/-!
# Singular staircases close to the identity

A measurable injection sends uniform measure on `[0, 1)` to an atomless
measure supported on the null Cantor set. Its distribution function is
continuous and locally constant off the Cantor set. Finite sums of scaled
copies approximate the clamped identity and have derivative zero almost everywhere.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal Pointwise

namespace GlobeFlattening

noncomputable section

private theorem volume_cantorSet : volume cantorSet = 0 := by
  have hsplit : (3 : ℝ) • cantorSet = cantorSet ∪ ((2 + · : ℝ → ℝ) '' cantorSet) := by
    nth_rw 1 [cantorSet_eq_union_halves, smul_set_union]
    simp only [← image_smul, image_image, smul_eq_mul,
      mul_div_cancel₀ _ (by norm_num : (3 : ℝ) ≠ 0), image_id']
  have hle : (3 : ℝ≥0∞) * volume cantorSet ≤ 2 * volume cantorSet := by
    have h := measure_union_le (μ := volume) cantorSet ((2 + · : ℝ → ℝ) '' cantorSet)
    rw [← hsplit, Measure.addHaar_smul_of_nonneg volume (by norm_num : 0 ≤ (3 : ℝ))] at h
    simpa [Module.finrank_self, image_add_left, measure_preimage_add, two_mul] using h
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
  let μ := ν.map embed
  letI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hm.aemeasurable
  have hnull (x : ℝ) : ν (embed ⁻¹' {x}) = 0 := (subsingleton_singleton.preimage hi).measure_zero ν
  letI : NullSingletonClass μ := ⟨fun x => (Measure.map_apply hm (measurableSet_singleton x)).trans (hnull x)⟩
  have hs (x : ℝ) : embed x ∈ cantorSet := (cantorSetHomeomorphNatToBool.symm (code x)).2
  let F (x : ℝ) := ν.real (embed ⁻¹' Iic x)
  refine ⟨F, continuous_iff_continuousAt.2 fun x => ?_,
    fun _ _ h => measureReal_mono (preimage_mono (Iic_subset_Iic.2 h)), ?_, ?_, ?_⟩
  · have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Iic (x + 1)) μ := (integrable_const 1).integrableOn
    simpa only [F, μ, setIntegral_const, smul_eq_mul, mul_one, map_measureReal_apply hm measurableSet_Iic] using
      hi.continuousOn_Iic_primitive_Iic.continuousAt (Iic_mem_nhds (lt_add_one x))
  · intro x hx
    refine measureReal_mono_null (s₂ := embed ⁻¹' {0}) (fun t ht => ?_) (by simp [measureReal_def, hnull])
    exact ((mem_Iic.mp ht).trans hx).antisymm (cantorSet_subset_unitInterval (hs t)).1
  · intro x hx
    exact (congrArg ν.real (eq_univ_of_forall (s := embed ⁻¹' Iic x) fun t =>
      (cantorSet_subset_unitInterval (hs t)).2.trans hx)).trans probReal_univ
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 volume_cantorSet] with x hx
    obtain ⟨a, b, hx', hab⟩ := mem_nhds_iff_exists_Ioo_subset.1 (isClosed_cantorSet.isOpen_compl.mem_nhds hx)
    apply (hasDerivAt_const x (F x)).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hx'.1 hx'.2] with y hy
    refine congrArg ν.real (Set.ext fun t => (show embed t ≤ y ↔ embed t ≤ x from ?_))
    have hgap : embed t ∉ Ioo a b := fun ht => hab ht (hs t)
    grind

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
  have hf (y : ℝ) : 0 ≤ f y ∧ f y ≤ 1 :=
    ⟨(hf₀ _ (min_le_right y 0)).ge.trans (hfm (min_le_left y 0)),
      (hfm (le_max_left y 1)).trans_eq (hf₁ _ (le_max_right y 1))⟩
  -- Only the translate containing `y` can differ from its linear ramp.
  have hH (m : ℕ) (y : ℝ) :
      H m y ∈ Icc 0 (m : ℝ) ∧ ((m : ℝ) ≤ y → H m y = m) ∧
        |H m y - max 0 (min (m : ℝ) y)| ≤ 1 := by
    induction m with
    | zero => simp [H]
    | succ m ih =>
      rw [Nat.cast_succ, show H (m + 1) y = H m y + f (y - m) from Finset.sum_range_succ _ _]
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have h0 : y ≤ m → f (y - m) = 0 := fun h => hf₀ _ (sub_nonpos.mpr h)
      have h1 : (m : ℝ) + 1 ≤ y → f (y - m) = 1 := fun h => hf₁ _ (by linarith)
      have hr := hf (y - m)
      grind [abs_le]
  let B := (OrderIso.mulLeft₀ w hw).trans (OrderIso.addRight a)
  have hB (x : ℝ) : B x = w * x + a := rfl
  have hBinv (x : ℝ) : B.symm x = w⁻¹ * (x - a) := rfl
  have hHc : Continuous (H n) := by unfold H; fun_prop
  refine ⟨B ∘ H n ∘ B.symm, B.continuous.comp (hHc.comp B.symm.continuous),
    B.monotone.comp ((hHm n).comp B.symm.monotone), ?_, ?_, ?_⟩
  · intro x
    simpa [hB, hwidth] using B.monotone.mapsTo_Icc (hH n (B.symm x)).1
  · intro x
    have hclip : B (max 0 (min (n : ℝ) (B.symm x))) = max a (min b x) := by
      rw [B.monotone.map_max, B.monotone.map_min, B.apply_symm_apply]
      simp [hB, hwidth]
    simp only [Function.comp_apply, ← hclip, hB, add_sub_add_right_eq_sub, ← mul_sub, abs_mul, abs_of_pos hw]
    exact (mul_le_of_le_one_right hw.le (hH n (B.symm x)).2.2).trans hwε
  · have hqmp : Measure.QuasiMeasurePreserving B.symm volume volume :=
      (Measure.quasiMeasurePreserving_smul volume (inv_ne_zero hw.ne')).comp
        (measurePreserving_sub_right volume a).quasiMeasurePreserving
    filter_upwards [ae_all_iff.2 fun j : ℕ =>
      hqmp.ae ((measurePreserving_sub_right volume (j : ℝ)).quasiMeasurePreserving.ae hfd)] with x hx
    have hAx := ((hasDerivAt_id x).sub_const a).const_mul w⁻¹
    have hs := HasDerivAt.fun_sum (u := Finset.range n) fun j _ => (hx j).comp x (hAx.sub_const (j : ℝ))
    simpa [H, Function.comp_def, hB, hBinv] using (hs.const_mul w).add_const a

end

end GlobeFlattening
