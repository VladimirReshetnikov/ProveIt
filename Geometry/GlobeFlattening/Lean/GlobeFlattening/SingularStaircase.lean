import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Instances.CantorSet

/-!
# Singular staircases close to the identity

The Cantor staircase is the cumulative distribution function of the
pushforward of uniform measure on `[0, 1)` by the binary-to-ternary
encoding. Its atomless measure gives a continuous distribution function
that is locally constant off the null Cantor set. Finite sums of scaled
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
  let digit : Fin 2 → Fin 3 := fun d => if d = 0 then 0 else 2
  have hdigit : Function.Injective digit := by decide
  have hne1 (d : Fin 2) : digit d ≠ 1 := by fin_cases d <;> decide
  let encode (x : ℝ) := Real.ofDigits (digit ∘ Real.digits x 2)
  have hmem (x : ℝ) : encode x ∈ cantorSet :=
    ofDigits_zero_two_sequence_mem_cantorSet fun i => hne1 (Real.digits x 2 i)
  have hmeas : Measurable encode := by
    refine Real.continuous_ofDigits.measurable.comp (measurable_pi_lambda _ fun i => ?_)
    exact (measurable_of_countable (digit ∘ Fin.ofNat 2)).comp
      (measurable_id.mul_const ((2 : ℝ) ^ (i + 1))).nat_floor
  have hinj : InjOn encode (Ico 0 1) := by
    intro x hx y hy hxy
    have h := ofDigits_zero_two_sequence_unique (fun i => hne1 (Real.digits x 2 i))
      (fun i => hne1 (Real.digits y 2 i)) hxy
    rw [← Real.ofDigits_digits (b := 2) (by decide) hx,
      ← Real.ofDigits_digits (b := 2) (by decide) hy]
    exact congrArg Real.ofDigits (funext fun i => hdigit (congrFun h i))
  let μ := (volume.restrict (Ico 0 1)).map encode
  have hμ (s : Set ℝ) (hs : MeasurableSet s) : μ s = volume (encode ⁻¹' s ∩ Ico 0 1) := by
    simp only [μ, Measure.map_apply hmeas hs, Measure.restrict_apply' measurableSet_Ico]
  letI : IsProbabilityMeasure μ := ⟨by simp [hμ _ MeasurableSet.univ, Real.volume_Ico]⟩
  letI : NullSingletonClass μ := ⟨fun x => by
    rw [hμ _ (measurableSet_singleton x)]
    exact (show (encode ⁻¹' {x} ∩ Ico 0 1).Subsingleton from
      fun y hy z hz => hinj hy.2 hz.2 ((mem_singleton_iff.mp hy.1).trans (mem_singleton_iff.mp hz.1).symm)).measure_zero volume⟩
  have hs : ∀ᵐ t ∂μ, t ∈ cantorSet :=
    (ae_map_iff hmeas.aemeasurable isClosed_cantorSet.measurableSet).2 (ae_of_all _ hmem)
  let F (x : ℝ) := μ.real (Iic x)
  refine ⟨F, continuous_iff_continuousAt.2 fun x => ?_,
    fun _ _ h => measureReal_mono (Iic_subset_Iic.2 h), ?_, ?_, ?_⟩
  · have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Iic (x + 1)) μ := (integrable_const 1).integrableOn
    simpa only [F, setIntegral_const, smul_eq_mul, mul_one] using
      hi.continuousOn_Iic_primitive_Iic.continuousAt (Iic_mem_nhds (lt_add_one x))
  · intro x hx
    have hle : Iic x ≤ᵐ[μ] ({0} : Set ℝ) := hs.mono fun t ht htx =>
      mem_singleton_iff.mpr (((mem_Iic.mp htx).trans hx).antisymm (cantorSet_subset_unitInterval ht).1)
    simp [F, measureReal_def, measure_mono_null_ae hle (measure_singleton 0)]
  · intro x hx
    exact (measureReal_congr (t := univ) (hs.mono fun t ht =>
      propext (iff_true_intro ((cantorSet_subset_unitInterval ht).2.trans hx)))).trans probReal_univ
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 volume_cantorSet] with x hx
    obtain ⟨a, b, hx', hab⟩ := mem_nhds_iff_exists_Ioo_subset.1 (isClosed_cantorSet.isOpen_compl.mem_nhds hx)
    apply (hasDerivAt_const x (F x)).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hx'.1 hx'.2] with y hy
    refine measureReal_congr (hs.mono fun t ht => propext (show t ≤ y ↔ t ≤ x from ?_))
    have hgap : t ∉ Ioo a b := fun ht' => hab ht' ht
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
  have hwidth : a + w * n = b := by simp [w, hn₀.ne']
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
  let A (x : ℝ) := (x - a) / w
  let g (x : ℝ) := a + w * H n (A x)
  have hA : Monotone A := fun _ _ hx => div_le_div_of_nonneg_right (sub_le_sub_right hx _) hw.le
  have hgm : Monotone g := (((hHm n).comp hA).const_mul hw.le).const_add a
  have hgr (x : ℝ) : g x ∈ Icc a b := ⟨
    le_add_of_nonneg_right (mul_nonneg hw.le (hH n _).1.1), hwidth ▸
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (hH n _).1.2 hw.le)⟩
  refine ⟨g, ?_, hgm, hgr, ?_, ?_⟩
  · unfold g A H
    fun_prop
  · intro x
    have hAx : a + w * A x = x := by rw [mul_comm]; simp [A, hw.ne']
    have hx : max a (min b x) = a + w * max 0 (min (n : ℝ) (A x)) := by
      rw [mul_max_of_nonneg _ _ hw.le, mul_min_of_nonneg _ _ hw.le, mul_zero,
        ← max_add_add_left, ← min_add_add_left, add_zero, hwidth, hAx]
    rw [hx, show g x = a + w * H n (A x) from rfl, add_sub_add_left_eq_sub, ← mul_sub, abs_mul,
      abs_of_pos hw]
    exact (mul_le_of_le_one_right hw.le (hH n (A x)).2.2).trans hwε
  · have hA : Measure.QuasiMeasurePreserving A volume volume := by
      simpa [A, Function.comp_def, smul_eq_mul, div_eq_inv_mul] using
        (Measure.quasiMeasurePreserving_smul volume (inv_ne_zero hw.ne')).comp
          (measurePreserving_sub_right volume a).quasiMeasurePreserving
    filter_upwards [ae_all_iff.2 fun j : ℕ =>
      hA.ae ((measurePreserving_sub_right volume (j : ℝ)).quasiMeasurePreserving.ae hfd)] with x hx
    have hAx := ((hasDerivAt_id x).sub_const a).div_const w
    have hs := HasDerivAt.fun_sum (u := Finset.range n) fun j _ => (hx j).comp x (hAx.sub_const (j : ℝ))
    simpa [g, H, A, Function.comp_def] using (hs.const_mul w).const_add a

end

end GlobeFlattening
