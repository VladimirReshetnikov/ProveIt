import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Probability.CDF
import Mathlib.Topology.Instances.CantorSet

/-!
# Singular staircases close to the identity

The Cantor staircase is the cumulative distribution function of the
pushforward of uniform measure on `[0, 1)` by the binary-to-ternary
encoding. The measure has no atoms and is supported on the null Cantor set.
Finite sums of scaled copies approximate the clamped identity on any
interval and have derivative zero almost everywhere.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal Pointwise

namespace GlobeFlattening

noncomputable section

private theorem volume_cantorSet : volume cantorSet = 0 := by
  have hscale (b : ℝ) : volume ((fun x : ℝ => (b + x) / 3) '' cantorSet) =
      ENNReal.ofReal (1 / 3) * volume cantorSet := by
    rw [show (fun x : ℝ => (b + x) / 3) '' cantorSet = (3 : ℝ)⁻¹ • ((b + ·) '' cantorSet) by
      simp only [← image_smul, image_image, smul_eq_mul, div_eq_inv_mul]]
    rw [Measure.addHaar_smul, image_add_left, measure_preimage_add, Module.finrank_self, pow_one]
    norm_num
  have hle : volume cantorSet ≤ ENNReal.ofReal (2 / 3) * volume cantorSet := by
    nth_rw 1 [cantorSet_eq_union_halves]
    refine (measure_union_le _ _).trans_eq ?_
    rw [show volume ((· / 3) '' cantorSet) = ENNReal.ofReal (1 / 3) * volume cantorSet by
      simpa using hscale 0, hscale 2, ← add_mul, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  by_contra hn
  have hc := ENNReal.ofReal_lt_one.2 (show (2 / 3 : ℝ) < 1 by norm_num)
  exact (not_lt_of_ge hle) (by
    simpa using ENNReal.mul_lt_mul_left hn isCompact_cantorSet.measure_lt_top.ne hc)

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
    dsimp only [μ]
    rw [Measure.map_apply hmeas hs, Measure.restrict_apply' measurableSet_Ico]
  letI : IsProbabilityMeasure μ := ⟨by simp [hμ _ MeasurableSet.univ, Real.volume_Ico]⟩
  have hnull (x : ℝ) : volume (encode ⁻¹' {x} ∩ Ico 0 1) = 0 := by
    apply Set.Subsingleton.measure_zero
    intro y hy z hz
    exact hinj hy.2 hz.2 ((mem_singleton_iff.mp hy.1).trans (mem_singleton_iff.mp hz.1).symm)
  refine ⟨cdf μ, ?_, monotone_cdf μ, ?_, ?_, ?_⟩
  · apply continuous_iff_continuousAt.mpr
    intro x
    rw [(monotone_cdf μ).continuousAt_iff_leftLim_eq_rightLim, (cdf μ).rightLim_eq]
    have h := ((cdf μ).measure_singleton x).symm
    rw [measure_cdf μ, hμ _ (measurableSet_singleton x), hnull,
      ENNReal.ofReal_eq_zero, sub_nonpos] at h
    exact le_antisymm ((monotone_cdf μ).leftLim_le le_rfl) h
  · intro x hx
    have hsubset : encode ⁻¹' Iic x ∩ Ico 0 1 ⊆ encode ⁻¹' {0} ∩ Ico 0 1 :=
      fun y hy => ⟨((mem_Iic.mp hy.1).trans hx).antisymm (cantorSet_subset_unitInterval (hmem y)).1, hy.2⟩
    rw [cdf_eq_real, measureReal_def, hμ _ measurableSet_Iic,
      measure_mono_null hsubset (hnull 0), ENNReal.toReal_zero]
  · intro x hx
    rw [cdf_eq_real, measureReal_def, hμ _ measurableSet_Iic, inter_eq_right.2]
    · simp [Real.volume_Ico]
    · exact fun y _ => (cantorSet_subset_unitInterval (hmem y)).2.trans hx
  · have hpreimage : encode ⁻¹' cantorSetᶜ = ∅ :=
      eq_empty_iff_forall_notMem.2 (fun x hx => hx (hmem x))
    have hsing : (cdf μ).measure ⟂ₘ volume := by
      refine ⟨cantorSetᶜ, isClosed_cantorSet.measurableSet.compl, ?_, by simpa using volume_cantorSet⟩
      simp [measure_cdf μ, hμ _ isClosed_cantorSet.measurableSet.compl, hpreimage]
    filter_upwards [(cdf μ).ae_hasDerivAt, hsing.rnDeriv_ae_eq_zero] with x hd hz
    simpa [show (cdf μ).measure.rnDeriv volume x = 0 from hz] using hd

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
  have hlow (m : ℕ) {y : ℝ} (hy : y ≤ 0) : H m y = 0 :=
    Finset.sum_eq_zero fun j _ => hf₀ _ (sub_nonpos.mpr (hy.trans (Nat.cast_nonneg j)))
  have hhigh (m : ℕ) {y : ℝ} (hy : (m : ℝ) ≤ y) : H m y = m := by
    unfold H
    rw [Finset.sum_eq_card_nsmul (b := 1) (fun j hj => hf₁ _ (by
      have hj' : (j : ℝ) + 1 ≤ m := by exact_mod_cast Finset.mem_range.mp hj
      linarith))]
    simp
  -- the sum of `m` translates stays within one step of the clamp to `[0, m]`
  have hclamp (m : ℕ) : ∀ y, |H m y - max 0 (min (m : ℝ) y)| ≤ 1 := by
    induction m with
    | zero => intro y; simp [H]
    | succ m ih =>
      intro y
      have hs : H (m + 1) y = H m y + f (y - m) := Finset.sum_range_succ _ _
      rw [Nat.cast_succ, hs]
      rcases le_total y m with hy | hy
      · rw [hf₀ _ (sub_nonpos.mpr hy), add_zero, min_eq_right (hy.trans (lt_add_one _).le)]
        simpa only [min_eq_right hy] using ih y
      · have hf0 : 0 ≤ f (y - m) := (hf₀ 0 le_rfl).ge.trans (hfm (sub_nonneg.mpr hy))
        have hf1 : f (y - m) ≤ 1 := (hfm (le_max_left _ 1)).trans_eq (hf₁ _ (le_max_right _ _))
        have hc0 : (m : ℝ) ≤ min ((m : ℝ) + 1) y := le_min (lt_add_one _).le hy
        have hc1 := min_le_left ((m : ℝ) + 1) y
        rw [hhigh m hy, max_eq_right ((Nat.cast_nonneg m).trans hc0)]
        exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hHr (y : ℝ) : H n y ∈ Icc 0 (n : ℝ) :=
    ⟨(hlow n (min_le_right y 0)).ge.trans (hHm n (min_le_left y 0)),
      (hHm n (le_max_left y n)).trans_eq (hhigh n (le_max_right y n))⟩
  let A (x : ℝ) := (x - a) / w
  let g (x : ℝ) := a + w * H n (A x)
  have hA : Monotone A := fun _ _ hx => div_le_div_of_nonneg_right (sub_le_sub_right hx _) hw.le
  have hgm : Monotone g := (((hHm n).comp hA).const_mul hw.le).const_add a
  have hgr (x : ℝ) : g x ∈ Icc a b := ⟨
    le_add_of_nonneg_right (mul_nonneg hw.le (hHr _).1), hwidth ▸
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (hHr _).2 hw.le)⟩
  refine ⟨g, ?_, hgm, hgr, ?_, ?_⟩
  · unfold g A H
    fun_prop
  · intro x
    have hmul : A x * w = x - a := div_mul_cancel₀ (x - a) hw.ne'
    have hAx : a + w * A x = x := by linarith only [hmul]
    have hx : max a (min b x) = a + w * max 0 (min (n : ℝ) (A x)) := by
      rw [mul_max_of_nonneg _ _ hw.le, mul_min_of_nonneg _ _ hw.le, mul_zero,
        ← max_add_add_left, ← min_add_add_left, add_zero, hwidth, hAx]
    rw [hx, show g x = a + w * H n (A x) from rfl, add_sub_add_left_eq_sub, ← mul_sub, abs_mul,
      abs_of_pos hw]
    exact (mul_le_of_le_one_right hw.le (hclamp n (A x))).trans hwε
  · have hshift (j : ℕ) : ∀ᵐ y ∂volume, HasDerivAt f 0 (y - j) :=
      (measurePreserving_sub_right volume (j : ℝ)).quasiMeasurePreserving.ae hfd
    have hscale := Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) (inv_ne_zero hw.ne')
    have hA : Measure.QuasiMeasurePreserving A volume volume := by
      simpa [A, Function.comp_def, smul_eq_mul, div_eq_inv_mul] using
        hscale.comp (measurePreserving_sub_right volume a).quasiMeasurePreserving
    filter_upwards [hA.ae (ae_all_iff.2 hshift)] with x hx
    have hs : HasDerivAt (fun y => H n (A y)) 0 x := by
      have hAx := ((hasDerivAt_id x).sub_const a).div_const w
      simpa [H, Function.comp_def] using HasDerivAt.fun_sum (u := Finset.range n)
        (fun j _ => (hx j).comp x (hAx.sub_const (j : ℝ)))
    simpa [g] using (hs.const_mul w).const_add a

end

end GlobeFlattening
