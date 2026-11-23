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
open scoped Topology ENNReal

namespace GlobeFlattening

noncomputable section

private theorem volume_cantorSet : volume cantorSet = 0 := by
  let c := ENNReal.ofReal (1 / 3)
  have hscale (b : ℝ) : volume ((fun x : ℝ => (b + x) / 3) '' cantorSet) =
      c * volume cantorSet := by
    have hfun : (fun x : ℝ => (b + x) / 3) =
        (fun x => b / 3 + (1 / 3 : ℝ) * x) := by
      funext x
      ring
    rw [hfun, ← image_image]
    simp only [← smul_eq_mul, image_smul, image_add_left, measure_preimage_add,
      Measure.addHaar_smul, Module.finrank_self, pow_one]
    norm_num [c]
  have hle : volume cantorSet ≤ (c + c) * volume cantorSet := by
    nth_rw 1 [cantorSet_eq_union_halves]
    refine (measure_union_le _ _).trans_eq ?_
    rw [show volume ((· / 3) '' cantorSet) = c * volume cantorSet by simpa using hscale 0,
      hscale 2, add_mul]
  have hc : c + c < 1 := by
    dsimp only [c]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num), ← ENNReal.ofReal_one,
      ENNReal.ofReal_lt_ofReal_iff zero_lt_one]
    norm_num
  by_contra hn
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
  letI : IsProbabilityMeasure μ := ⟨by
    rw [hμ _ MeasurableSet.univ]
    simp [Real.volume_Ico]⟩
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
    have hsubset : encode ⁻¹' Iic x ∩ Ico 0 1 ⊆ encode ⁻¹' {0} ∩ Ico 0 1 := by
      intro y hy
      exact ⟨le_antisymm ((mem_Iic.mp hy.1).trans hx)
        (cantorSet_subset_unitInterval (hmem y)).1, hy.2⟩
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
      g a = a ∧ g b = b ∧ (∀ x, |g x - max a (min b x)| ≤ ε) ∧
      (∀ᵐ x ∂volume, HasDerivAt g 0 x) := by
  obtain ⟨f, hfc, hfm, hf₀, hf₁, hfd⟩ := exists_singular_staircase
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / ε)
  have hn₀ : (0 : ℝ) < n := (by positivity : 0 ≤ (b - a) / ε).trans_lt hn
  let w := (b - a) / (n : ℝ)
  have hw : 0 < w := div_pos (sub_pos.mpr hab) hn₀
  have hwε : w ≤ ε := by
    apply (div_le_iff₀ hn₀).2
    linarith [(div_lt_iff₀ hε).1 hn]
  have hwidth : a + w * n = b := by
    rw [div_mul_cancel₀ (b - a) hn₀.ne']
    ring
  let H (y : ℝ) := ∑ j ∈ Finset.range n, f (y - j)
  have hHm : Monotone H :=
    fun _ _ hy => Finset.sum_le_sum fun _ _ => hfm (sub_le_sub_right hy _)
  have hfRange (x : ℝ) : f x ∈ Icc 0 1 := ⟨by
    simpa only [hf₀ _ (min_le_left 0 x)] using hfm (min_le_right 0 x), by
    simpa only [hf₁ _ (le_max_left 1 x)] using hfm (le_max_right 1 x)⟩
  have hHr (y : ℝ) : H y ∈ Icc 0 (n : ℝ) := ⟨
    Finset.sum_nonneg fun j _ => (hfRange (y - j)).1, by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] using
      (Finset.sum_le_sum (s := Finset.range n) fun j _ => (hfRange (y - j)).2)⟩
  have hgrid (i : ℕ) (hi : i ≤ n) : H i = i := by
    have hplateau (j : ℕ) : f ((i : ℝ) - j) = if j < i then 1 else 0 := by
      split_ifs with h
      · have hj : ((j : ℝ) + 1) ≤ i := by exact_mod_cast h
        exact hf₁ _ (by linarith)
      · exact hf₀ _ (sub_nonpos.mpr (Nat.cast_le.mpr (le_of_not_gt h)))
    have hcount : (Finset.range n).filter (· < i) = Finset.range i := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    simp_rw [H, hplateau]
    rw [Finset.sum_boole, hcount, Finset.card_range]
  have hunit (y : ℝ) (hlo : 0 ≤ y) (hhi : y < n) : |H y - y| ≤ 1 := by
    let j := ⌊y⌋₊
    have hj : j < n := (Nat.floor_lt hlo).2 hhi
    have hl := Nat.floor_le hlo
    have hr := (Nat.lt_floor_add_one y).le
    have hH₀ : (j : ℝ) ≤ H y := (hgrid j hj.le).ge.trans (hHm hl)
    have hH₁ : H y ≤ (j : ℝ) + 1 := by
      calc
        _ ≤ H (↑(j + 1) : ℝ) := hHm (by exact_mod_cast hr)
        _ = _ := (hgrid (j + 1) hj).trans (Nat.cast_succ _)
    exact abs_le.2 ⟨by linarith, by linarith⟩
  let A (x : ℝ) := (x - a) / w
  let g (x : ℝ) := a + w * H (A x)
  have hgm : Monotone g := fun _ _ hx =>
    add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (hHm (div_le_div_of_nonneg_right (sub_le_sub_right hx _) hw.le)) hw.le)
  have hgr (x : ℝ) : g x ∈ Icc a b := ⟨
    le_add_of_nonneg_right (mul_nonneg hw.le (hHr _).1), hwidth ▸
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (hHr _).2 hw.le)⟩
  have hH₀ : H 0 = 0 := by simpa only [Nat.cast_zero] using hgrid 0 (Nat.zero_le n)
  have hga : g a = a := by simp [g, A, hH₀]
  have hAb : A b = n := (div_eq_iff hw.ne').2 (by linarith only [hwidth])
  have hgb : g b = b := by rw [show g b = a + w * H (A b) from rfl, hAb, hgrid n le_rfl, hwidth]
  refine ⟨g, ?_, hgm, hgr, hga, hgb, ?_, ?_⟩
  · unfold g A H
    fun_prop
  · intro x
    by_cases hxa : a ≤ x
    · by_cases hxb : x < b
      · rw [min_eq_right hxb.le, max_eq_right hxa]
        have hAx : A x < n := (div_lt_iff₀ hw).2 (by linarith only [hxb, hwidth])
        have hmul : A x * w = x - a := div_mul_cancel₀ (x - a) hw.ne'
        have hd : g x - x = w * (H (A x) - A x) := by
          dsimp only [g]
          linarith only [hmul]
        rw [hd, abs_mul, abs_of_pos hw]
        have he := hunit (A x) (div_nonneg (sub_nonneg.mpr hxa) hw.le) hAx
        exact (mul_le_mul_of_nonneg_left he hw.le).trans (by simpa only [mul_one] using hwε)
      · have hx : b ≤ x := le_of_not_gt hxb
        have he : g x = b := le_antisymm (hgr x).2 (hgb.ge.trans (hgm hx))
        simpa [min_eq_left hx, max_eq_right hab.le, he] using hε.le
    · have hx : x ≤ a := (lt_of_not_ge hxa).le
      have he : g x = a := le_antisymm ((hgm hx).trans hga.le) (hgr x).1
      simpa [min_eq_right (hx.trans hab.le), max_eq_left hx, he] using hε.le
  · have hae (j : ℕ) : ∀ᵐ x ∂volume, HasDerivAt (fun x => f (A x - j)) 0 x := by
      have hpres (t : ℝ) := (measurePreserving_sub_right volume t).quasiMeasurePreserving
      have hmul := Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) (inv_ne_zero hw.ne')
      have hA : Measure.QuasiMeasurePreserving (fun x => A x - j) volume volume := by
        simpa [A, Function.comp_def, smul_eq_mul, div_eq_inv_mul] using
          (hpres j).comp (hmul.comp (hpres a))
      filter_upwards [hA.ae hfd] with x hx
      have hAffine : HasDerivAt (fun x => A x - j) (1 / w) x :=
        (((hasDerivAt_id x).sub_const a).div_const w).sub_const (j : ℝ)
      simpa [Function.comp_def] using hx.comp x hAffine
    filter_upwards [ae_all_iff.2 hae] with x hx
    have hs : HasDerivAt (fun y => H (A y)) 0 x := by
      simpa only [Finset.sum_const_zero, H] using
        HasDerivAt.fun_sum (u := Finset.range n) (fun j _ => hx j)
    simpa [g] using (hs.const_mul w).const_add a

end

end GlobeFlattening
