import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import OAI.Combinatorics.Progressions.Geometry.UnitBoxAmplitude

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def densityMixture {T X : Type*} [MeasurableSpace T]
    (μ : Measure T) (F : T → X → ℝ) (x : X) : ℝ := ∫ t, F t x ∂μ

theorem densityMixture_section_integrable {T X : Type*} [MeasurableSpace T]
    (μ : Measure T) (F : T → X → ℝ) (C : T → ℝ) (hC : Integrable C μ)
    (hm : ∀ x, AEStronglyMeasurable (fun t => F t x) μ)
    (hbound : ∀ᵐ t ∂μ, ∀ x, ‖F t x‖ ≤ C t) (x : X) :
    Integrable (fun t => F t x) μ :=
  hC.mono' (hm x) (hbound.mono (fun _ ht => ht x))

theorem densityMixture_cap {T X : Type*} [MeasurableSpace T]
    (μ : Measure T) (F : T → X → ℝ) (C : T → ℝ) (hC : Integrable C μ)
    (hm : ∀ x, AEStronglyMeasurable (fun t => F t x) μ)
    (hbound : ∀ᵐ t ∂μ, ∀ x, F t x ∈ Set.Icc (0 : ℝ) (C t)) (x : X) :
    densityMixture μ F x ∈ Set.Icc (0 : ℝ) (∫ t, C t ∂μ) := by
  have hb : ∀ᵐ t ∂μ, ∀ y, ‖F t y‖ ≤ C t := hbound.mono fun t ht y => by
    rw [Real.norm_of_nonneg (ht y).1]
    exact (ht y).2
  exact ⟨integral_nonneg_of_ae (hbound.mono (fun _ ht => (ht x).1)),
    integral_mono_ae (densityMixture_section_integrable μ F C hC hm hb x) hC
      (hbound.mono (fun _ ht => (ht x).2))⟩

theorem densityMixture_lipschitz {T X : Type*} [MeasurableSpace T] [PseudoMetricSpace X]
    (μ : Measure T) (F : T → X → ℝ) (L : T → ℝ≥0)
    (hL : Integrable (fun t => (L t : ℝ)) μ)
    (hint : ∀ x, Integrable (fun t => F t x) μ)
    (hLip : ∀ᵐ t ∂μ, LipschitzWith (L t) (F t)) :
    LipschitzWith ⟨∫ t, (L t : ℝ) ∂μ, integral_nonneg (fun t => (L t).coe_nonneg)⟩
      (densityMixture μ F) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  change |(∫ t, F t x ∂μ) - ∫ t, F t y ∂μ| ≤ _
  rw [← integral_sub (hint x) (hint y)]
  have hb : ∀ᵐ t ∂μ, ‖F t x - F t y‖ ≤ (L t : ℝ) * dist x y := by
    filter_upwards [hLip] with t ht
    simpa only [Real.dist_eq, Real.norm_eq_abs] using ht.dist_le_mul x y
  have h := norm_integral_le_of_norm_le (hL.mul_const (dist x y)) hb
  rw [Real.norm_eq_abs, integral_mul_const] at h
  exact h

theorem densityMixture_joint_integrable {T X : Type*} [MeasurableSpace T] [MeasurableSpace X]
    (μ : Measure T) (ν : Measure X) [IsProbabilityMeasure μ] [SFinite ν]
    (F : T → X → ℝ) (hm : Measurable (Function.uncurry F))
    (hF : ∀ᵐ t ∂μ, (∀ x, 0 ≤ F t x) ∧ Integrable (F t) ν ∧ (∫ x, F t x ∂ν) = 1) :
    Integrable (Function.uncurry F) (μ.prod ν) := by
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨hF.mono (fun _ ht => ht.2.1), ?_⟩
  apply (integrable_const (1 : ℝ)).congr
  filter_upwards [hF] with t ht
  simp only [Function.uncurry_apply_pair, Real.norm_of_nonneg (ht.1 _)]
  exact ht.2.2.symm

theorem densityMixture_probability_density {T X : Type*} [MeasurableSpace T] [MeasurableSpace X]
    (μ : Measure T) (ν : Measure X) [IsProbabilityMeasure μ] [SFinite ν]
    (F : T → X → ℝ) (hm : Measurable (Function.uncurry F))
    (hF : ∀ᵐ t ∂μ, (∀ x, 0 ≤ F t x) ∧ Integrable (F t) ν ∧ (∫ x, F t x ∂ν) = 1) :
    (∀ x, 0 ≤ densityMixture μ F x) ∧ Integrable (densityMixture μ F) ν ∧
      (∫ x, densityMixture μ F x ∂ν) = 1 := by
  have hi := densityMixture_joint_integrable μ ν F hm hF
  refine ⟨fun x => integral_nonneg_of_ae (hF.mono (fun _ ht => ht.1 x)),
    hi.integral_prod_right, ?_⟩
  change (∫ x, ∫ t, F t x ∂μ ∂ν) = 1
  rw [← integral_integral_swap hi]
  calc
    (∫ t, ∫ x, F t x ∂ν ∂μ) = ∫ _, (1 : ℝ) ∂μ :=
      integral_congr_ae (hF.mono (fun _ ht => ht.2.2))
    _ = 1 := by simp

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem densityMixture_l1_le {T X : Type*} [MeasurableSpace T] [MeasurableSpace X]
    (μ : Measure T) (ν : Measure X) [SFinite μ] [SFinite ν]
    (F G : T → X → ℝ)
    (hF : Integrable (Function.uncurry F) (μ.prod ν))
    (hG : Integrable (Function.uncurry G) (μ.prod ν)) :
    (∫ x, ‖densityMixture μ F x - densityMixture μ G x‖ ∂ν) ≤
      ∫ t, ∫ x, ‖F t x - G t x‖ ∂ν ∂μ := by
  have hd : Integrable (Function.uncurry (fun t x => F t x - G t x)) (μ.prod ν) := hF.sub hG
  have hm : Integrable (fun x => densityMixture μ F x - densityMixture μ G x) ν :=
    hF.integral_prod_right.sub hG.integral_prod_right
  calc
    (∫ x, ‖densityMixture μ F x - densityMixture μ G x‖ ∂ν) ≤
        ∫ x, ∫ t, ‖F t x - G t x‖ ∂μ ∂ν := by
      apply integral_mono_ae hm.norm hd.integral_norm_prod_right
      filter_upwards [hF.prod_left_ae, hG.prod_left_ae] with x hfx hgx
      change Integrable (fun t => F t x) μ at hfx
      change Integrable (fun t => G t x) μ at hgx
      change ‖(∫ t, F t x ∂μ) - ∫ t, G t x ∂μ‖ ≤ _
      rw [← integral_sub hfx hgx]
      exact norm_integral_le_integral_norm _
    _ = ∫ t, ∫ x, ‖F t x - G t x‖ ∂ν ∂μ := (integral_integral_swap hd.norm).symm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem measurable_normalizedIntervalWindow {T : Type*} [MeasurableSpace T]
    (ℓ s t : T → ℝ) (hℓ : Measurable ℓ) (hs : Measurable s) (ht : Measurable t) :
    Measurable (fun u => normalizedIntervalWindow (ℓ u) (s u) (t u)) := by
  have hm : MeasurableSet {u | s u < t u ∧ t u ≤ s u + ℓ u} :=
    (measurableSet_lt hs ht).inter (measurableSet_le ht (hs.add hℓ))
  have hn : Measurable ({u | s u < t u ∧ t u ≤ s u + ℓ u}.indicator (fun _ : T => (1 : ℝ))) :=
    measurable_const.indicator hm
  exact hn.div hℓ

noncomputable def randomIntervalDensity {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (ℓ s : T → ℝ) : ℝ → ℝ :=
  densityMixture μ (fun t => normalizedIntervalWindow (ℓ t) (s t))

theorem randomIntervalDensity_cap {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (ℓ s : T → ℝ) (hℓ : Measurable ℓ) (hs : Measurable s)
    (hpos : ∀ᵐ t ∂μ, 0 < ℓ t) (hi : Integrable (fun t => (ℓ t)⁻¹) μ) (x : ℝ) :
    randomIntervalDensity μ ℓ s x ∈ Set.Icc (0 : ℝ) (∫ t, (ℓ t)⁻¹ ∂μ) := by
  apply densityMixture_cap μ _ _ hi
  · intro y
    exact (measurable_normalizedIntervalWindow ℓ s (fun _ => y) hℓ hs measurable_const).aestronglyMeasurable
  · filter_upwards [hpos] with t ht
    intro y
    exact ⟨normalizedIntervalWindow_nonneg ht _ _, by simpa only [one_div] using normalizedIntervalWindow_le ht (s t) y⟩

theorem randomIntervalDensity_probability_density {T : Type*} [MeasurableSpace T]
    (μ : Measure T) [IsProbabilityMeasure μ] (ℓ s : T → ℝ)
    (hℓ : Measurable ℓ) (hs : Measurable s) (hpos : ∀ᵐ t ∂μ, 0 < ℓ t) :
    (∀ x, 0 ≤ randomIntervalDensity μ ℓ s x) ∧ Integrable (randomIntervalDensity μ ℓ s) ∧
      (∫ x, randomIntervalDensity μ ℓ s x) = 1 := by
  apply densityMixture_probability_density μ volume _
  · exact measurable_normalizedIntervalWindow _ _ _ (hℓ.comp measurable_fst)
      (hs.comp measurable_fst) measurable_snd
  · filter_upwards [hpos] with t ht
    exact ⟨normalizedIntervalWindow_nonneg ht _, normalizedIntervalWindow_integrable _ _,
      normalizedIntervalWindow_mass ht _⟩

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem densityMixture_uniform_bound {T X : Type*} [MeasurableSpace T] [PseudoMetricSpace X]
    (μ : Measure T) [IsProbabilityMeasure μ] (F : T → X → ℝ) (C L : ℝ≥0)
    (hm : ∀ x, AEStronglyMeasurable (fun t => F t x) μ)
    (hF : ∀ᵐ t ∂μ, (∀ x, F t x ∈ Set.Icc (0 : ℝ) C) ∧ LipschitzWith L (F t)) :
    (∀ x, densityMixture μ F x ∈ Set.Icc (0 : ℝ) C) ∧ LipschitzWith L (densityMixture μ F) := by
  have hb : ∀ᵐ t ∂μ, ∀ x, ‖F t x‖ ≤ (C : ℝ) := by
    filter_upwards [hF] with t ht
    intro x
    rw [Real.norm_of_nonneg (ht.1 x).1]
    exact (ht.1 x).2
  have hi := densityMixture_section_integrable μ F (fun _ => (C : ℝ)) (integrable_const _) hm hb
  constructor
  · intro x
    have h := densityMixture_cap μ F (fun _ => (C : ℝ)) (integrable_const _) hm
      (hF.mono (fun _ ht => ht.1)) x
    simpa only [integral_const, probReal_univ, one_smul] using h
  · have h := densityMixture_lipschitz μ F (fun _ => L) (integrable_const _) hi
      (hF.mono (fun _ ht => ht.2))
    have heq : (⟨∫ _ : T, (L : ℝ) ∂μ, integral_nonneg (fun _ => L.coe_nonneg)⟩ : ℝ≥0) = L := by
      apply Subtype.ext
      simp
    rw [heq] at h
    exact h

theorem densityMixture_test_integral {T X : Type*} [MeasurableSpace T] [MeasurableSpace X]
    (μ : Measure T) (ν : Measure X) [SFinite μ] [SFinite ν]
    (F : T → X → ℝ) (hF : Integrable (Function.uncurry F) (μ.prod ν))
    (φ : X → ℝ) (hφ : Measurable φ) {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    (∫ x, densityMixture μ F x * φ x ∂ν) = ∫ t, ∫ x, F t x * φ x ∂ν ∂μ := by
  have hi : Integrable (Function.uncurry (fun t x => F t x * φ x)) (μ.prod ν) :=
    hF.mul_bdd (hφ.comp measurable_snd).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hbound p.2))
  calc
    (∫ x, densityMixture μ F x * φ x ∂ν) = ∫ x, ∫ t, F t x * φ x ∂μ ∂ν := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact (integral_mul_const (φ x) _).symm
    _ = ∫ t, ∫ x, F t x * φ x ∂ν ∂μ := (integral_integral_swap hi).symm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem densityMixture_translation_l1 {T : Type*} [MeasurableSpace T]
    (μ : Measure T) [IsProbabilityMeasure μ] (F : T → ℝ → ℝ)
    (hm : Measurable (Function.uncurry F))
    (hF : ∀ᵐ t ∂μ, (∀ x, 0 ≤ F t x) ∧ Integrable (F t) ∧ (∫ x, F t x) = 1)
    (D : ℝ) (hmove : ∀ᵐ t ∂μ, ∀ a b, (∫ x, |F t (x + a) - F t (x + b)|) ≤ D * |a - b|)
    (a b : ℝ) :
    (∫ x, |densityMixture μ F (x + a) - densityMixture μ F (x + b)|) ≤ D * |a - b| := by
  have hj (c : ℝ) : Integrable (Function.uncurry (fun t x => F t (x + c))) (μ.prod volume) := by
    apply densityMixture_joint_integrable μ volume _
    · exact hm.comp (measurable_fst.prodMk (measurable_snd.add_const c))
    · filter_upwards [hF] with t ht
      refine ⟨fun x => ht.1 _, ht.2.1.comp_add_right c, ?_⟩
      rw [integral_add_right_eq_self, ht.2.2]
  have h := densityMixture_l1_le μ volume _ _ (hj a) (hj b)
  simp only [Real.norm_eq_abs] at h
  apply h.trans
  have hd : Integrable (Function.uncurry (fun t x => F t (x + a) - F t (x + b)))
      (μ.prod volume) := (hj a).sub (hj b)
  have hmono := integral_mono_ae hd.integral_norm_prod_left
    (integrable_const (D * |a - b|)) (by
      filter_upwards [hmove] with t ht
      change (∫ x, ‖F t (x + a) - F t (x + b)‖) ≤ D * |a - b|
      simp only [Real.norm_eq_abs]
      exact ht a b)
  simp only [integral_const, probReal_univ, one_smul] at hmono
  exact hmono

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

noncomputable def unitScalarMeasure : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)

instance unitScalarMeasure_probability : IsProbabilityMeasure unitScalarMeasure := by
  constructor
  simp [unitScalarMeasure]

theorem normalizedIntervalWindow_test_integral {ℓ : ℝ} (hℓ : 0 < ℓ) (s : ℝ) (φ : ℝ → ℝ) :
    (∫ x, normalizedIntervalWindow ℓ s x * φ x) =
      ∫ u, φ (s + ℓ * u) ∂unitScalarMeasure := by
  have heq (x : ℝ) : normalizedIntervalWindow ℓ s x * φ x =
      (Set.Ioc s (s + ℓ)).indicator φ x / ℓ := by
    by_cases hx : x ∈ Set.Ioc s (s + ℓ)
    · simp only [normalizedIntervalWindow, intervalWindow, Set.indicator_of_mem hx]
      ring
    · simp only [normalizedIntervalWindow, intervalWindow, Set.indicator_of_notMem hx, zero_div, zero_mul]
  simp_rw [heq]
  rw [integral_div, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : s ≤ s + ℓ)]
  change _ = ∫ u in Set.Ioc (0 : ℝ) 1, φ (s + ℓ * u)
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_comp_add_mul φ hℓ.ne' s]
  simp only [mul_zero, add_zero, mul_one, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem randomIntervalDensity_measurable {T : Type*} [MeasurableSpace T]
    (μ : Measure T) [SFinite μ] (ℓ s : T → ℝ) (hℓ : Measurable ℓ) (hs : Measurable s) :
    Measurable (randomIntervalDensity μ ℓ s) := by
  have hm : Measurable (fun p : T × ℝ => normalizedIntervalWindow (ℓ p.1) (s p.1) p.2) :=
    measurable_normalizedIntervalWindow _ _ _ (hℓ.comp measurable_fst)
      (hs.comp measurable_fst) measurable_snd
  exact hm.stronglyMeasurable.integral_prod_left'.measurable

theorem randomIntervalDensity_test_integral {T : Type*} [MeasurableSpace T]
    (μ : Measure T) [IsProbabilityMeasure μ] (ℓ s : T → ℝ)
    (hℓ : Measurable ℓ) (hs : Measurable s) (hpos : ∀ᵐ t ∂μ, 0 < ℓ t)
    (φ : ℝ → ℝ) (hφ : Measurable φ) {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    (∫ x, randomIntervalDensity μ ℓ s x * φ x) =
      ∫ t, ∫ u, φ (s t + ℓ t * u) ∂unitScalarMeasure ∂μ := by
  have hm : Measurable (fun p : T × ℝ => normalizedIntervalWindow (ℓ p.1) (s p.1) p.2) :=
    measurable_normalizedIntervalWindow _ _ _ (hℓ.comp measurable_fst)
      (hs.comp measurable_fst) measurable_snd
  have hd : ∀ᵐ t ∂μ, (∀ x, 0 ≤ normalizedIntervalWindow (ℓ t) (s t) x) ∧
      Integrable (normalizedIntervalWindow (ℓ t) (s t)) ∧
      (∫ x, normalizedIntervalWindow (ℓ t) (s t) x) = 1 := by
    filter_upwards [hpos] with t ht
    exact ⟨normalizedIntervalWindow_nonneg ht _, normalizedIntervalWindow_integrable _ _,
      normalizedIntervalWindow_mass ht _⟩
  have hi : Integrable (Function.uncurry
      (fun t x => normalizedIntervalWindow (ℓ t) (s t) x * φ x)) (μ.prod volume) :=
    (densityMixture_joint_integrable μ volume _ hm hd).mul_bdd
      (hφ.comp measurable_snd).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hbound p.2))
  calc
    (∫ x, randomIntervalDensity μ ℓ s x * φ x) =
        ∫ x, ∫ t, normalizedIntervalWindow (ℓ t) (s t) x * φ x ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact (integral_mul_const (φ x) _).symm
    _ = ∫ t, ∫ x, normalizedIntervalWindow (ℓ t) (s t) x * φ x ∂volume ∂μ :=
      (integral_integral_swap hi).symm
    _ = ∫ t, ∫ u, φ (s t + ℓ t * u) ∂unitScalarMeasure ∂μ := by
      apply integral_congr_ae
      filter_upwards [hpos] with t ht
      exact normalizedIntervalWindow_test_integral ht _ _

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

noncomputable def haarShiftDensity {T G : Type*} [MeasurableSpace T] [Sub G]
    (ν : Measure T) (z : T → G) (f : G → ℝ) (y : G) : ℝ :=
  densityMixture ν (fun t x => f (x - z t)) y

variable {T G : Type*} [MeasurableSpace T] [AddCommGroup G]
  [MeasurableSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]

theorem haarShiftDensity_measurable (ν : Measure T) [SFinite ν]
    {z : T → G} {f : G → ℝ} (hz : Measurable z) (hf : Measurable f) :
    Measurable (haarShiftDensity ν z f) := by
  have hm : Measurable (fun p : T × G => f (p.2 - z p.1)) :=
    hf.comp (measurable_snd.sub (hz.comp measurable_fst))
  exact hm.stronglyMeasurable.integral_prod_left'.measurable

theorem haarShiftDensity_cap (ν : Measure T) [IsProbabilityMeasure ν]
    {z : T → G} {f : G → ℝ} (hz : Measurable z) (hf : Measurable f)
    {C : ℝ} (hcap : ∀ x, f x ∈ Set.Icc (0 : ℝ) C) (y : G) :
    haarShiftDensity ν z f y ∈ Set.Icc (0 : ℝ) C := by
  have h := densityMixture_cap ν (fun t x => f (x - z t)) (fun _ => C) (integrable_const C)
    (fun x => (hf.comp (measurable_const.sub hz)).aestronglyMeasurable)
    (ae_of_all ν (fun t x => hcap (x - z t))) y
  simpa only [haarShiftDensity, integral_const, probReal_univ, one_smul] using h

theorem haarShiftDensity_probability (μ : Measure G) [μ.IsAddLeftInvariant]
    (ν : Measure T) [IsProbabilityMeasure ν]
    {z : T → G} {f : G → ℝ} (hz : Measurable z) (hf : Measurable f)
    [SFinite μ] (hfi : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x) (hmass : (∫ x, f x ∂μ) = 1) :
    (∀ x, 0 ≤ haarShiftDensity ν z f x) ∧ Integrable (haarShiftDensity ν z f) μ ∧
      (∫ x, haarShiftDensity ν z f x ∂μ) = 1 := by
  apply densityMixture_probability_density ν μ _
  · exact hf.comp (measurable_snd.sub (hz.comp measurable_fst))
  · exact ae_of_all ν (fun t => ⟨fun x => hf0 _, hfi.comp_sub_right (z t),
      (integral_sub_right_eq_self f (z t)).trans hmass⟩)

theorem haarShiftDensity_test_integral (μ : Measure G) [μ.IsAddLeftInvariant] [SFinite μ]
    (ν : Measure T) [IsProbabilityMeasure ν]
    {z : T → G} {f : G → ℝ} (hz : Measurable z) (hf : Measurable f)
    (hfi : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x) (hmass : (∫ x, f x ∂μ) = 1)
    (φ : G → ℝ) (hφ : Measurable φ) {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    (∫ x, haarShiftDensity ν z f x * φ x ∂μ) =
      ∫ t, ∫ u, f u * φ (u + z t) ∂μ ∂ν := by
  have hi := densityMixture_joint_integrable ν μ (fun t x => f (x - z t))
    (hf.comp (measurable_snd.sub (hz.comp measurable_fst)))
    (ae_of_all ν (fun t => ⟨fun x => hf0 _, hfi.comp_sub_right (z t),
      (integral_sub_right_eq_self f (z t)).trans hmass⟩))
  change (∫ x, densityMixture ν (fun t y => f (y - z t)) x * φ x ∂μ) = _
  rw [densityMixture_test_integral ν μ _ hi φ hφ hbound]
  apply integral_congr_ae
  exact ae_of_all ν (fun t => by
    have he := integral_add_right_eq_self (μ := μ) (fun x => f (x - z t) * φ x) (z t)
    simpa only [add_sub_cancel_right] using he.symm)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {T : Type*} [MeasurableSpace T]

noncomputable def independentShiftDensity (μ : Measure T) (z : T → ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  densityMixture μ (fun t x => f (x - z t))

theorem independentShiftDensity_measurable (μ : Measure T) [SFinite μ]
    {z : T → ℝ} {f : ℝ → ℝ} (hz : Measurable z) (hf : Measurable f) :
    Measurable (independentShiftDensity μ z f) := by
  have hm : Measurable (fun p : T × ℝ => f (p.2 - z p.1)) :=
    hf.comp (measurable_snd.sub (hz.comp measurable_fst))
  exact hm.stronglyMeasurable.integral_prod_left'.measurable

theorem independentShiftDensity_cap (μ : Measure T) [IsProbabilityMeasure μ]
    {z : T → ℝ} {f : ℝ → ℝ} (hz : Measurable z) (hf : Measurable f)
    {C : ℝ} (hcap : ∀ x, f x ∈ Set.Icc (0 : ℝ) C) (x : ℝ) :
    independentShiftDensity μ z f x ∈ Set.Icc (0 : ℝ) C := by
  have h := densityMixture_cap μ (fun t x => f (x - z t)) (fun _ => C) (integrable_const C)
    (fun x => (hf.comp (measurable_const.sub hz)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun t x => hcap (x - z t))) x
  simp only [integral_const, probReal_univ, one_smul] at h
  exact h

theorem independentShiftDensity_lipschitz (μ : Measure T) [IsProbabilityMeasure μ]
    {z : T → ℝ} {f : ℝ → ℝ} (hz : Measurable z) (L : ℝ≥0) (hf : LipschitzWith L f)
    {C : ℝ} (hcap : ∀ x, ‖f x‖ ≤ C) :
    LipschitzWith L (independentShiftDensity μ z f) := by
  have hi (x : ℝ) : Integrable (fun t => f (x - z t)) μ :=
    (integrable_const C).mono'
      (hf.continuous.measurable.comp (measurable_const.sub hz)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun t => hcap (x - z t)))
  have h := fixedKernelMixture_lipschitz μ (fun _ => (1 : ℝ)) (fun x t => f (x - z t)) L
    (integrable_const 1) (fun _ => zero_le_one) (by simp)
    (fun x => by simpa only [one_mul] using hi x) (fun t => by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [dist_sub_right] using hf.dist_le_mul (x - z t) (y - z t))
  simp only [one_mul] at h
  exact h

theorem independentShiftDensity_joint_integrable (μ : Measure T) [IsProbabilityMeasure μ]
    {z : T → ℝ} {f : ℝ → ℝ} (hz : Measurable z) (hf : Measurable f)
    (hfi : Integrable f) (hf0 : ∀ x, 0 ≤ f x) (hmass : (∫ x, f x) = 1) :
    Integrable (Function.uncurry (fun t x => f (x - z t))) (μ.prod volume) := by
  apply densityMixture_joint_integrable μ volume _
  · exact hf.comp (measurable_snd.sub (hz.comp measurable_fst))
  · filter_upwards [] with t
    exact ⟨fun x => hf0 _, hfi.comp_sub_right (z t),
      (integral_sub_right_eq_self f (z t)).trans hmass⟩

theorem independentShiftDensity_probability_density (μ : Measure T) [IsProbabilityMeasure μ]
    {z : T → ℝ} {f : ℝ → ℝ} (hz : Measurable z) (hf : Measurable f)
    (hfi : Integrable f) (hf0 : ∀ x, 0 ≤ f x) (hmass : (∫ x, f x) = 1) :
    (∀ x, 0 ≤ independentShiftDensity μ z f x) ∧ Integrable (independentShiftDensity μ z f) ∧
      (∫ x, independentShiftDensity μ z f x) = 1 := by
  apply densityMixture_probability_density μ volume _
  · exact hf.comp (measurable_snd.sub (hz.comp measurable_fst))
  · filter_upwards [] with t
    exact ⟨fun x => hf0 _, hfi.comp_sub_right (z t),
      (integral_sub_right_eq_self f (z t)).trans hmass⟩

theorem independentShiftDensity_test_integral (μ : Measure T) [IsProbabilityMeasure μ]
    {z : T → ℝ} {f : ℝ → ℝ} (hz : Measurable z) (hf : Measurable f)
    (hfi : Integrable f) (hf0 : ∀ x, 0 ≤ f x) (hmass : (∫ x, f x) = 1)
    (φ : ℝ → ℝ) (hφ : Measurable φ) {C : ℝ} (hcap : ∀ x, ‖φ x‖ ≤ C) :
    (∫ x, independentShiftDensity μ z f x * φ x) =
      ∫ t, ∫ u, f u * φ (u + z t) ∂volume ∂μ := by
  have hi : Integrable (Function.uncurry (fun t x => f (x - z t) * φ x)) (μ.prod volume) :=
    (independentShiftDensity_joint_integrable μ hz hf hfi hf0 hmass).mul_bdd
      (hφ.comp measurable_snd).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hcap p.2))
  calc
    (∫ x, independentShiftDensity μ z f x * φ x) =
        ∫ x, ∫ t, f (x - z t) * φ x ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact (integral_mul_const (φ x) _).symm
    _ = ∫ t, ∫ x, f (x - z t) * φ x ∂volume ∂μ := (integral_integral_swap hi).symm
    _ = ∫ t, ∫ u, f u * φ (u + z t) ∂volume ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with t
      have h := integral_add_right_eq_self (μ := volume) (fun x => f (x - z t) * φ x) (z t)
      simpa only [add_sub_cancel_right] using h.symm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem densityMixture_test_integral_complex {T X : Type*}
    [MeasurableSpace T] [MeasurableSpace X]
    (μ : Measure T) (ν : Measure X) [SFinite μ] [SFinite ν]
    (F : T → X → ℝ) (hF : Integrable (Function.uncurry F) (μ.prod ν))
    (φ : X → ℂ) (hφ : Measurable φ) {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    (∫ x, (densityMixture μ F x : ℂ) * φ x ∂ν) =
      ∫ t, ∫ x, (F t x : ℂ) * φ x ∂ν ∂μ := by
  have hi : Integrable (Function.uncurry (fun t x => (F t x : ℂ) * φ x)) (μ.prod ν) :=
    hF.ofReal.mul_bdd (hφ.comp measurable_snd).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hbound p.2))
  calc
    (∫ x, (densityMixture μ F x : ℂ) * φ x ∂ν) =
        ∫ x, ∫ t, (F t x : ℂ) * φ x ∂μ ∂ν := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [integral_mul_const, integral_complex_ofReal]
      rfl
    _ = ∫ t, ∫ x, (F t x : ℂ) * φ x ∂ν ∂μ := (integral_integral_swap hi).symm

theorem haarShiftDensity_test_integral_complex {T G : Type*} [MeasurableSpace T]
    [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddLeftInvariant] [SFinite μ]
    (ν : Measure T) [IsProbabilityMeasure ν]
    {z : T → G} {f : G → ℝ} (hz : Measurable z) (hf : Measurable f)
    (hfi : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x) (hmass : (∫ x, f x ∂μ) = 1)
    (φ : G → ℂ) (hφ : Measurable φ) {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    (∫ x, (haarShiftDensity ν z f x : ℂ) * φ x ∂μ) =
      ∫ t, ∫ u, (f u : ℂ) * φ (u + z t) ∂μ ∂ν := by
  have hi := densityMixture_joint_integrable ν μ (fun t x => f (x - z t))
    (hf.comp (measurable_snd.sub (hz.comp measurable_fst)))
    (ae_of_all ν (fun t => ⟨fun x => hf0 _, hfi.comp_sub_right (z t),
      (integral_sub_right_eq_self f (z t)).trans hmass⟩))
  change (∫ x, (densityMixture ν (fun t y => f (y - z t)) x : ℂ) * φ x ∂μ) = _
  rw [densityMixture_test_integral_complex ν μ _ hi φ hφ hbound]
  apply integral_congr_ae
  exact ae_of_all ν (fun t => by
    have he := integral_add_right_eq_self (μ := μ) (fun x => (f (x - z t) : ℂ) * φ x) (z t)
    simpa only [add_sub_cancel_right] using he.symm)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

noncomputable def pairedProductParameterMeasure (ι : Type*) [Fintype ι] :
    Measure (((ι → ℝ) × (ι → ℝ)) × ℝ) :=
  ((unitBoxMeasure ι).prod (unitBoxMeasure ι)).prod unitScalarMeasure

instance pairedProductParameterMeasure_probability :
    IsProbabilityMeasure (pairedProductParameterMeasure ι) :=
  inferInstanceAs (IsProbabilityMeasure (((unitBoxMeasure ι).prod (unitBoxMeasure ι)).prod unitScalarMeasure))

noncomputable def pairedProductWidth (p : ((ι → ℝ) × (ι → ℝ)) × ℝ) : ℝ := pairedAmplitude p.1

noncomputable def pairedProductShift (p : ((ι → ℝ) × (ι → ℝ)) × ℝ) : ℝ :=
  min (∏ i, p.1.1 i) (∏ i, p.1.2 i) * p.2

theorem pairedProductWidth_measurable : Measurable (pairedProductWidth (ι := ι)) :=
  pairedAmplitude_continuous.measurable.comp measurable_fst

theorem pairedProductShift_measurable : Measurable (pairedProductShift (ι := ι)) := by
  unfold pairedProductShift
  fun_prop

theorem pairedProductWidth_pos :
    ∀ᵐ p ∂pairedProductParameterMeasure ι, 0 < pairedProductWidth p :=
  Measure.quasiMeasurePreserving_fst.ae (pairedAmplitude_pos_ae (ι := ι))

theorem pairedProductWidth_inverse_integrable :
    Integrable (fun p => (pairedProductWidth p)⁻¹) (pairedProductParameterMeasure ι) :=
  pairedAmplitude_inverse_integrable.comp_fst unitScalarMeasure

theorem pairedProductWidth_inverse_integral_le :
    (∫ p, (pairedProductWidth p)⁻¹ ∂pairedProductParameterMeasure ι) ≤ 4 ^ Fintype.card ι := by
  change (∫ p, (pairedAmplitude p.1)⁻¹ ∂((unitBoxMeasure ι).prod (unitBoxMeasure ι)).prod unitScalarMeasure) ≤ _
  rw [integral_fun_fst (fun p : (ι → ℝ) × (ι → ℝ) => (pairedAmplitude p)⁻¹)]
  simpa using pairedAmplitude_inverse_integral_le (ι := ι)

noncomputable def pairedProductDensity (ι : Type*) [Fintype ι] : ℝ → ℝ :=
  randomIntervalDensity (pairedProductParameterMeasure ι) pairedProductWidth pairedProductShift

theorem pairedProductDensity_measurable : Measurable (pairedProductDensity ι) :=
  randomIntervalDensity_measurable _ _ _ pairedProductWidth_measurable pairedProductShift_measurable

theorem pairedProductDensity_cap (x : ℝ) :
    pairedProductDensity ι x ∈ Set.Icc (0 : ℝ) (4 ^ Fintype.card ι) := by
  have h := randomIntervalDensity_cap (pairedProductParameterMeasure ι) _ _
    pairedProductWidth_measurable pairedProductShift_measurable pairedProductWidth_pos
    pairedProductWidth_inverse_integrable x
  exact ⟨h.1, h.2.trans pairedProductWidth_inverse_integral_le⟩

theorem pairedProductDensity_probability_density :
    (∀ x, 0 ≤ pairedProductDensity ι x) ∧ Integrable (pairedProductDensity ι) ∧
      (∫ x, pairedProductDensity ι x) = 1 :=
  randomIntervalDensity_probability_density _ _ _ pairedProductWidth_measurable
    pairedProductShift_measurable pairedProductWidth_pos

theorem pairedProductDensity_test_sorted (φ : ℝ → ℝ) (hφ : Measurable φ)
    {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    (∫ x, pairedProductDensity ι x * φ x) =
      ∫ p, ∫ v, φ (pairedProductShift p + pairedProductWidth p * v)
        ∂unitScalarMeasure ∂pairedProductParameterMeasure ι :=
  randomIntervalDensity_test_integral _ _ _ pairedProductWidth_measurable
    pairedProductShift_measurable pairedProductWidth_pos φ hφ hbound

end Erdos3

end

end OAI
