/-
Modified for ProveIt: construct the mapped joint probability instance from
its existing measurability proof for older Mathlib. Statements unchanged.
-/
import OAI.Combinatorics.Progressions.Estimates.UnitCoefficientSourceMarginal
import OAI.Combinatorics.Progressions.Sampling.MixedOutputGrid

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem retainedDensity_mappedTest {T Ω X : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure T) (ν : Measure Ω) (ξ : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [SFinite ξ]
    (U : T × Ω → X) (hU : Measurable U) (D : T → X → ℝ)
    (hD : Measurable (Function.uncurry D))
    (hprob : ∀ t, (∀ x, 0 ≤ D t x) ∧ Integrable (D t) ξ ∧ (∫ x, D t x ∂ξ) = 1)
    (hlaw : ∀ t, ν.map (fun a => U (t, a)) = realDensityMeasure ξ (D t))
    (φ : T × X → ℝ) (hφ : Measurable φ) {C : ℝ} (hbound : ∀ p, ‖φ p‖ ≤ C) :
    mappedTest (μ.prod ν) (fun p => (p.1, U p)) φ =
      ∫ p, D p.1 p.2*φ p ∂μ.prod ξ := by
  have hi : Integrable (fun p => φ (p.1, U p)) (μ.prod ν) :=
    (integrable_const C).mono' (hφ.comp (measurable_fst.prodMk hU)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hbound (p.1, U p)))
  have hDint := densityMixture_joint_integrable μ ξ D hD (Filter.Eventually.of_forall hprob)
  have hright : Integrable (fun p => D p.1 p.2*φ p) (μ.prod ξ) :=
    hDint.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  change (∫ p, φ (p.1, U p) ∂μ.prod ν) = _
  rw [integral_prod _ hi, integral_prod _ hright]
  apply integral_congr_ae
  filter_upwards [] with t
  exact mappedTest_eq_density ν ξ (fun a => U (t, a))
    (hU.comp (measurable_const.prodMk measurable_id)) (D t)
    (hD.comp (measurable_const.prodMk measurable_id)) (hprob t).1 (hlaw t)
    (fun x => φ (t, x)) (hφ.comp (measurable_const.prodMk measurable_id))

theorem retainedDensity_image_law {T Ω X : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure T) (ν : Measure Ω) (ξ : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [SFinite ξ]
    (U : T × Ω → X) (hU : Measurable U) (D : T → X → ℝ)
    (hD : Measurable (Function.uncurry D))
    (hprob : ∀ t, (∀ x, 0 ≤ D t x) ∧ Integrable (D t) ξ ∧ (∫ x, D t x ∂ξ) = 1)
    (hlaw : ∀ t, ν.map (fun a => U (t, a)) = realDensityMeasure ξ (D t)) :
    (μ.prod ν).map (fun p => (p.1, U p)) =
      realDensityMeasure (μ.prod ξ) (Function.uncurry D) := by
  have hi := densityMixture_joint_integrable μ ξ D hD (Filter.Eventually.of_forall hprob)
  have hnonneg : ∀ p, 0 ≤ Function.uncurry D p := fun p => (hprob p.1).1 p.2
  have hmap := measurable_fst.prodMk hU
  let : IsProbabilityMeasure ((μ.prod ν).map (fun p => (p.1, U p))) :=
    Measure.isProbabilityMeasure_map hmap.aemeasurable
  let : IsFiniteMeasure (realDensityMeasure (μ.prod ξ) (Function.uncurry D)) :=
    realDensityMeasure_finite _ _ hi hnonneg
  ext s hs
  apply (measureReal_eq_measureReal_iff (measure_ne_top _ _) (measure_ne_top _ _)).mp
  have hb : ∀ p, ‖s.indicator (fun _ => (1 : ℝ)) p‖ ≤ 1 := by
    intro p
    by_cases hp : p ∈ s <;> simp [hp]
  have ht := retainedDensity_mappedTest μ ν ξ U hU D hD hprob hlaw
    (s.indicator (fun _ => (1 : ℝ))) (measurable_const.indicator hs) hb
  have himage : mappedTest (μ.prod ν) (fun p => (p.1, U p)) (s.indicator (fun _ => (1 : ℝ))) =
      ∫ p, s.indicator (fun _ => (1 : ℝ)) p ∂(μ.prod ν).map (fun p => (p.1, U p)) :=
    (integral_map hmap.aemeasurable (measurable_const.indicator hs).aestronglyMeasurable).symm
  rw [himage] at ht
  have hd := realDensityMeasure_integral (μ.prod ξ) (Function.uncurry D) hD hnonneg
    (s.indicator (fun _ => (1 : ℝ)))
  have heq := ht.trans hd.symm
  simpa only [integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one] using heq

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem retained_density_l1_comparison {W Ω X : Type*}
    [MeasurableSpace W] [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure W) (ν : Measure Ω) (ξ : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [SFinite ξ]
    (U V : W × Ω → X) (hU : Measurable U) (hV : Measurable V)
    (f g : W → X → ℝ) (hfm : Measurable (Function.uncurry f)) (hgm : Measurable (Function.uncurry g))
    (hf : ∀ w, (∀ x, 0 ≤ f w x) ∧ Integrable (f w) ξ ∧ (∫ x, f w x ∂ξ) = 1)
    (hg : ∀ w, (∀ x, 0 ≤ g w x) ∧ Integrable (g w) ξ ∧ (∫ x, g w x ∂ξ) = 1)
    (hUf : ∀ w, ν.map (fun a => U (w, a)) = realDensityMeasure ξ (f w))
    (hVg : ∀ w, ν.map (fun a => V (w, a)) = realDensityMeasure ξ (g w))
    {ε : ℝ} (he : ∀ φ : W × X → ℝ, Measurable φ → (∀ p, ‖φ p‖ ≤ 1) →
      |mappedTest (μ.prod ν) (fun p => (p.1, U p)) φ-
        mappedTest (μ.prod ν) (fun p => (p.1, V p)) φ| ≤ ε) :
    (∫ p, |f p.1 p.2-g p.1 p.2| ∂μ.prod ξ) ≤ ε :=
  imageComparison_density_l1 (μ.prod ν) (μ.prod ξ) _ _
    (measurable_fst.prodMk hU) (measurable_fst.prodMk hV) _ _ hfm hgm
    (densityMixture_joint_integrable μ ξ f hfm (Filter.Eventually.of_forall hf))
    (densityMixture_joint_integrable μ ξ g hgm (Filter.Eventually.of_forall hg))
    (fun p => (hf p.1).1 p.2) (fun p => (hg p.1).1 p.2)
    (retainedDensity_image_law μ ν ξ U hU f hfm hf hUf)
    (retainedDensity_image_law μ ν ξ V hV g hgm hg hVg) he

theorem retained_density_grid_comparison {W Ω J : Type*}
    [MeasurableSpace W] [MeasurableSpace Ω] [Fintype J]
    (μ : Measure W) (ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (U V : W × Ω → (J → ℝ)) (hU : Measurable U) (hV : Measurable V)
    (f g : W → (J → ℝ) → ℝ) (hfm : Measurable (Function.uncurry f)) (hgm : Measurable (Function.uncurry g))
    (hf : ∀ w, (∀ x, 0 ≤ f w x) ∧ Integrable (f w) ∧ (∫ x, f w x) = 1)
    (hg : ∀ w, (∀ x, 0 ≤ g w x) ∧ Integrable (g w) ∧ (∫ x, g w x) = 1)
    (hUf : ∀ w, ν.map (fun a => U (w, a)) = realDensityMeasure volume (f w))
    (hVg : ∀ w, ν.map (fun a => V (w, a)) = realDensityMeasure volume (g w))
    {ε : ℝ} (he : ∀ φ : W × (J → ℝ) → ℝ, Measurable φ → (∀ p, ‖φ p‖ ≤ 1) →
      |mappedTest (μ.prod ν) (fun p => (p.1, U p)) φ-
        mappedTest (μ.prod ν) (fun p => (p.1, V p)) φ| ≤ ε)
    {Kf Kg : ℝ≥0} (hfLip : ∀ w, LipschitzWith Kf (f w)) (hgLip : ∀ w, LipschitzWith Kg (g w))
    (a S : J → ℝ) (hS : ∀ j, 0 < S j) {R δ G : ℝ}
    (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ j, 1/S j ≤ δ)
    (hfs : ∀ w x, R < ‖x‖ → f w x = 0) (hgs : ∀ w x, R < ‖x‖ → g w x = 0)
    (s : Finset (J → ℤ)) (mask : W → (J → ℤ) → ℝ) (φ : W → (J → ℤ) → ℂ)
    (hG : 0 ≤ G) (hm : ∀ w k, k ∈ s → |mask w k| ≤ G) (hφ : ∀ w k, k ∈ s → ‖φ w k‖ ≤ 1) :
    ‖∫ w, gridDensityTest (f w) a S s (mask w) (φ w)-
      gridDensityTest (g w) a S s (mask w) (φ w) ∂μ‖ ≤
      G*(ε+(2*R+2)^Fintype.card J*((Kf : ℝ)+Kg)*δ) := by
  have hl1 := retained_density_l1_comparison μ ν volume U V hU hV f g hfm hgm hf hg hUf hVg he
  have hfi := densityMixture_joint_integrable μ volume f hfm (Filter.Eventually.of_forall hf)
  have hgi := densityMixture_joint_integrable μ volume g hgm (Filter.Eventually.of_forall hg)
  simpa only [probReal_univ, one_mul] using
    partial_gridDensityTest_error μ f g hfLip hgLip a S hS hR hδ hδ1 hmesh hfs hgs s mask φ hG hm hφ
      (hfi.sub hgi) hl1

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem affineProductProfile_measurable_center {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (c x : Ω → I → ℝ) (w : I → ℝ)
    (hc : ∀ i, Measurable (fun a => c a i)) (hx : ∀ i, Measurable (fun a => x a i)) :
    Measurable (fun a => affineProductProfile (c a) w (x a)) := by
  unfold affineProductProfile affineProbabilityProfile
  apply Finset.measurable_prod
  intro i _
  exact measurable_const.mul (smoothProbabilityProfile_contDiff.continuous.measurable.comp
    (((hx i).sub (hc i)).div_const (w i)))

def regularizedImageMap {Ω I : Type*} (δ : ℝ≥0) (U : Ω → I → ℝ)
    (p : Ω × (I → ℝ)) : I → ℝ := U p.1 + (δ : ℝ) • p.2

noncomputable def regularizedImageDensity {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) (U : Ω → I → ℝ) (δ : ℝ≥0) : (I → ℝ) → ℝ :=
  densityMixture μ (fun a => affineProductProfile (U a) (fun _ => (δ : ℝ)))

theorem regularizedImageMap_measurable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (δ : ℝ≥0) (U : Ω → I → ℝ) (hU : Measurable U) : Measurable (regularizedImageMap δ U) :=
  (hU.comp measurable_fst).add (measurable_snd.const_smul (δ : ℝ))

theorem regularizedImageDensity_joint_measurable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (U : Ω → I → ℝ) (hU : Measurable U) (δ : ℝ≥0) :
    Measurable (fun p : Ω × (I → ℝ) => affineProductProfile (U p.1) (fun _ => (δ : ℝ)) p.2) :=
  affineProductProfile_measurable_center _ _ _
    (fun i => (measurable_pi_apply i).comp (hU.comp measurable_fst))
    (fun i => (measurable_pi_apply i).comp measurable_snd)

theorem regularizedImageDensity_measurable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [SFinite μ] (U : Ω → I → ℝ) (hU : Measurable U) (δ : ℝ≥0) :
    Measurable (regularizedImageDensity μ U δ) :=
  (regularizedImageDensity_joint_measurable U hU δ).stronglyMeasurable.integral_prod_left'.measurable

theorem regularizedImageDensity_probability {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → I → ℝ) (hU : Measurable U)
    (δ : ℝ≥0) (hδ : 0 < δ) :
    (∀ x, 0 ≤ regularizedImageDensity μ U δ x) ∧ Integrable (regularizedImageDensity μ U δ) ∧
      (∫ x, regularizedImageDensity μ U δ x) = 1 := by
  apply densityMixture_probability_density μ volume _ (regularizedImageDensity_joint_measurable U hU δ)
  exact Filter.Eventually.of_forall (fun a =>
    ⟨affineProductProfile_nonneg (U a) _ (fun _ => hδ),
      affineProductProfile_integrable (U a) _ (fun _ => hδ),
      affineProductProfile_integral (U a) _ (fun _ => hδ)⟩)

theorem regularizedImageDensity_bounds {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → I → ℝ) (hU : Measurable U)
    (δ : ℝ≥0) (hδ : 0 < δ) :
    (∀ x, regularizedImageDensity μ U δ x ∈ Set.Icc (0 : ℝ) (δ⁻¹ ^ Fintype.card I : ℝ≥0)) ∧
      LipschitzWith (affineProductProfileLip I δ) (regularizedImageDensity μ U δ) := by
  apply densityMixture_uniform_bound μ _ (δ⁻¹ ^ Fintype.card I) (affineProductProfileLip I δ)
  · intro x
    exact ((regularizedImageDensity_joint_measurable U hU δ).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro a
    refine ⟨?_, affineProductProfile_lipschitz (U a) (fun _ => (δ : ℝ)) hδ (fun _ => le_rfl)⟩
    intro x
    have hn := affineProductProfile_nonneg (U a) (fun _ => (δ : ℝ)) (fun _ => hδ) x
    have hc := affineProductProfile_cap (U a) (fun _ => (δ : ℝ)) hδ (fun _ => le_rfl) x
    rw [Real.norm_of_nonneg hn] at hc
    exact ⟨hn, hc⟩

theorem regularizedImageDensity_image_law {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → I → ℝ) (hU : Measurable U)
    (δ : ℝ≥0) (hδ : 0 < δ) :
    (μ.prod (unitCoefficientSource I)).map (regularizedImageMap δ U) =
      realDensityMeasure volume (regularizedImageDensity μ U δ) := by
  apply densityMixture_image_law μ (unitCoefficientSource I) volume _
    (regularizedImageMap_measurable δ U hU)
    (fun a => affineProductProfile (U a) (fun _ => (δ : ℝ)))
    (regularizedImageDensity_joint_measurable U hU δ)
  · intro a
    exact ⟨affineProductProfile_nonneg (U a) _ (fun _ => hδ),
      affineProductProfile_integrable (U a) _ (fun _ => hδ),
      affineProductProfile_integral (U a) _ (fun _ => hδ)⟩
  · intro a
    exact unitCoefficientSource_affine_law (U a) (fun _ => (δ : ℝ)) (fun _ => hδ)

theorem regularizedImageDensity_support {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) (U : Ω → I → ℝ) (δ : ℝ≥0) (hδ : 0 < δ)
    {R : ℝ} (hR : 0 ≤ R) (hU : ∀ᵐ a ∂μ, ‖U a‖ ≤ R) :
    ∀ x, R+δ < ‖x‖ → regularizedImageDensity μ U δ x = 0 := by
  intro x hx
  apply integral_eq_zero_of_ae
  filter_upwards [hU] with a ha
  apply affineProductProfile_zero_outside (U a) (fun _ => (δ : ℝ)) (fun _ => hδ)
    (add_nonneg hR δ.coe_nonneg) _ x hx
  intro i
  exact add_le_add ((Real.norm_eq_abs (U a i)).symm.trans_le ((norm_le_pi_norm (U a) i).trans ha)) le_rfl

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem conditionalRegularizedDensity_measurable {W X I : Type*}
    [MeasurableSpace W] [MeasurableSpace X] [Fintype I]
    (ν : Measure X) [SFinite ν] (U : W × X → I → ℝ) (hU : Measurable U) (δ : ℝ≥0) :
    Measurable (fun p : W × (I → ℝ) => regularizedImageDensity ν (fun x => U (p.1, x)) δ p.2) := by
  have hm := affineProductProfile_measurable_center
    (fun p : (W × (I → ℝ)) × X => U (p.1.1, p.2)) (fun p => p.1.2) (fun _ => (δ : ℝ))
    (fun i => (measurable_pi_apply i).comp (hU.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
    (fun i => (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem conditionalRegularizedDensity_image_law {W X I : Type*}
    [MeasurableSpace W] [MeasurableSpace X] [Fintype I]
    (μ : Measure W) (ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (U : W × X → I → ℝ) (hU : Measurable U) (δ : ℝ≥0) (hδ : 0 < δ) :
    (μ.prod (ν.prod (unitCoefficientSource I))).map
      (fun p => (p.1, U (p.1, p.2.1)+(δ : ℝ) • p.2.2)) =
      realDensityMeasure (μ.prod volume)
        (fun p => regularizedImageDensity ν (fun x => U (p.1, x)) δ p.2) := by
  have hmap : Measurable (fun p : W × (X × (I → ℝ)) => U (p.1, p.2.1)+(δ : ℝ) • p.2.2) :=
    (hU.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).add
      ((measurable_snd.comp measurable_snd).const_smul (δ : ℝ))
  apply retainedDensity_image_law μ (ν.prod (unitCoefficientSource I)) volume _ hmap
    (fun w => regularizedImageDensity ν (fun x => U (w, x)) δ)
    (conditionalRegularizedDensity_measurable ν U hU δ)
  · intro w
    exact regularizedImageDensity_probability ν _ (hU.comp (measurable_const.prodMk measurable_id)) δ hδ
  · intro w
    exact regularizedImageDensity_image_law ν _ (hU.comp (measurable_const.prodMk measurable_id)) δ hδ

theorem conditionalRegularizedDensity_test_error {W X I : Type*}
    [MeasurableSpace W] [MeasurableSpace X] [Fintype I]
    (μ : Measure W) (ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (U : W × X → I → ℝ) (hU : Measurable U) (δ : ℝ≥0) (hδ : 0 < δ) {ε : ℝ}
    (herr : ∀ᵐ w ∂μ, ∀ f : (I → ℝ) → ℝ, Measurable f → (∀ y, ‖f y‖ ≤ 1) →
      |(∫ y, regularizedImageDensity ν (fun x => U (w, x)) δ y*f y)-
        mappedTest ν (fun x => U (w, x)) f| ≤ ε)
    (φ : W × (I → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ p, ‖φ p‖ ≤ 1) :
    |(∫ p, regularizedImageDensity ν (fun x => U (p.1, x)) δ p.2*φ p ∂μ.prod volume) -
      ∫ p, φ (p.1, U p) ∂μ.prod ν| ≤ ε := by
  have hD := conditionalRegularizedDensity_measurable ν U hU δ
  have hp (w) := regularizedImageDensity_probability ν (fun x => U (w, x))
    (hU.comp (measurable_const.prodMk measurable_id)) δ hδ
  have hj := densityMixture_joint_integrable μ volume
    (fun w => regularizedImageDensity ν (fun x => U (w, x)) δ) hD (Filter.Eventually.of_forall hp)
  have hd : Integrable (fun p : W × (I → ℝ) =>
      regularizedImageDensity ν (fun x => U (p.1, x)) δ p.2*φ p) (μ.prod volume) :=
    hj.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  have hi := mappedTest_integrable (μ.prod ν) (fun p => (p.1, U p))
    (measurable_fst.prodMk hU) φ hφ hbound
  rw [integral_prod _ hd, integral_prod _ hi,
    ← integral_sub hd.integral_prod_left hi.integral_prod_left]
  have hb : ∀ᵐ w ∂μ, ‖(∫ y, regularizedImageDensity ν (fun x => U (w, x)) δ y*φ (w, y))-
      ∫ x, φ (w, U (w, x)) ∂ν‖ ≤ ε := by
    filter_upwards [herr] with w hw
    exact hw (fun y => φ (w, y)) (hφ.comp (measurable_const.prodMk measurable_id)) (fun y => hbound (w, y))
  have he := norm_integral_le_of_norm_le (integrable_const ε (μ := μ)) hb
  simpa only [Real.norm_eq_abs, integral_const, probReal_univ, one_smul] using he

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped NNReal

theorem conditionalRegularizedDensity_comparison {W X I : Type*}
    [MeasurableSpace W] [MeasurableSpace X] [Fintype I]
    (μ : Measure W) (ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (U V : W × X → I → ℝ) (hU : Measurable U) (hV : Measurable V) (δ : ℝ≥0) (hδ : 0 < δ) {ε : ℝ}
    (herr : ∀ᵐ w ∂μ, ∀ f : (I → ℝ) → ℝ, Measurable f → (∀ y, ‖f y‖ ≤ 1) →
      |(∫ y, regularizedImageDensity ν (fun x => U (w, x)) δ y*f y)-
        mappedTest ν (fun x => V (w, x)) f| ≤ ε)
    (φ : W × (I → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ p, ‖φ p‖ ≤ 1) :
    |(∫ p, regularizedImageDensity ν (fun x => U (p.1, x)) δ p.2*φ p ∂μ.prod volume) -
      ∫ p, φ (p.1, V p) ∂μ.prod ν| ≤ ε := by
  have hD := conditionalRegularizedDensity_measurable ν U hU δ
  have hp (w) := regularizedImageDensity_probability ν (fun x => U (w, x))
    (hU.comp (measurable_const.prodMk measurable_id)) δ hδ
  have hj := densityMixture_joint_integrable μ volume
    (fun w => regularizedImageDensity ν (fun x => U (w, x)) δ) hD (Filter.Eventually.of_forall hp)
  have hd : Integrable (fun p : W × (I → ℝ) =>
      regularizedImageDensity ν (fun x => U (p.1, x)) δ p.2*φ p) (μ.prod volume) :=
    hj.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  have hi := mappedTest_integrable (μ.prod ν) (fun p => (p.1, V p))
    (measurable_fst.prodMk hV) φ hφ hbound
  rw [integral_prod _ hd, integral_prod _ hi,
    ← integral_sub hd.integral_prod_left hi.integral_prod_left]
  have hb : ∀ᵐ w ∂μ, ‖(∫ y, regularizedImageDensity ν (fun x => U (w, x)) δ y*φ (w, y))-
      ∫ x, φ (w, V (w, x)) ∂ν‖ ≤ ε := by
    filter_upwards [herr] with w hw
    exact hw (fun y => φ (w, y)) (hφ.comp (measurable_const.prodMk measurable_id)) (fun y => hbound (w, y))
  have he := norm_integral_le_of_norm_le (integrable_const ε (μ := μ)) hb
  simpa only [Real.norm_eq_abs, integral_const, probReal_univ, one_smul] using he

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

theorem unitCoefficientSource_sigma {D : Type*} [Fintype D]
    (I : D → Type*) [∀ d, Fintype (I d)] :
    unitCoefficientSource (Σ d, I d) = sigmaAxisMeasure (fun d => unitCoefficientSource (I d)) := by
  let : IsProbabilityMeasure (realDensityMeasure volume smoothProbabilityProfile) :=
    realDensityMeasure_probability volume _
      (smoothProbabilityProfile_contDiff.continuous.integrable_of_hasCompactSupport
        smoothProbabilityProfile_compact)
      (fun r => (smoothProbabilityProfile_range r).1) smoothProbabilityProfile_integral
  unfold sigmaAxisMeasure
  simp only [unitCoefficientSource_pi]
  exact (sigmaProductMeasure_flatten
    (fun _ : Σ d, I d => realDensityMeasure volume smoothProbabilityProfile)).symm

theorem regularizedImageDensity_sigma {D : Type*} [Fintype D]
    {I O : D → Type*} [∀ d, Fintype (I d)] [∀ d, Fintype (O d)]
    (μ : ∀ d, Measure (I d → ℝ)) [∀ d, IsProbabilityMeasure (μ d)]
    (U : ∀ d, (I d → ℝ) → (O d → ℝ)) (δ : ℝ≥0) (v : (Σ d, O d) → ℝ) :
    regularizedImageDensity (sigmaAxisMeasure μ) (sigmaAxisSampler U) δ v =
      ∏ d, regularizedImageDensity (μ d) (U d) δ (fun o => v ⟨d, o⟩) := by
  unfold regularizedImageDensity densityMixture
  rw [sigmaAxisMeasure_integral]
  have he (x : ∀ d, I d → ℝ) :
      affineProductProfile (sigmaAxisSampler U ((sigmaAxisCoordinates I).symm x))
        (fun _ => (δ : ℝ)) v =
      ∏ d, affineProductProfile (U d (x d)) (fun _ => (δ : ℝ)) (fun o => v ⟨d, o⟩) := by
    simp only [affineProductProfile, Fintype.prod_sigma]
    rfl
  simp_rw [he]
  exact integral_fintype_prod_eq_prod (μ := μ)
    (fun d x => affineProductProfile (U d x) (fun _ => (δ : ℝ)) (fun o => v ⟨d, o⟩))

end Erdos3

end

end OAI
