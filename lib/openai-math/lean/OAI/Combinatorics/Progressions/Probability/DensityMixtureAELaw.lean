import OAI.Combinatorics.Progressions.Estimates.RealWeightPMF
import OAI.Combinatorics.Progressions.Estimates.SplitSmoothProductProfile

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def scalarDensityConvolution (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t, f (x - t) * g t

theorem scalarDensityConvolution_lipschitz (f g : ℝ → ℝ) (C D : ℝ≥0)
    (hf : Integrable f) (hg : Measurable g) (hcap : ∀ t, ‖g t‖ ≤ C)
    (hmove : ∀ a b, (∫ u, |f (u + a) - f (u + b)|) ≤ D * |a - b|) :
    LipschitzWith (C * D) (scalarDensityConvolution f g) := by
  apply kernelAverage_lipschitz volume (fun x t => f (x - t)) g C D
    (fun x => hf.comp_sub_left x) hg.aestronglyMeasurable hcap
  intro x y
  rw [← integral_neg_eq_self (fun t => |f (x - t) - f (y - t)|) volume]
  simpa only [sub_neg_eq_add, add_comm, Real.dist_eq] using hmove x y

theorem scalarDensityConvolution_cap (f g : ℝ → ℝ) (hf : Integrable f)
    (hf0 : ∀ t, 0 ≤ f t) (hfmass : (∫ t, f t) = 1) (hg : Measurable g)
    {C : ℝ} (hcap : ∀ t, g t ∈ Set.Icc (0 : ℝ) C) (x : ℝ) :
    scalarDensityConvolution f g x ∈ Set.Icc (0 : ℝ) C := by
  refine ⟨integral_nonneg (fun t => mul_nonneg (hf0 _) (hcap t).1), ?_⟩
  apply kernelAverage_cap volume (fun x t => f (x - t)) g (fun x => hf.comp_sub_left x)
    (fun x t => hf0 (x - t)) _ hg.aestronglyMeasurable hcap x
  intro y
  rw [integral_sub_left_eq_self f volume y, hfmass]

theorem scalarDensityConvolution_joint_integrable (f g : ℝ → ℝ)
    (hfm : Measurable f) (hgm : Measurable g) (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun p : ℝ × ℝ => f (p.1 - p.2) * g p.2) (volume.prod volume) := by
  have hm := (hfm.comp (measurable_fst.sub measurable_snd)).mul (hgm.comp measurable_snd)
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun t => (hf.comp_sub_right t).mul_const (g t)), ?_⟩
  have heq (t : ℝ) : (∫ x, ‖f (x - t) * g t‖) = (∫ x, ‖f x‖) * ‖g t‖ := by
    simp only [norm_mul, integral_mul_const]
    rw [integral_sub_right_eq_self (fun x => ‖f x‖) t]
  change Integrable (fun t => ∫ x, ‖f (x - t) * g t‖)
  simp_rw [heq]
  exact hg.norm.const_mul _

theorem scalarDensityConvolution_integrable (f g : ℝ → ℝ)
    (hfm : Measurable f) (hgm : Measurable g) (hf : Integrable f) (hg : Integrable g) :
    Integrable (scalarDensityConvolution f g) :=
  (scalarDensityConvolution_joint_integrable f g hfm hgm hf hg).integral_prod_left

theorem scalarDensityConvolution_mass (f g : ℝ → ℝ)
    (hfm : Measurable f) (hgm : Measurable g) (hf : Integrable f) (hg : Integrable g) :
    (∫ x, scalarDensityConvolution f g x) = (∫ x, f x) * ∫ x, g x := by
  have hi : Integrable (Function.uncurry (fun x t => f (x - t) * g t)) (volume.prod volume) :=
    scalarDensityConvolution_joint_integrable f g hfm hgm hf hg
  unfold scalarDensityConvolution
  rw [integral_integral_swap hi]
  simp_rw [integral_mul_const, integral_sub_right_eq_self f]
  exact integral_const_mul _ _

theorem scalarDensityConvolution_test_integral (f g φ : ℝ → ℝ)
    (hfm : Measurable f) (hgm : Measurable g) (hf : Integrable f) (hg : Integrable g)
    (hφ : Measurable φ) {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    (∫ x, scalarDensityConvolution f g x * φ x) =
      ∫ t, g t * ∫ u, f u * φ (u + t) := by
  have hi : Integrable (Function.uncurry (fun x t => (f (x - t) * g t) * φ x))
      (volume.prod volume) :=
    (scalarDensityConvolution_joint_integrable f g hfm hgm hf hg).mul_bdd
      (hφ.comp measurable_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hbound p.1))
  calc
    (∫ x, scalarDensityConvolution f g x * φ x) =
        ∫ x, ∫ t, (f (x - t) * g t) * φ x := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact (integral_mul_const (φ x) _).symm
    _ = ∫ t, ∫ x, (f (x - t) * g t) * φ x := integral_integral_swap hi
    _ = ∫ t, g t * ∫ u, f u * φ (u + t) := by
      apply integral_congr_ae
      filter_upwards [] with t
      have h := integral_add_right_eq_self (μ := volume) (fun x => (f (x - t) * g t) * φ x) t
      simp only [add_sub_cancel_right] at h
      rw [← h]
      simp only [mul_comm (f _), mul_assoc, integral_const_mul]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem realDensityMeasure_map_equiv {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) (μ : Measure X) (f : X → ℝ) :
    Measure.map e (realDensityMeasure μ f) =
      realDensityMeasure (Measure.map e μ) (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, realDensityMeasure, realDensityMeasure,
    withDensity_apply _ (e.measurable hs), withDensity_apply _ hs,
    e.restrict_map, e.measurableEmbedding.lintegral_map]
  simp only [e.symm_apply_apply]

theorem realDensityMeasure_pi {D : Type*} [Fintype D] {E : D → Type*}
    [∀ d, MeasurableSpace (E d)] (μ : ∀ d, Measure (E d)) [∀ d, SigmaFinite (μ d)]
    (f : ∀ d, E d → ℝ) (hf : ∀ d, Integrable (f d) (μ d)) (hf0 : ∀ d x, 0 ≤ f d x) :
    Measure.pi (fun d => realDensityMeasure (μ d) (f d)) =
      realDensityMeasure (Measure.pi μ) (tensorCutoffWeight f) := by
  let : ∀ d, IsFiniteMeasure (realDensityMeasure (μ d) (f d)) :=
    fun d => realDensityMeasure_finite (μ d) (f d) (hf d) (hf0 d)
  apply Measure.pi_eq
  intro s hs
  have hfi : Integrable (tensorCutoffWeight f) (Measure.pi μ) := Integrable.fintype_prod_dep hf
  rw [realDensityMeasure_apply _ (tensorCutoffWeight f) hfi
    (tensorCutoffWeight_nonneg f hf0) (MeasurableSet.univ_pi hs)]
  have hi : (∫ x in Set.univ.pi s, tensorCutoffWeight f x ∂Measure.pi μ) =
      ∏ d, ∫ y in s d, f d y ∂μ d := by
    rw [Measure.restrict_pi_pi]
    exact integral_fintype_prod_eq_prod f
  rw [hi, ENNReal.ofReal_prod_of_nonneg (fun d _ => integral_nonneg (hf0 d))]
  apply Finset.prod_congr rfl
  intro d _
  exact (realDensityMeasure_apply (μ d) (f d) (hf d) (hf0 d) (hs d)).symm

theorem finiteMeasure_eq_of_integrals {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ f : X → ℝ, Measurable f → (∫ x, f x ∂μ) = ∫ x, f x ∂ν) : μ = ν := by
  ext s hs
  apply (measureReal_eq_measureReal_iff (measure_ne_top _ _) (measure_ne_top _ _)).mp
  have hi := h (s.indicator (fun _ => (1 : ℝ))) (measurable_const.indicator hs)
  simpa only [integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one] using hi

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem imageLaw_eq_density_of_bounded_tests
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure X)
    (U : Ω → X) (hU : Measurable U)
    (f : X → ℝ) (hf : Measurable f) (hfi : Integrable f ν) (hf0 : ∀ x, 0 ≤ f x)
    (htest : ∀ φ : X → ℝ, Measurable φ → (∀ x, ‖φ x‖ ≤ 1) →
      (∫ a, φ (U a) ∂μ) = ∫ x, f x * φ x ∂ν) :
    μ.map U = realDensityMeasure ν f := by
  let : IsProbabilityMeasure (μ.map U) := inferInstance
  let : IsFiniteMeasure (realDensityMeasure ν f) := realDensityMeasure_finite ν f hfi hf0
  ext s hs
  apply (measureReal_eq_measureReal_iff (measure_ne_top _ _) (measure_ne_top _ _)).mp
  have hb : ∀ x, ‖s.indicator (fun _ => (1 : ℝ)) x‖ ≤ 1 := by
    intro x
    by_cases hx : x ∈ s <;> simp [hx]
  have ht := htest (s.indicator (fun _ => (1 : ℝ))) (measurable_const.indicator hs) hb
  rw [← integral_map hU.aemeasurable (measurable_const.indicator hs).aestronglyMeasurable,
    ← realDensityMeasure_integral ν f hf hf0] at ht
  simpa only [integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one] using ht

theorem scalarDensityConvolution_image_law (f g : ℝ → ℝ)
    (hfm : Measurable f) (hgm : Measurable g)
    (hf : Integrable f) (hg : Integrable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfmass : (∫ x, f x) = 1) (hgmass : (∫ x, g x) = 1) :
    ((realDensityMeasure volume g).prod (realDensityMeasure volume f)).map
      (fun p : ℝ × ℝ => p.2 + p.1) =
        realDensityMeasure volume (scalarDensityConvolution f g) := by
  let : IsProbabilityMeasure (realDensityMeasure volume f) :=
    realDensityMeasure_probability volume f hf hf0 hfmass
  let : IsProbabilityMeasure (realDensityMeasure volume g) :=
    realDensityMeasure_probability volume g hg hg0 hgmass
  have hm : Measurable (scalarDensityConvolution f g) :=
    ((hfm.comp (measurable_fst.sub measurable_snd)).mul
      (hgm.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable
  apply imageLaw_eq_density_of_bounded_tests _ volume _ (measurable_snd.add measurable_fst)
    _ hm (scalarDensityConvolution_integrable f g hfm hgm hf hg)
    (fun x => integral_nonneg (fun t => mul_nonneg (hf0 _) (hg0 _)))
  intro φ hφ hb
  have hi : Integrable (fun p : ℝ × ℝ => φ (p.2 + p.1))
      ((realDensityMeasure volume g).prod (realDensityMeasure volume f)) :=
    (integrable_const (1 : ℝ)).mono'
      (hφ.comp (measurable_snd.add measurable_fst)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hb _))
  change (∫ p : ℝ × ℝ, φ (p.2 + p.1)
    ∂(realDensityMeasure volume g).prod (realDensityMeasure volume f)) = _
  rw [integral_prod _ hi]
  simp_rw [realDensityMeasure_integral volume f hfm hf0]
  rw [realDensityMeasure_integral volume g hgm hg0]
  exact (scalarDensityConvolution_test_integral f g φ hfm hgm hf hg hφ hb).symm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem densityMixture_mappedTest {T Ω X : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure T) (ν : Measure Ω) (ξ : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [SFinite ξ]
    (U : T × Ω → X) (hU : Measurable U) (D : T → X → ℝ)
    (hD : Measurable (Function.uncurry D))
    (hprob : ∀ t, (∀ x, 0 ≤ D t x) ∧ Integrable (D t) ξ ∧ (∫ x, D t x ∂ξ) = 1)
    (hlaw : ∀ t, ν.map (fun a => U (t, a)) = realDensityMeasure ξ (D t))
    (φ : X → ℝ) (hφ : Measurable φ) {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    mappedTest (μ.prod ν) U φ = ∫ x, densityMixture μ D x*φ x ∂ξ := by
  have hi : Integrable (fun p => φ (U p)) (μ.prod ν) :=
    (integrable_const C).mono' (hφ.comp hU).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hbound (U p)))
  change (∫ p, φ (U p) ∂μ.prod ν) = _
  rw [integral_prod _ hi, densityMixture_test_integral μ ξ D
    (densityMixture_joint_integrable μ ξ D hD (Filter.Eventually.of_forall hprob)) φ hφ hbound]
  apply integral_congr_ae
  filter_upwards [] with t
  exact mappedTest_eq_density ν ξ (fun a => U (t, a))
    (hU.comp (measurable_const.prodMk measurable_id)) (D t)
    (hD.comp (measurable_const.prodMk measurable_id)) (hprob t).1 (hlaw t) φ hφ

theorem densityMixture_image_law {T Ω X : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure T) (ν : Measure Ω) (ξ : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [SFinite ξ]
    (U : T × Ω → X) (hU : Measurable U) (D : T → X → ℝ)
    (hD : Measurable (Function.uncurry D))
    (hprob : ∀ t, (∀ x, 0 ≤ D t x) ∧ Integrable (D t) ξ ∧ (∫ x, D t x ∂ξ) = 1)
    (hlaw : ∀ t, ν.map (fun a => U (t, a)) = realDensityMeasure ξ (D t)) :
    (μ.prod ν).map U = realDensityMeasure ξ (densityMixture μ D) := by
  have hp := densityMixture_probability_density μ ξ D hD (Filter.Eventually.of_forall hprob)
  have hm : Measurable (densityMixture μ D) :=
    hD.stronglyMeasurable.integral_prod_left'.measurable
  let : IsProbabilityMeasure ((μ.prod ν).map U) := inferInstance
  let : IsFiniteMeasure (realDensityMeasure ξ (densityMixture μ D)) :=
    realDensityMeasure_finite ξ _ hp.2.1 hp.1
  ext s hs
  apply (measureReal_eq_measureReal_iff (measure_ne_top _ _) (measure_ne_top _ _)).mp
  have hb : ∀ x, ‖s.indicator (fun _ => (1 : ℝ)) x‖ ≤ 1 := by
    intro x
    by_cases hx : x ∈ s <;> simp [hx]
  have ht := densityMixture_mappedTest μ ν ξ U hU D hD hprob hlaw
    (s.indicator (fun _ => (1 : ℝ))) (measurable_const.indicator hs) hb
  have himage : mappedTest (μ.prod ν) U (s.indicator (fun _ => (1 : ℝ))) =
      ∫ x, s.indicator (fun _ => (1 : ℝ)) x ∂(μ.prod ν).map U :=
    (integral_map hU.aemeasurable (measurable_const.indicator hs).aestronglyMeasurable).symm
  rw [himage, ← realDensityMeasure_integral ξ _ hm hp.1] at ht
  simpa only [integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one] using ht

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem pmf_support_ae {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : PMF X) : ∀ᵐ x ∂p.toMeasure, x ∈ p.support := by
  rw [ae_iff]
  change p.toMeasure p.supportᶜ = 0
  rw [p.toMeasure_apply_eq_zero_iff p.support_countable.measurableSet.compl]
  exact disjoint_compl_right

theorem pmf_real_mass {X : Type*} (p : PMF X) : (∑' x, (p x).toReal) = 1 := by
  rw [← ENNReal.tsum_toReal_eq (p.apply_ne_top), p.tsum_coe, ENNReal.toReal_one]

theorem pmf_real_integrable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : PMF X) : Integrable (fun x => (p x).toReal) Measure.count := by
  apply integrable_count_iff.mpr
  simpa only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using
    ENNReal.summable_toReal p.tsum_coe_ne_top

theorem pmf_realDensity_count {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : PMF X) : p.toMeasure = realDensityMeasure Measure.count (fun x => (p x).toReal) := by
  ext s hs
  rw [p.toMeasure_apply hs, realDensityMeasure, withDensity_apply _ hs]
  simp_rw [ENNReal.ofReal_toReal (p.apply_ne_top _)]
  rw [← lintegral_indicator (μ := Measure.count) hs p, lintegral_count]

theorem independentIntegerLaw_density {J : Type*} [Fintype J] (p : J → PMF ℤ) :
    Measure.pi (fun j => (p j).toMeasure) =
      realDensityMeasure (Measure.pi (fun _ : J => (Measure.count : Measure ℤ)))
        (fun z => ∏ j, (p j (z j)).toReal) := by
  simp_rw [pmf_realDensity_count]
  exact realDensityMeasure_pi (fun _ => Measure.count) (fun j z => (p j z).toReal)
    (fun j => pmf_real_integrable (p j)) (fun _ _ => ENNReal.toReal_nonneg)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Function Set

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem realDensityMeasure_map_embedding (e : X → Y) (he : MeasurableEmbedding e)
    (μ : Measure X) (f : X → ℝ) :
    Measure.map e (realDensityMeasure μ f) =
      realDensityMeasure (Measure.map e μ) (Function.extend e f (fun _ => 0)) := by
  ext S hS
  rw [Measure.map_apply he.measurable hS, realDensityMeasure, realDensityMeasure,
    withDensity_apply _ (hS.preimage he.measurable), withDensity_apply _ hS,
    he.restrict_map, he.lintegral_map]
  simp only [he.injective.extend_apply]

theorem realDensityMeasure_restrict_support (ν : Measure Y) (f : Y → ℝ)
    {S : Set Y} (hS : MeasurableSet S) (hf : ∀ y ∉ S, f y = 0) :
    realDensityMeasure (ν.restrict S) f = realDensityMeasure ν f := by
  unfold realDensityMeasure
  rw [← withDensity_indicator hS]
  congr 1
  ext y
  by_cases hy : y ∈ S
  · simp only [Set.indicator_of_mem hy]
  · simp only [Set.indicator_of_notMem hy, hf y hy, ENNReal.ofReal_zero]

theorem realDensityMeasure_smul_real (ν : Measure Y) (f : Y → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    realDensityMeasure (ENNReal.ofReal c • ν) f = realDensityMeasure ν (fun y => c * f y) := by
  unfold realDensityMeasure
  rw [withDensity_smul_measure]
  have he : (fun y => ENNReal.ofReal (c * f y)) =
      ENNReal.ofReal c • (fun y => ENNReal.ofReal (f y)) := by
    funext y
    exact ENNReal.ofReal_mul hc
  rw [he, withDensity_smul' _ _ ENNReal.ofReal_ne_top]

noncomputable def embeddingDensity (e : X → Y) (c : ℝ) (f : X → ℝ) (y : Y) : ℝ :=
  c * Function.extend e f (fun _ => 0) y

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem embeddingDensity_apply (e : X → Y) (he : Function.Injective e)
    (c : ℝ) (f : X → ℝ) (x : X) : embeddingDensity e c f (e x) = c * f x := by
  simp only [embeddingDensity, he.extend_apply]

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem embeddingDensity_zero (e : X → Y) (c : ℝ) (f : X → ℝ) (y : Y)
    (hy : y ∉ Set.range e) : embeddingDensity e c f y = 0 := by
  simp only [embeddingDensity, Function.extend_apply' f (fun _ => 0) y hy, mul_zero]

theorem embeddingDensity_measurable (e : X → Y) (he : MeasurableEmbedding e)
    (c : ℝ) (f : X → ℝ) (hf : Measurable f) : Measurable (embeddingDensity e c f) :=
  measurable_const.mul (he.measurable_extend hf measurable_const)

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem embeddingDensity_nonneg (e : X → Y) (he : Function.Injective e)
    {c : ℝ} (hc : 0 ≤ c) (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) (y : Y) :
    0 ≤ embeddingDensity e c f y := by
  by_cases hy : y ∈ Set.range e
  · obtain ⟨x, rfl⟩ := hy
    rw [embeddingDensity_apply e he]
    exact mul_nonneg hc (hf x)
  · rw [embeddingDensity_zero e c f y hy]

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem embeddingDensity_bound (e : X → Y) (he : Function.Injective e)
    {c B : ℝ} (hB : 0 ≤ B) (f : X → ℝ) (hf : ∀ x, c * f x ≤ B) (y : Y) :
    embeddingDensity e c f y ≤ B := by
  by_cases hy : y ∈ Set.range e
  · obtain ⟨x, rfl⟩ := hy
    rw [embeddingDensity_apply e he]
    exact hf x
  · rw [embeddingDensity_zero e c f y hy]
    exact hB

theorem embeddingDensity_law (e : X → Y) (he : MeasurableEmbedding e)
    (μ : Measure X) (ν : Measure Y) {c : ℝ} (hc : 0 ≤ c)
    (hmap : Measure.map e μ = ENNReal.ofReal c • ν.restrict (Set.range e)) (f : X → ℝ) :
    Measure.map e (realDensityMeasure μ f) = realDensityMeasure ν (embeddingDensity e c f) := by
  rw [realDensityMeasure_map_embedding e he, hmap, realDensityMeasure_smul_real _ _ hc]
  apply realDensityMeasure_restrict_support ν _ he.measurableSet_range
  exact embeddingDensity_zero e c f

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem measurePreserving_realDensity_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (π : X → Y) (hπ : MeasurePreserving π μ ν)
    (f : Y → ℝ) (hf : Measurable f) (hfi : Integrable f ν) (hf0 : ∀ y, 0 ≤ f y) :
    (realDensityMeasure μ (fun x => f (π x))).map π = realDensityMeasure ν f := by
  have hi := hπ.integrable_comp_of_integrable hfi
  let _ := realDensityMeasure_finite μ (fun x => f (π x)) hi (fun x => hf0 _)
  let _ := realDensityMeasure_finite ν f hfi hf0
  apply finiteMeasure_eq_of_integrals
  intro φ hφ
  rw [integral_map hπ.measurable.aemeasurable hφ.aestronglyMeasurable,
    realDensityMeasure_integral μ (fun x => f (π x)) (hf.comp hπ.measurable)
      (fun x => hf0 _) (fun x => φ (π x)),
    realDensityMeasure_integral ν f hf hf0 φ]
  have he := integral_map (μ := μ) hπ.measurable.aemeasurable (hf.mul hφ).aestronglyMeasurable
  simpa only [hπ.map_eq, Pi.mul_apply] using he.symm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem productDensity_pushforward {J : Type*} [Fintype J] {X Y : J → Type*}
    [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSpace (Y j)]
    (μ : ∀ j, Measure (X j)) (ν : ∀ j, Measure (Y j)) [∀ j, SigmaFinite (ν j)]
    (q : ∀ j, X j → Y j) (hq : ∀ j, Measurable (q j)) (f : ∀ j, Y j → ℝ)
    (hfi : ∀ j, Integrable (f j) (ν j)) (hf0 : ∀ j y, 0 ≤ f j y)
    (hlaw : ∀ j, Measure.map (q j) (μ j) = realDensityMeasure (ν j) (f j)) :
    Measure.map (fun x j => q j (x j)) (Measure.pi μ) =
      realDensityMeasure (Measure.pi ν) (tensorCutoffWeight f) := by
  have houtput : ∀ j, SigmaFinite (Measure.map (q j) (μ j)) := by
    intro j
    rw [hlaw j]
    let : IsFiniteMeasure (realDensityMeasure (ν j) (f j)) :=
      realDensityMeasure_finite (ν j) (f j) (hfi j) (hf0 j)
    exact IsFiniteMeasure.toSigmaFinite _
  rw [Measure.pi_map_pi (μ := μ) (f := q) (hμ := houtput) (fun j => (hq j).aemeasurable)]
  simp_rw [hlaw]
  exact realDensityMeasure_pi ν f hfi hf0

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem densityMixture_mappedTest_of_ae {T Ω X : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure T) (ν : Measure Ω) (ξ : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [SFinite ξ]
    (U : T × Ω → X) (hU : Measurable U) (D : T → X → ℝ)
    (hD : Measurable (Function.uncurry D))
    (hprob : ∀ᵐ t ∂μ, (∀ x, 0 ≤ D t x) ∧ Integrable (D t) ξ ∧ (∫ x, D t x ∂ξ) = 1)
    (hlaw : ∀ᵐ t ∂μ, ν.map (fun a => U (t, a)) = realDensityMeasure ξ (D t))
    (φ : X → ℝ) (hφ : Measurable φ) {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    mappedTest (μ.prod ν) U φ = ∫ x, densityMixture μ D x * φ x ∂ξ := by
  have hi : Integrable (fun p => φ (U p)) (μ.prod ν) :=
    (integrable_const C).mono' (hφ.comp hU).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hbound (U p)))
  change (∫ p, φ (U p) ∂μ.prod ν) = _
  rw [integral_prod _ hi, densityMixture_test_integral μ ξ D
    (densityMixture_joint_integrable μ ξ D hD hprob) φ hφ hbound]
  apply integral_congr_ae
  filter_upwards [hprob, hlaw] with t hp hl
  exact mappedTest_eq_density ν ξ (fun a => U (t, a))
    (hU.comp (measurable_const.prodMk measurable_id)) (D t)
    (hD.comp (measurable_const.prodMk measurable_id)) hp.1 hl φ hφ

theorem densityMixture_image_law_of_ae {T Ω X : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure T) (ν : Measure Ω) (ξ : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [SFinite ξ]
    (U : T × Ω → X) (hU : Measurable U) (D : T → X → ℝ)
    (hD : Measurable (Function.uncurry D))
    (hprob : ∀ᵐ t ∂μ, (∀ x, 0 ≤ D t x) ∧ Integrable (D t) ξ ∧ (∫ x, D t x ∂ξ) = 1)
    (hlaw : ∀ᵐ t ∂μ, ν.map (fun a => U (t, a)) = realDensityMeasure ξ (D t)) :
    (μ.prod ν).map U = realDensityMeasure ξ (densityMixture μ D) := by
  have hp := densityMixture_probability_density μ ξ D hD hprob
  have hm : Measurable (densityMixture μ D) := hD.stronglyMeasurable.integral_prod_left'.measurable
  apply imageLaw_eq_density_of_bounded_tests (μ.prod ν) ξ U hU _ hm hp.2.1 hp.1
  intro φ hφ hb
  exact densityMixture_mappedTest_of_ae μ ν ξ U hU D hD hprob hlaw φ hφ hb

end Erdos3

end

end OAI
