import OAI.Combinatorics.Progressions.Sampling.ControlledJointGrid
import OAI.Combinatorics.Progressions.Sampling.JointSamplerProductivity

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable (μ : Measure C) (law : C → FiniteProbabilityWeights Ω)
variable (hweight : ∀ x, Measurable (fun c => (law c).weight x))

noncomputable def centeredFiniteProbabilityMeasure : Measure (C × Ω) :=
  realDensityMeasure (μ.prod Measure.count) (centeredFiniteWeightDensity law)

include hweight

theorem centeredFiniteProbabilityMeasure_probability [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (centeredFiniteProbabilityMeasure μ law) :=
  realDensityMeasure_probability _ _ (centeredFiniteWeightDensity_integrable law hweight μ)
    (centeredFiniteWeightDensity_nonneg law) (centeredFiniteWeightDensity_integral law hweight μ)

theorem centeredFiniteProbabilityMeasure_ae_positive_weight :
    ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law, 0 < (law z.1).weight z.2 := by
  exact realDensityMeasure_ae_of_support (μ.prod Measure.count) (centeredFiniteWeightDensity law)
    (centeredFiniteWeightDensity_measurable law hweight) _ (fun z hz =>
      lt_of_le_of_ne (centeredFiniteWeightDensity_nonneg law z) (Ne.symm hz))

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem centeredFinite_weight_integrable [IsFiniteMeasure μ] (x : Ω) :
    Integrable (fun c => (law c).weight x) μ :=
  Integrable.of_bound (hweight x).aestronglyMeasurable 1 (ae_of_all μ (fun c => by
    rw [Real.norm_of_nonneg ((law c).nonneg x)]
    exact centeredFiniteWeightDensity_le_one law (c, x)))

omit μ [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem centeredFinite_mean_measurable (f : C → Ω → ℝ)
    (hf : ∀ x, Measurable (fun c => f c x)) :
    Measurable (fun c => (law c).mean (f c)) :=
  Finset.measurable_sum _ (fun x _ => (hweight x).mul (hf x))

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem centeredFinite_mean_integrable (f : C → Ω → ℝ)
    (hf : ∀ x, Integrable (fun c => f c x) μ) :
    Integrable (fun c => (law c).mean (f c)) μ := by
  apply integrable_finsetSum
  intro x _
  exact (hf x).bdd_mul (hweight x).aestronglyMeasurable (ae_of_all μ (fun c => by
    rw [Real.norm_of_nonneg ((law c).nonneg x)]
    exact centeredFiniteWeightDensity_le_one law (c, x)))

theorem centeredFiniteProbabilityMeasure_integral [IsProbabilityMeasure μ]
    (f : C × Ω → ℝ) (hf : Integrable f (centeredFiniteProbabilityMeasure μ law)) :
    (∫ z, f z ∂centeredFiniteProbabilityMeasure μ law) =
      ∫ c, (law c).mean (fun x => f (c, x)) ∂μ := by
  have hi := (integrable_withDensity_iff_integrable_smul'
    (centeredFiniteWeightDensity_measurable law hweight).ennreal_ofReal
    (ae_of_all (μ.prod Measure.count) (fun _ => ENNReal.ofReal_lt_top))).mp hf
  simp only [ENNReal.toReal_ofReal (centeredFiniteWeightDensity_nonneg law _), smul_eq_mul] at hi
  rw [centeredFiniteProbabilityMeasure, realDensityMeasure_integral _ _
    (centeredFiniteWeightDensity_measurable law hweight) (centeredFiniteWeightDensity_nonneg law),
    integral_prod _ hi]
  simp only [integral_count, centeredFiniteWeightDensity, FiniteProbabilityWeights.mean]

theorem centeredFiniteProbabilityMeasure_integral_bounded [IsProbabilityMeasure μ]
    (f : C × Ω → ℝ) (hf : Measurable f) {M : ℝ} (hbound : ∀ z, ‖f z‖ ≤ M) :
    (∫ z, f z ∂centeredFiniteProbabilityMeasure μ law) =
      ∫ c, (law c).mean (fun x => f (c, x)) ∂μ := by
  let := centeredFiniteProbabilityMeasure_probability μ law hweight
  exact centeredFiniteProbabilityMeasure_integral μ law hweight f
    (Integrable.of_bound hf.aestronglyMeasurable M (ae_of_all _ hbound))

theorem centeredFiniteProbabilityMeasure_complexIntegral [IsProbabilityMeasure μ]
    (f : C × Ω → ℂ) (hf : Integrable f (centeredFiniteProbabilityMeasure μ law)) :
    (∫ z, f z ∂centeredFiniteProbabilityMeasure μ law) =
      ∫ c, (law c).complexMean (fun x => f (c, x)) ∂μ := by
  have hi := (integrable_withDensity_iff_integrable_smul'
    (centeredFiniteWeightDensity_measurable law hweight).ennreal_ofReal
    (ae_of_all (μ.prod Measure.count) (fun _ => ENNReal.ofReal_lt_top))).mp hf
  simp only [ENNReal.toReal_ofReal (centeredFiniteWeightDensity_nonneg law _), Complex.real_smul] at hi
  rw [centeredFiniteProbabilityMeasure, realDensityMeasure_integral_complex _ _
    (centeredFiniteWeightDensity_measurable law hweight) (centeredFiniteWeightDensity_nonneg law),
    integral_prod _ hi]
  simp only [integral_count, centeredFiniteWeightDensity, FiniteProbabilityWeights.complexMean]

theorem centeredFiniteProbabilityMeasure_complexIntegral_bounded [IsProbabilityMeasure μ]
    (f : C × Ω → ℂ) (hf : Measurable f) {M : ℝ} (hbound : ∀ z, ‖f z‖ ≤ M) :
    (∫ z, f z ∂centeredFiniteProbabilityMeasure μ law) =
      ∫ c, (law c).complexMean (fun x => f (c, x)) ∂μ := by
  let := centeredFiniteProbabilityMeasure_probability μ law hweight
  exact centeredFiniteProbabilityMeasure_complexIntegral μ law hweight f
    (Integrable.of_bound hf.aestronglyMeasurable M (ae_of_all _ hbound))

theorem centeredFiniteProbabilityMeasure_real_event [IsProbabilityMeasure μ]
    (event : Set (C × Ω)) (hevent : MeasurableSet event) :
    (centeredFiniteProbabilityMeasure μ law).real event =
      ∫ c, (law c).mean (fun x => if (c, x) ∈ event then 1 else 0) ∂μ := by
  rw [← integral_indicator_one (μ := centeredFiniteProbabilityMeasure μ law) hevent]
  have hmeas : Measurable (event.indicator (1 : C × Ω → ℝ)) :=
    measurable_const.indicator hevent
  have hbound (z : C × Ω) : ‖event.indicator (1 : C × Ω → ℝ) z‖ ≤ 1 := by
    by_cases hz : z ∈ event <;> simp [hz]
  rw [centeredFiniteProbabilityMeasure_integral_bounded μ law hweight _ hmeas hbound]
  rfl

theorem centeredFiniteProbabilityMeasure_real_finset_fiber [IsProbabilityMeasure μ]
    (F : Finset Ω) :
    (centeredFiniteProbabilityMeasure μ law).real {z | z.2 ∈ F} =
      ∫ c, (law c).mass F ∂μ := by
  have hevent : MeasurableSet {z : C × Ω | z.2 ∈ F} :=
    (Finset.measurableSet F).preimage measurable_snd
  have h := centeredFiniteProbabilityMeasure_real_event μ law hweight _ hevent
  refine h.trans (integral_congr_ae (ae_of_all μ (fun c => ?_)))
  calc
    _ = (law c).mean (fun x => if x ∈ F then 1 else 0) := by
      apply congrArg (law c).mean
      funext x
      by_cases hx : x ∈ F <;> simp [hx]
    _ = _ := (law c).mean_indicator F

omit μ law hweight in
theorem centeredFinite_finite_event_measurable (F : C → Finset Ω)
    (hF : ∀ x, MeasurableSet {c | x ∈ F c}) :
    MeasurableSet {z : C × Ω | z.2 ∈ F z.1} := by
  have hm : Measurable (fun z : C × Ω => if z.2 ∈ F z.1 then (1 : ℝ) else 0) :=
    measurable_from_prod_countable_left
      (fun x => measurable_const.ite (hF x) measurable_const)
  have he : {z : C × Ω | z.2 ∈ F z.1} =
      (fun z : C × Ω => if z.2 ∈ F z.1 then (1 : ℝ) else 0) ⁻¹' {1} := by
    ext z
    by_cases hz : z.2 ∈ F z.1 <;> simp [hz]
  rw [he]
  exact hm (measurableSet_singleton 1)

theorem centeredFiniteProbabilityMeasure_real_finite_events [IsProbabilityMeasure μ]
    (F : C → Finset Ω) (hevent : MeasurableSet {z : C × Ω | z.2 ∈ F z.1}) :
    (centeredFiniteProbabilityMeasure μ law).real {z | z.2 ∈ F z.1} =
      ∫ c, (law c).mass (F c) ∂μ := by
  have h := centeredFiniteProbabilityMeasure_real_event μ law hweight _ hevent
  refine h.trans (integral_congr_ae (ae_of_all μ (fun c => ?_)))
  calc
    _ = (law c).mean (fun x => if x ∈ F c then 1 else 0) := by
      apply congrArg (law c).mean
      funext x
      by_cases hx : x ∈ F c <;> simp [hx]
    _ = _ := (law c).mean_indicator (F c)

theorem centeredFiniteProbabilityMeasure_real_finite_events_of_measurable_membership
    [IsProbabilityMeasure μ] (F : C → Finset Ω)
    (hF : ∀ x, MeasurableSet {c | x ∈ F c}) :
    (centeredFiniteProbabilityMeasure μ law).real {z | z.2 ∈ F z.1} =
      ∫ c, (law c).mass (F c) ∂μ :=
  centeredFiniteProbabilityMeasure_real_finite_events μ law hweight F
    (centeredFinite_finite_event_measurable F hF)

omit μ [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem centeredFinite_mass_measurable (F : C → Finset Ω)
    (hF : ∀ x, MeasurableSet {c | x ∈ F c}) :
    Measurable (fun c => (law c).mass (F c)) := by
  have h := centeredFinite_mean_measurable law hweight
    (fun c x => if x ∈ F c then 1 else 0)
    (fun x => measurable_const.ite (hF x) measurable_const)
  simpa only [FiniteProbabilityWeights.mean_indicator] using h

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem centeredFinite_mass_integrable [IsFiniteMeasure μ] (F : C → Finset Ω)
    (hF : ∀ x, MeasurableSet {c | x ∈ F c}) :
    Integrable (fun c => (law c).mass (F c)) μ := by
  apply Integrable.of_bound (centeredFinite_mass_measurable law hweight F hF).aestronglyMeasurable 1
  exact ae_of_all μ (fun c => by
    rw [Real.norm_of_nonneg ((law c).mass_nonneg (F c))]
    exact (law c).mass_le_one (F c))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
variable (μ : Measure C) [IsProbabilityMeasure μ]
variable (law : C → FiniteProbabilityWeights Ω)
variable (hweight : ∀ x, Measurable (fun c => (law c).weight x))

noncomputable def integratedFiniteProbabilityWeights : FiniteProbabilityWeights Ω where
  weight x := ∫ c, (law c).weight x ∂μ
  nonneg x := integral_nonneg (fun c => (law c).nonneg x)
  total := by
    rw [← integral_finsetSum _ (fun x _ => centeredFinite_weight_integrable μ law hweight x)]
    simp only [(law _).total, integral_const, probReal_univ, smul_eq_mul, one_mul]

@[simp] theorem integratedFiniteProbabilityWeights_weight (x : Ω) :
    (integratedFiniteProbabilityWeights μ law hweight).weight x =
      ∫ c, (law c).weight x ∂μ := rfl

theorem integratedFiniteProbabilityWeights_mean (f : Ω → ℝ) :
    (integratedFiniteProbabilityWeights μ law hweight).mean f =
      ∫ c, (law c).mean f ∂μ := by
  rw [FiniteProbabilityWeights.mean]
  simp only [integratedFiniteProbabilityWeights_weight, ← integral_mul_const]
  exact (integral_finsetSum _ (fun x _ =>
    (centeredFinite_weight_integrable μ law hweight x).mul_const (f x))).symm

theorem integratedFiniteProbabilityWeights_mass (F : Finset Ω) :
    (integratedFiniteProbabilityWeights μ law hweight).mass F =
      ∫ c, (law c).mass F ∂μ := by
  unfold FiniteProbabilityWeights.mass
  simp only [integratedFiniteProbabilityWeights_weight]
  exact (integral_finsetSum _ (fun x _ =>
    centeredFinite_weight_integrable μ law hweight x)).symm

theorem integratedFiniteProbabilityWeights_mass_eq_joint
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (F : Finset Ω) :
    (integratedFiniteProbabilityWeights μ law hweight).mass F =
      (centeredFiniteProbabilityMeasure μ law).real {z | z.2 ∈ F} := by
  rw [integratedFiniteProbabilityWeights_mass,
    centeredFiniteProbabilityMeasure_real_finset_fiber μ law hweight F]

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical

theorem centeredFiniteProbabilityMeasure_productive_family
    {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure C) [IsProbabilityMeasure μ]
    (law : C → FiniteProbabilityWeights Ω)
    (hweight : ∀ z, Measurable (fun c => (law c).weight z))
    (productive : Finset Ω) (Qgood : C × Ω → Prop)
    (hgood : ∀ c z, 0 < (law c).weight z → Qgood (c,z))
    {τ : ℝ} (hmass : τ ≤ ∫ c, (law c).mass productive ∂μ) :
    IsProbabilityMeasure (centeredFiniteProbabilityMeasure μ law) ∧
      MeasurableSet {z : C × Ω | z.2 ∈ productive} ∧
      τ ≤ (centeredFiniteProbabilityMeasure μ law).real {z | z.2 ∈ productive} ∧
      ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law, Qgood z := by
  refine ⟨centeredFiniteProbabilityMeasure_probability μ law hweight,
    (Finset.measurableSet productive).preimage measurable_snd, ?_, ?_⟩
  · rw [centeredFiniteProbabilityMeasure_real_finset_fiber μ law hweight]
    exact hmass
  · filter_upwards [centeredFiniteProbabilityMeasure_ae_positive_weight μ law hweight] with z hz
    exact hgood z.1 z.2 hz

theorem centeredFiniteProbabilityMeasure_productive_injective
    {C Ω R Y : Type*} [MeasurableSpace C] [Fintype Ω] [Fintype R]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure C) [IsProbabilityMeasure μ]
    (law : C → FiniteProbabilityWeights Ω)
    (hweight : ∀ z, Measurable (fun c => (law c).weight z))
    (sites : FiniteProbabilityWeights R) (image : Ω → R → Y) (test : Y → ℝ)
    (Qgood : C × Ω → Prop) (hgood : ∀ c z, 0 < (law c).weight z → Qgood (c,z))
    {σ η parent : ℝ} (hσ : 0 < σ) (hη : η ≤ σ / 8) (hparent : σ ≤ parent)
    (htest : ∀ y, test y ≤ 1)
    (hmarginal : ∀ r,
      Integrable (fun c => (law c).complexMean (fun z => (test (image z r) : ℂ))) μ ∧
      ‖(∫ c, (law c).complexMean (fun z => (test (image z r) : ℂ)) ∂μ) -
        (parent : ℂ)‖ ≤ η)
    (hcollision : (∫ c, (law c).mean (fun z => noninjectivityIndicator (image z)) ∂μ) ≤ σ / 16) :
    let productive := Finset.univ.filter (fun z => Function.Injective (image z) ∧
      σ / 2 ≤ sites.mean (fun r => test (image z r)))
    IsProbabilityMeasure (centeredFiniteProbabilityMeasure μ law) ∧
      MeasurableSet {z : C × Ω | z.2 ∈ productive} ∧
      σ / 4 ≤ (centeredFiniteProbabilityMeasure μ law).real {z | z.2 ∈ productive} ∧
      ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law, Qgood z := by
  intro productive
  apply centeredFiniteProbabilityMeasure_productive_family μ law hweight productive Qgood hgood
  have hiBad := centeredFinite_mean_integrable μ law hweight
    (fun _ z => noninjectivityIndicator (image z)) (fun z => integrable_const _)
  have hiProd : Integrable (fun c => (law c).mass productive) μ :=
    centeredFinite_mass_integrable μ law hweight (fun _ => productive)
      (fun z => by by_cases hz : z ∈ productive <;> simp [hz])
  exact integral_productive_injective_mass_of_complex_marginals μ law sites image test
    hσ hη hparent htest (fun r => (hmarginal r).1) (fun r => (hmarginal r).2)
    hiBad hiProd hcollision

end Erdos3

end

end OAI
