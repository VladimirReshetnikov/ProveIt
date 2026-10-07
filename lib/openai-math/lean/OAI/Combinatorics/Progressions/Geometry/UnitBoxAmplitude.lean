import OAI.Combinatorics.Progressions.Estimates.InverseSqrtMoment

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

def positiveUnitBox (ι : Type*) := Set.univ.pi (fun _ : ι => Set.Ioc (0 : ℝ) 1)

theorem positiveUnitBox_measurable : MeasurableSet (positiveUnitBox ι) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)

noncomputable def unitBoxMeasure (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  volume.restrict (positiveUnitBox ι)

instance unitBoxMeasure_probability : IsProbabilityMeasure (unitBoxMeasure ι) := by
  constructor
  simp only [unitBoxMeasure, Measure.restrict_apply_univ, positiveUnitBox, Real.volume_pi_Ioc,
    sub_zero, ENNReal.ofReal_one, Finset.prod_const_one]

theorem unitBoxMeasure_ae : ∀ᵐ x ∂unitBoxMeasure ι, ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1 := by
  filter_upwards [ae_restrict_mem (μ := volume) (positiveUnitBox_measurable (ι := ι))] with x hx
  exact fun i => hx i (Set.mem_univ i)

theorem unitBoxInverseSqrt_indicator : unitBoxInverseSqrt (ι := ι) =
    (positiveUnitBox ι).indicator (fun x => (Real.sqrt (∏ i, x i))⁻¹) := by
  funext x
  by_cases hx : x ∈ positiveUnitBox ι
  · rw [Set.indicator_of_mem hx]
    exact unitBoxInverseSqrt_eq x (fun i => hx i (Set.mem_univ i))
  · rw [Set.indicator_of_notMem hx]
    have h : ¬ ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1 := by
      intro hall
      exact hx (fun i _ => hall i)
    push Not at h
    obtain ⟨i, hi⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact Set.indicator_of_notMem hi _

theorem unitBox_inverse_sqrt_integrable :
    Integrable (fun x : ι → ℝ => (Real.sqrt (∏ i, x i))⁻¹) (unitBoxMeasure ι) := by
  apply (integrable_indicator_iff positiveUnitBox_measurable).mp
  rw [← unitBoxInverseSqrt_indicator]
  exact unitBoxInverseSqrt_integrable

theorem unitBox_inverse_sqrt_mass :
    (∫ x : ι → ℝ, (Real.sqrt (∏ i, x i))⁻¹ ∂unitBoxMeasure ι) = 2 ^ Fintype.card ι := by
  rw [unitBoxMeasure, ← integral_indicator positiveUnitBox_measurable,
    ← unitBoxInverseSqrt_indicator]
  exact unitBoxInverseSqrt_mass

noncomputable def pairedAmplitude (p : (ι → ℝ) × (ι → ℝ)) : ℝ :=
  max (∏ i, p.1 i) (∏ i, p.2 i)

theorem pairedAmplitude_continuous : Continuous (pairedAmplitude (ι := ι)) := by
  unfold pairedAmplitude
  fun_prop

theorem pairedAmplitude_pos_ae :
    ∀ᵐ p ∂(unitBoxMeasure ι).prod (unitBoxMeasure ι), 0 < pairedAmplitude p := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (unitBoxMeasure_ae (ι := ι))] with p hp
  exact lt_max_of_lt_left (Finset.prod_pos (fun i _ => (hp i).1))

theorem pairedAmplitude_inverse_bound :
    ∀ᵐ p ∂(unitBoxMeasure ι).prod (unitBoxMeasure ι),
      (pairedAmplitude p)⁻¹ ≤ (Real.sqrt (∏ i, p.1 i))⁻¹ * (Real.sqrt (∏ i, p.2 i))⁻¹ := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (unitBoxMeasure_ae (ι := ι)),
    Measure.quasiMeasurePreserving_snd.ae (unitBoxMeasure_ae (ι := ι))] with p hp hq
  exact inverse_max_le_inverse_sqrt_product (Finset.prod_pos (fun i _ => (hp i).1))
    (Finset.prod_pos (fun i _ => (hq i).1))

theorem pairedAmplitude_inverse_integrable :
    Integrable (fun p : (ι → ℝ) × (ι → ℝ) => (pairedAmplitude p)⁻¹)
      ((unitBoxMeasure ι).prod (unitBoxMeasure ι)) := by
  have hi := (unitBox_inverse_sqrt_integrable (ι := ι)).mul_prod
    (unitBox_inverse_sqrt_integrable (ι := ι))
  apply hi.mono' pairedAmplitude_continuous.measurable.inv.aestronglyMeasurable
  filter_upwards [pairedAmplitude_inverse_bound (ι := ι), pairedAmplitude_pos_ae (ι := ι)] with p hp hpos
  change ‖(pairedAmplitude p)⁻¹‖ ≤ _
  rw [Real.norm_of_nonneg (inv_nonneg.mpr hpos.le)]
  exact hp

theorem pairedAmplitude_inverse_integral_le :
    (∫ p : (ι → ℝ) × (ι → ℝ), (pairedAmplitude p)⁻¹
      ∂(unitBoxMeasure ι).prod (unitBoxMeasure ι)) ≤ 4 ^ Fintype.card ι := by
  have hi := (unitBox_inverse_sqrt_integrable (ι := ι)).mul_prod
    (unitBox_inverse_sqrt_integrable (ι := ι))
  have h := integral_mono_ae (pairedAmplitude_inverse_integrable (ι := ι)) hi
    (pairedAmplitude_inverse_bound (ι := ι))
  rw [integral_prod_mul (fun x : ι → ℝ => (Real.sqrt (∏ i, x i))⁻¹)
    (fun x : ι → ℝ => (Real.sqrt (∏ i, x i))⁻¹), unitBox_inverse_sqrt_mass, ← mul_pow] at h
  norm_num only [show (2 : ℝ) * 2 = 4 by norm_num] at h
  exact h

end Erdos3

end

end OAI
