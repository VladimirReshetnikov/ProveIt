import OAI.Combinatorics.Progressions.Probability.DensityMixtureAELaw
import OAI.Combinatorics.Progressions.Probability.PairedProductLaw

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem normalizedIntervalWindow_add_arg (ℓ s x a : ℝ) :
    normalizedIntervalWindow ℓ s (x + a) = normalizedIntervalWindow ℓ (s - a) x := by
  calc
    normalizedIntervalWindow ℓ s (x + a) = normalizedIntervalWindow ℓ 0 (x + a - s) :=
      normalizedIntervalWindow_translate _ _ _
    _ = normalizedIntervalWindow ℓ 0 (x - (s - a)) := by congr 1; ring
    _ = normalizedIntervalWindow ℓ (s - a) x := (normalizedIntervalWindow_translate _ _ _).symm

theorem randomIntervalDensity_add_arg {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (ℓ s : T → ℝ) (x a : ℝ) :
    randomIntervalDensity μ ℓ s (x + a) =
      randomIntervalDensity μ ℓ (fun t => s t - a) x := by
  apply integral_congr_ae
  filter_upwards [] with t
  exact normalizedIntervalWindow_add_arg _ _ _ _

theorem randomIntervalDensity_translation_l1 {T : Type*} [MeasurableSpace T]
    (μ : Measure T) [IsProbabilityMeasure μ] (ℓ s : T → ℝ)
    (hℓ : Measurable ℓ) (hs : Measurable s) (hpos : ∀ᵐ t ∂μ, 0 < ℓ t)
    (hi : Integrable (fun t => (ℓ t)⁻¹) μ) (a b : ℝ) :
    (∫ x, |randomIntervalDensity μ ℓ s (x + a) - randomIntervalDensity μ ℓ s (x + b)|) ≤
      2 * (∫ t, (ℓ t)⁻¹ ∂μ) * |a - b| := by
  have hj (c : ℝ) : Integrable (Function.uncurry
      (fun t x => normalizedIntervalWindow (ℓ t) (s t - c) x)) (μ.prod volume) := by
    apply densityMixture_joint_integrable μ volume _
    · exact measurable_normalizedIntervalWindow _ _ _ (hℓ.comp measurable_fst)
        ((hs.sub_const c).comp measurable_fst) measurable_snd
    · filter_upwards [hpos] with t ht
      exact ⟨normalizedIntervalWindow_nonneg ht _, normalizedIntervalWindow_integrable _ _,
        normalizedIntervalWindow_mass ht _⟩
  have hd : Integrable (Function.uncurry (fun t x =>
      normalizedIntervalWindow (ℓ t) (s t - a) x -
      normalizedIntervalWindow (ℓ t) (s t - b) x)) (μ.prod volume) := (hj a).sub (hj b)
  have h := densityMixture_l1_le μ volume _ _ (hj a) (hj b)
  simp only [Real.norm_eq_abs] at h
  simp_rw [randomIntervalDensity_add_arg]
  apply h.trans
  have hb : ∀ᵐ t ∂μ, (∫ x, |normalizedIntervalWindow (ℓ t) (s t - a) x -
      normalizedIntervalWindow (ℓ t) (s t - b) x|) ≤ 2 * (ℓ t)⁻¹ * |a - b| := by
    filter_upwards [hpos] with t ht
    have hbound := normalizedIntervalWindow_translation_le ht (s t - a) (s t - b)
    rwa [show s t - a - (s t - b) = -(a - b) by ring, abs_neg, div_eq_mul_inv] at hbound
  have hmono := integral_mono_ae hd.integral_norm_prod_left
    ((hi.const_mul 2).mul_const |a - b|) (by
      filter_upwards [hb] with t ht
      exact ht)
  rw [integral_mul_const, integral_const_mul] at hmono
  exact hmono

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {ι : Type*} [Fintype ι]

theorem pairedProductDensity_translation_l1 (a b : ℝ) :
    (∫ x, |pairedProductDensity ι (x + a) - pairedProductDensity ι (x + b)|) ≤
      (2 * 4 ^ Fintype.card ι) * |a - b| := by
  have h := randomIntervalDensity_translation_l1 (pairedProductParameterMeasure ι)
    pairedProductWidth pairedProductShift pairedProductWidth_measurable
    pairedProductShift_measurable pairedProductWidth_pos pairedProductWidth_inverse_integrable a b
  apply h.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left pairedProductWidth_inverse_integral_le (by norm_num)) (abs_nonneg _)

noncomputable def fourProductSumDensity (ι : Type*) [Fintype ι] : ℝ → ℝ :=
  scalarDensityConvolution (pairedProductDensity ι) (pairedProductDensity ι)

theorem fourProductSumDensity_cap (x : ℝ) :
    fourProductSumDensity ι x ∈ Set.Icc (0 : ℝ) (4 ^ Fintype.card ι) :=
  scalarDensityConvolution_cap _ _ pairedProductDensity_probability_density.2.1
    pairedProductDensity_probability_density.1 pairedProductDensity_probability_density.2.2
    pairedProductDensity_measurable pairedProductDensity_cap x

theorem fourProductSumDensity_lipschitz :
    LipschitzWith ((4 : ℝ≥0) ^ Fintype.card ι * (2 * (4 : ℝ≥0) ^ Fintype.card ι))
      (fourProductSumDensity ι) := by
  apply scalarDensityConvolution_lipschitz _ _ _ _ pairedProductDensity_probability_density.2.1
    pairedProductDensity_measurable
  · intro t
    rw [Real.norm_of_nonneg (pairedProductDensity_cap (ι := ι) t).1]
    exact (pairedProductDensity_cap (ι := ι) t).2
  · intro a b
    exact pairedProductDensity_translation_l1 a b

theorem fourProductSumDensity_probability_density :
    (∀ x, 0 ≤ fourProductSumDensity ι x) ∧ Integrable (fourProductSumDensity ι) ∧
      (∫ x, fourProductSumDensity ι x) = 1 := by
  have h := pairedProductDensity_probability_density (ι := ι)
  refine ⟨fun x => (fourProductSumDensity_cap x).1,
    scalarDensityConvolution_integrable _ _ pairedProductDensity_measurable
      pairedProductDensity_measurable h.2.1 h.2.1, ?_⟩
  unfold fourProductSumDensity
  rw [scalarDensityConvolution_mass _ _ pairedProductDensity_measurable
    pairedProductDensity_measurable h.2.1 h.2.1, h.2.2, one_mul]

theorem fourProductSumDensity_test_integral (φ : ℝ → ℝ) (hφ : Measurable φ)
    {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    (∫ x, fourProductSumDensity ι x * φ x) =
      ∫ t, pairedProductDensity ι t * ∫ u, pairedProductDensity ι u * φ (u + t) :=
  scalarDensityConvolution_test_integral _ _ φ pairedProductDensity_measurable
    pairedProductDensity_measurable pairedProductDensity_probability_density.2.1
    pairedProductDensity_probability_density.2.1 hφ hbound

end Erdos3

end

end OAI
