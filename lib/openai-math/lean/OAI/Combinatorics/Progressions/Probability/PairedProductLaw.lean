import OAI.Combinatorics.Progressions.Probability.PairedProductDensity

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem uniform_two_term_sum_sort (a b : ℝ) (φ : ℝ → ℝ) (hφ : Measurable φ)
    {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    (∫ u, ∫ v, φ (min a b * u + max a b * v) ∂unitScalarMeasure ∂unitScalarMeasure) =
      ∫ u, ∫ v, φ (a * u + b * v) ∂unitScalarMeasure ∂unitScalarMeasure := by
  rcases le_total a b with hab | hab
  · simp only [min_eq_left hab, max_eq_right hab]
  · rw [min_eq_right hab, max_eq_left hab]
    have hi : Integrable (Function.uncurry (fun u v => φ (b * u + a * v)))
        (unitScalarMeasure.prod unitScalarMeasure) := by
      apply (integrable_const C).mono'
      · exact (hφ.comp ((measurable_const.mul measurable_fst).add
          (measurable_const.mul measurable_snd))).aestronglyMeasurable
      · exact Filter.Eventually.of_forall (fun p => hbound (b * p.1 + a * p.2))
    have h := integral_integral_swap hi
    conv_rhs at h => arg 2; ext u; arg 2; ext v; rw [add_comm]
    exact h

variable {ι : Type*} [Fintype ι]

theorem pairedProductDensity_test_integral (φ : ℝ → ℝ) (hφ : Measurable φ)
    {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    (∫ x, pairedProductDensity ι x * φ x) =
      ∫ p : (ι → ℝ) × (ι → ℝ), ∫ u, ∫ v,
        φ ((∏ i, p.1 i) * u + (∏ i, p.2 i) * v)
        ∂unitScalarMeasure ∂unitScalarMeasure ∂(unitBoxMeasure ι).prod (unitBoxMeasure ι) := by
  rw [pairedProductDensity_test_sorted φ hφ hbound]
  have hm : Measurable (fun p : (((ι → ℝ) × (ι → ℝ)) × ℝ) × ℝ =>
      φ (pairedProductShift p.1 + pairedProductWidth p.1 * p.2)) :=
    hφ.comp ((pairedProductShift_measurable.comp measurable_fst).add
      ((pairedProductWidth_measurable.comp measurable_fst).mul measurable_snd))
  have hi : Integrable (fun p : (((ι → ℝ) × (ι → ℝ)) × ℝ) × ℝ =>
      φ (pairedProductShift p.1 + pairedProductWidth p.1 * p.2))
      ((pairedProductParameterMeasure ι).prod unitScalarMeasure) :=
    (integrable_const C).mono' hm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hbound _))
  change (∫ p, ∫ v, φ (pairedProductShift p + pairedProductWidth p * v)
      ∂unitScalarMeasure ∂((unitBoxMeasure ι).prod (unitBoxMeasure ι)).prod unitScalarMeasure) = _
  rw [integral_prod _ hi.integral_prod_left]
  apply integral_congr_ae
  filter_upwards [] with p
  simp only [pairedProductShift, pairedProductWidth, pairedAmplitude]
  exact uniform_two_term_sum_sort (∏ i, p.1 i) (∏ i, p.2 i) φ hφ hbound

end Erdos3

end

end OAI
