import OAI.Combinatorics.Progressions.Estimates.SlicedPairAmplitude
import OAI.Combinatorics.Progressions.Lattices.RandomAffinePair

namespace OAI

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory

variable {ι : Type*} [Fintype ι]

noncomputable def pairDensity (A B : SlicedProductBlock ι) : ℝ → ℝ :=
  affinePairDensity ((unitBoxMeasure ι).prod (unitBoxMeasure ι))
    (fun p => A.slope p.1) (fun p => B.slope p.2) (fun p => A.base p.1 + B.base p.2)

theorem pairDensity_measurable (A B : SlicedProductBlock ι) : Measurable (pairDensity A B) :=
  affinePairDensity_measurable _ (A.slope_continuous.measurable.comp measurable_fst)
    (B.slope_continuous.measurable.comp measurable_snd)
    ((A.base_continuous.measurable.comp measurable_fst).add
      (B.base_continuous.measurable.comp measurable_snd))

theorem pairDensity_cap {A B : SlicedProductBlock ι} (hA : A.Admissible) (hB : B.Admissible)
    (x : ℝ) : pairDensity A B x ∈ Set.Icc (0 : ℝ) (pairCap A B) := by
  have h := affinePairDensity_cap ((unitBoxMeasure ι).prod (unitBoxMeasure ι))
    (A.slope_continuous.measurable.comp measurable_fst)
    (B.slope_continuous.measurable.comp measurable_snd)
    ((A.base_continuous.measurable.comp measurable_fst).add
      (B.base_continuous.measurable.comp measurable_snd))
    (pairWidth_pos hA hB) (pairWidth_inverse_integrable hA hB) x
  exact ⟨h.1, h.2.trans (pairWidth_inverse_integral_le hA hB)⟩

theorem pairDensity_probability_density {A B : SlicedProductBlock ι}
    (hA : A.Admissible) (hB : B.Admissible) :
    (∀ x, 0 ≤ pairDensity A B x) ∧ Integrable (pairDensity A B) ∧
      (∫ x, pairDensity A B x) = 1 :=
  affinePairDensity_probability_density ((unitBoxMeasure ι).prod (unitBoxMeasure ι))
    (A.slope_continuous.measurable.comp measurable_fst)
    (B.slope_continuous.measurable.comp measurable_snd)
    ((A.base_continuous.measurable.comp measurable_fst).add
      (B.base_continuous.measurable.comp measurable_snd)) (pairWidth_pos hA hB)

theorem pairDensity_translation_l1 {A B : SlicedProductBlock ι}
    (hA : A.Admissible) (hB : B.Admissible) (x y : ℝ) :
    (∫ u, |pairDensity A B (u + x) - pairDensity A B (u + y)|) ≤
      2 * pairCap A B * |x - y| := by
  have h := affinePairDensity_translation_l1 ((unitBoxMeasure ι).prod (unitBoxMeasure ι))
    (A.slope_continuous.measurable.comp measurable_fst)
    (B.slope_continuous.measurable.comp measurable_snd)
    ((A.base_continuous.measurable.comp measurable_fst).add
      (B.base_continuous.measurable.comp measurable_snd))
    (pairWidth_pos hA hB) (pairWidth_inverse_integrable hA hB) x y
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pairWidth_inverse_integral_le hA hB) (by norm_num)) (abs_nonneg _))

theorem pairDensity_test_integral {A B : SlicedProductBlock ι}
    (hA : A.Admissible) (hB : B.Admissible) (φ : ℝ → ℝ) (hφ : Measurable φ)
    {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    (∫ x, pairDensity A B x * φ x) =
      ∫ p : (ι → ℝ) × (ι → ℝ), ∫ u, ∫ v, φ (A.value p.1 u + B.value p.2 v)
        ∂unitScalarMeasure ∂unitScalarMeasure ∂(unitBoxMeasure ι).prod (unitBoxMeasure ι) := by
  have h := affinePairDensity_test_integral ((unitBoxMeasure ι).prod (unitBoxMeasure ι))
    (A.slope_continuous.measurable.comp measurable_fst)
    (B.slope_continuous.measurable.comp measurable_snd)
    ((A.base_continuous.measurable.comp measurable_fst).add
      (B.base_continuous.measurable.comp measurable_snd)) (pairWidth_pos hA hB) φ hφ hbound
  apply h.trans
  apply integral_congr_ae
  filter_upwards [] with p
  apply integral_congr_ae
  filter_upwards [] with u
  apply integral_congr_ae
  filter_upwards [] with v
  rw [value_eq, value_eq]
  congr 1
  simp only [Function.comp_def, Pi.add_apply]
  ring

end Erdos3.SlicedProductBlock

end

end OAI
