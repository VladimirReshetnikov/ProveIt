import OAI.Combinatorics.Progressions.Probability.DensityMixtureAELaw

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem count_integrable_of_zero_off_finset {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] (s : Finset X) (f : X → ℝ)
    (hs : ∀ x ∉ s, f x = 0) : Integrable f Measure.count := by
  apply integrable_count_iff.mpr
  exact (hasSum_sum_of_ne_finset_zero (fun x hx => by rw [hs x hx, norm_zero])).summable

theorem count_integral_eq_sum_of_zero_off_finset {X : Type*} [Countable X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (s : Finset X) (f : X → ℝ) (hs : ∀ x ∉ s, f x = 0) :
    (∫ x, f x ∂Measure.count) = ∑ x ∈ s, f x := by
  rw [integral_countable (count_integrable_of_zero_off_finset s f hs)]
  simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
  exact (hasSum_sum_of_ne_finset_zero hs).tsum_eq

theorem count_density_l1_le_card {X : Type*} [Countable X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (s : Finset X) (f g : X → ℝ) (hf : ∀ x ∉ s, f x = 0) (hg : ∀ x ∉ s, g x = 0)
    {ε : ℝ} (he : ∀ x ∈ s, |f x - g x| ≤ ε) :
    (∫ x, |f x - g x| ∂Measure.count) ≤ (s.card : ℝ) * ε := by
  rw [count_integral_eq_sum_of_zero_off_finset s _ (fun x hx => by
    rw [hf x hx, hg x hx, sub_self, abs_zero])]
  exact (Finset.sum_le_sum he).trans_eq (by simp)

theorem rectangular_count_density_l1 {J : Type*} [Fintype J]
    (a S : J → ℝ) (hS : ∀ j, 1 ≤ S j) {R E : ℝ} (hR : 0 ≤ R) (hE : 0 ≤ E)
    (f q : (J → ℤ) → ℝ)
    (hf : ∀ v ∉ rectangularWeightIndices a S R, f v = 0)
    (hq : ∀ v ∉ rectangularWeightIndices a S R, q v = 0)
    (he : ∀ v, |(∏ j, S j) * f v - q v| ≤ E) :
    (∫ v, |f v - q v / (∏ j, S j)| ∂Measure.count) ≤ (2 * R + 1) ^ Fintype.card J * E := by
  have hprod : 0 < ∏ j, S j := Finset.prod_pos (fun j _ => zero_lt_one.trans_le (hS j))
  have hp (v) : |f v - q v / (∏ j, S j)| ≤ E / (∏ j, S j) := by
    have heq : f v - q v / (∏ j, S j) = ((∏ j, S j) * f v - q v) / (∏ j, S j) := by
      field_simp [hprod.ne']
    rw [heq, abs_div, abs_of_pos hprod]
    exact div_le_div_of_nonneg_right (he v) hprod.le
  refine (count_density_l1_le_card (rectangularWeightIndices a S R) f
    (fun v => q v / (∏ j, S j)) hf (fun v hv => by rw [hq v hv, zero_div])
    (fun v _ => hp v)).trans ?_
  calc
    _ ≤ ((2 * R + 1) ^ Fintype.card J * ∏ j, S j) * (E / ∏ j, S j) :=
      mul_le_mul_of_nonneg_right (rectangularWeightIndices_card_le a S hS hR)
        (div_nonneg hE hprod.le)
    _ = _ := by field_simp [hprod.ne']

end Erdos3

end

end OAI
