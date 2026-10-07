import OAI.Combinatorics.Progressions.Geometry.ScalarSupportTranslationL1

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem affineProductProfile_translation_l1 {I : Type*} [Fintype I]
    (c w : I → ℝ) {δ : ℝ} (hδ : 0 < δ) (hw : ∀ i, δ ≤ w i) (a b : I → ℝ) :
    (∫ x, |affineProductProfile c w (x + a) - affineProductProfile c w (x + b)|) ≤
      (Fintype.card I * (4 * (probabilityProfileLipschitz : ℝ) / δ)) * dist a b := by
  classical
  have hwp (i) : 0 < w i := hδ.trans_le (hw i)
  have hi (z : I → ℝ) (i) : Integrable (fun x => affineProbabilityProfile (c i) (w i) (x + z i)) :=
    (affineProbabilityProfile_integrable (c i) (hwp i)).comp_add_right (z i)
  have hm (z : I → ℝ) (i) : (∫ x, affineProbabilityProfile (c i) (w i) (x + z i)) = 1 := by
    rw [integral_add_right_eq_self, affineProbabilityProfile_integral (c i) (hwp i)]
  have h := product_density_l1_le_sum
    (fun i x => affineProbabilityProfile (c i) (w i) (x + a i))
    (fun i x => affineProbabilityProfile (c i) (w i) (x + b i))
    (hi a) (hi b) (fun i _ => affineProbabilityProfile_nonneg (c i) (hwp i) _)
    (fun i _ => affineProbabilityProfile_nonneg (c i) (hwp i) _) (hm a) (hm b)
  change (∫ x, |affineProductProfile c w (x + a) - affineProductProfile c w (x + b)|) ≤ _ at h
  refine h.trans ?_
  calc
    _ ≤ ∑ _i : I, (4 * (probabilityProfileLipschitz : ℝ) / δ) * dist a b := by
      apply Finset.sum_le_sum
      intro i _
      apply (affineProbabilityProfile_translation_l1 (c i) (a i) (b i) (hwp i)).trans
      apply mul_le_mul
      · exact div_le_div_of_nonneg_left (by positivity) hδ (hw i)
      · simpa only [Real.dist_eq] using dist_le_pi_dist a b i
      · exact abs_nonneg _
      · positivity
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Erdos3

end

end OAI
