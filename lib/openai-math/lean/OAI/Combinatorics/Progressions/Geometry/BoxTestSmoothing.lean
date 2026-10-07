import OAI.Combinatorics.Progressions.Lattices.AffineBoxTest

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

noncomputable def boxTestAverage (δ : ℝ) (φ : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ :=
  kernelAverage volume (boxProbabilityWindow (fun _ => δ)) φ

theorem boxTestAverage_translate (δ : ℝ) (φ : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    boxTestAverage δ φ x = ∫ u, boxProbabilityWindow (fun _ => δ) 0 u * φ (x + u) := by
  rw [boxTestAverage, boxAverage_eq_translate]
  simp only [add_comm]

noncomputable def boxTestLipschitz (δ : ℝ) (hδ : 0 < δ) : ℝ≥0 :=
  boxWindowTranslationBound (fun _ : ι => δ) (fun _ => hδ)

theorem boxTestLipschitz_coe (δ : ℝ) (hδ : 0 < δ) :
    (boxTestLipschitz (ι := ι) δ hδ : ℝ) = 2 * Fintype.card ι / δ := by
  change (∑ _ : ι, 2 / δ) = _
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

theorem boxTestAverage_lipschitz [DecidableEq ι] (δ : ℝ) (hδ : 0 < δ)
    (φ : (ι → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    LipschitzWith (boxTestLipschitz (ι := ι) δ hδ) (boxTestAverage δ φ) := by
  have h := boxAverage_lipschitz (fun _ : ι => δ) (fun _ => hδ) φ 1
    hφ.aestronglyMeasurable hbound
  simp only [one_mul] at h
  exact h

theorem boxTestAverage_norm_le (δ : ℝ) (hδ : 0 < δ) (φ : (ι → ℝ) → ℝ)
    (hbound : ∀ x, ‖φ x‖ ≤ 1) (x : ι → ℝ) : ‖boxTestAverage δ φ x‖ ≤ 1 := by
  have hp (t : ι → ℝ) : ‖boxProbabilityWindow (fun _ => δ) x t * φ t‖ ≤
      boxProbabilityWindow (fun _ => δ) x t := by
    rw [norm_mul, Real.norm_of_nonneg (boxProbabilityWindow_nonneg _ (fun _ => hδ) _ _)]
    exact (mul_le_mul_of_nonneg_left (hbound t)
      (boxProbabilityWindow_nonneg _ (fun _ => hδ) _ _)).trans_eq (mul_one _)
  have h := norm_integral_le_of_norm_le (boxProbabilityWindow_integrable (fun _ => δ) x)
    (Filter.Eventually.of_forall hp)
  exact h.trans_eq (boxProbabilityWindow_mass _ (fun _ => hδ) x)

theorem boxProbabilityWindow_support_dist (δ : ℝ) (hδ : 0 < δ) (u : ι → ℝ)
    (hu : boxProbabilityWindow (fun _ => δ) 0 u ≠ 0) : dist u 0 ≤ δ := by
  apply (dist_pi_le_iff hδ.le).mpr
  intro i
  have hi : normalizedIntervalWindow δ 0 (u i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hu i (Finset.mem_univ i)
  have hui : u i ∈ Set.Ioc (0 : ℝ) δ := by
    by_contra hnot
    apply hi
    simp only [normalizedIntervalWindow, intervalWindow, zero_add, Set.indicator_of_notMem hnot, zero_div]
  simpa only [Pi.zero_apply, Real.dist_eq, sub_zero, abs_of_pos hui.1] using hui.2

end Erdos3

end

end OAI
