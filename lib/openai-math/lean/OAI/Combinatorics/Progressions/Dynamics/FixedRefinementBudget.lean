import OAI.Combinatorics.Progressions.Estimates.RefinementEnlargement

namespace OAI

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped NNReal

noncomputable def refinementScaleLoss (rank : ℕ) (p : ℝ) : ℝ :=
  (rank : ℝ) + p / 8 + 3 * p + 1600

noncomputable def refinementMatchingLoss (rank : ℕ) (p epsilon : ℝ) : ℝ :=
  5 * rank + (25 / 2 : ℝ) * p + localMomentErrorBudget (flatComparisonDelta epsilon) +
    unbalancedErrorBudget (localMomentGain (flatComparisonDelta epsilon)) + 8020

noncomputable def refinementRoundLoss (rank : ℕ) (p H epsilon : ℝ) : ℝ :=
  refinementMatchingLoss rank p epsilon +
    unbalancedReturnWidthLoss rank (localMomentGain (flatComparisonDelta epsilon)) p H (p / 8) (2 * p)

noncomputable def refinementComparisonBudget (rank : ℕ) (p R epsilon : ℝ) : ℝ :=
  max (2 * rank + p + ((1 / 4 : ℝ) + 2) * p +
      (R + refinementMatchingLoss rank p epsilon) + 1612)
    (((1 / 4 : ℝ) + 2) * p + 2 +
      rank * (R + refinementMatchingLoss rank p epsilon + 10))

theorem refinementMatchingLoss_eq (rank : ℕ) (p epsilon : ℝ) :
    matchingWidthLoss rank p (outerMatchingScaleLoss rank (p / 8) (2 * p)
      (refinementScaleLoss rank p)) (flatComparisonDelta epsilon)
        (localMomentGain (flatComparisonDelta epsilon)) = refinementMatchingLoss rank p epsilon := by
  rw [matchingWidthLoss_outer]
  unfold refinementScaleLoss refinementMatchingLoss
  ring

theorem refinementRoundLoss_eq (rank : ℕ) (p H epsilon : ℝ) :
    refinementMatchingWidthLoss rank p H (p / 8) (2 * p) (2 * p)
      (refinementScaleLoss rank p) (flatComparisonDelta epsilon) =
        refinementRoundLoss rank p H epsilon := by
  unfold refinementMatchingWidthLoss refinementRoundLoss
  rw [refinementMatchingLoss_eq]

theorem refinementMatchingLoss_nonneg (rank : ℕ) {p epsilon : ℝ}
    (hp : 0 ≤ p) (hepsilon : 0 < epsilon) : 0 ≤ refinementMatchingLoss rank p epsilon := by
  have hdelta := (flatComparisonDelta_spec hepsilon).1
  have hc := localMomentGain_pos (flatComparisonDelta epsilon)
  have hc1 := (localMomentGain_le_half (flatComparisonDelta epsilon)).trans (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hEd := (localMomentErrorBudget_spec hdelta).1
  have hEc := (unbalancedErrorBudget_spec hc hc1).1
  unfold refinementMatchingLoss
  positivity

theorem two_le_refinementRoundLoss (rank : ℕ) {p H epsilon : ℝ}
    (hp : 0 ≤ p) (hH : 0 ≤ H) (hepsilon : 0 < epsilon) :
    2 ≤ refinementRoundLoss rank p H epsilon := by
  have hm := refinementMatchingLoss_nonneg rank hp hepsilon
  have hc := localMomentGain_pos (flatComparisonDelta epsilon)
  have hc1 := (localMomentGain_le_half (flatComparisonDelta epsilon)).trans (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hu := unbalancedWidthLoss_nonneg rank hc hc1 hp hH
  have hrank : (0 : ℝ) ≤ rank := Nat.cast_nonneg rank
  unfold refinementRoundLoss unbalancedReturnWidthLoss
  linarith

theorem refinementMatchingLoss_mono_rank {r d : ℕ} (hrd : r ≤ d) (p epsilon : ℝ) :
    refinementMatchingLoss r p epsilon ≤ refinementMatchingLoss d p epsilon := by
  have hrdR : (r : ℝ) ≤ d := by exact_mod_cast hrd
  unfold refinementMatchingLoss
  linarith

theorem refinementRoundLoss_mono_rank {r d : ℕ} (hrd : r ≤ d) (p H epsilon : ℝ) :
    refinementRoundLoss r p H epsilon ≤ refinementRoundLoss d p H epsilon := by
  have hrdR : (r : ℝ) ≤ d := by exact_mod_cast hrd
  have hm := refinementMatchingLoss_mono_rank hrd p epsilon
  have hc := localMomentGain_pos (flatComparisonDelta epsilon)
  have hK := CyclicCrootSisask.almostPeriodicityWidthConstant_pos (show 0 <
    localMomentGain (flatComparisonDelta epsilon) / 64 by positivity)
  have hlog : Real.log (2 + (r : ℝ)) ≤ Real.log (2 + (d : ℝ)) :=
    Real.log_le_log (by positivity) (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hlog hK.le
  unfold refinementRoundLoss unbalancedReturnWidthLoss unbalancedWidthLoss
  push_cast
  nlinarith

theorem fixed_refinement_scale_spec (rank : ℕ) {p W : ℝ} (hp : 0 ≤ p)
    (hW : 0 ≤ W) (hWcap : W ≤ Real.exp (p / 8)) :
    let scale := localizedAverageScale rank W (Real.exp (-(3 * p)))
    0 < scale ∧ scale ≤ 1 / (100 * (2 * max rank 1 : ℕ) : ℝ≥0) ∧
      W * (400 * (max rank 1 : ℕ) * (scale : ℝ)) ≤ Real.exp (-(3 * p)) ∧
      Real.exp (-refinementScaleLoss rank p) ≤ (scale : ℝ) := by
  intro scale
  obtain ⟨hs, hlim, herr⟩ := localizedAverageScale_spec rank hW (Real.exp_pos (-(3 * p)))
  refine ⟨hs, hlim, herr, ?_⟩
  exact localizedAverageScale_exp_lower_of_error rank hW hWcap (by positivity) (by positivity)
    (by nlinarith [Real.exp_pos (-(3 * p))])

end Erdos3.CellRefinement

end

end OAI
