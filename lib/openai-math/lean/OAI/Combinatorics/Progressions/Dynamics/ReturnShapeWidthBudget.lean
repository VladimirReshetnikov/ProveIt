import OAI.Combinatorics.Progressions.Estimates.RefinementMatchingGeometry

namespace OAI

section

namespace Erdos3.LocalConvolution

open CyclicCrootSisask

theorem two_le_unbalancedWidthLoss (rank : ℕ) {c p H : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hp : 0 ≤ p) (hH : 0 ≤ H) :
    2 ≤ unbalancedWidthLoss rank c p H := by
  have hE := (unbalancedErrorBudget_spec hc hc1).1
  have hK := (almostPeriodicityWidthConstant_pos (show 0 < c / 64 by positivity)).le
  have hlog : 0 ≤ Real.log (2 + (rank : ℝ)) :=
    Real.log_nonneg (by have hrank : (0 : ℝ) ≤ rank := Nat.cast_nonneg rank; linarith)
  have hrest : 0 ≤ (rank : ℝ) + 2 * H * p ^ 2 + unbalancedErrorBudget c +
      (((rank + unbalancedRankExtra c p H : ℕ) : ℝ) + 2 * p + unbalancedErrorBudget c) +
      almostPeriodicityWidthConstant (c / 64) *
        (1 + (3 * H + 1) * p ^ 2 + Real.log (2 + rank)) := by positivity
  unfold unbalancedWidthLoss
  linarith

theorem unbalanced_return_width_le_regular_return {N : ℕ} [NeZero N]
    (S : CyclicBohr.Set N) {c p H W Q E : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hp : 0 ≤ p) (hH : 0 ≤ H)
    (hW : 0 ≤ W) (hWcap : W ≤ Real.exp Q) (hQ : 0 ≤ Q) (hE : 0 ≤ E) :
    S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank c p H Q E) ≤
      (CellRefinement.independentReturnScale S.rank W (Real.exp (-E)) : ℝ) * S.radius / 2 := by
  have hscale := CellRefinement.independentReturnScale_exp_lower S.rank hW hWcap hQ hE
  have htwo : Real.exp (-2 : ℝ) ≤ 1 / 2 := by
    have h : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
    simpa only [Real.exp_neg, one_div] using one_div_le_one_div_of_le (by norm_num) h
  have hloss : Real.exp (-unbalancedWidthLoss S.rank c p H) ≤ 1 / 2 :=
    (Real.exp_le_exp.mpr (neg_le_neg (two_le_unbalancedWidthLoss S.rank hc hc1 hp hH))).trans htwo
  have hS := S.radius_nonneg
  calc
    _ = Real.exp (-((S.rank : ℝ) + Q + E + 1602)) * S.radius *
        Real.exp (-unbalancedWidthLoss S.rank c p H) := by
      unfold unbalancedReturnWidthLoss
      rw [neg_add, Real.exp_add]
      ring
    _ ≤ (CellRefinement.independentReturnScale S.rank W (Real.exp (-E)) : ℝ) * S.radius * (1 / 2) := by
      gcongr
    _ = _ := by ring

end Erdos3.LocalConvolution

end

end OAI
