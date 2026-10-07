import OAI.Combinatorics.Progressions.Dynamics.UnbalancedWidthBudget

namespace OAI

section

namespace Erdos3.LocalConvolution

open CyclicCrootSisask

theorem unbalancedRankExtra_le {c p H : ℝ} (hc : 0 < c) :
    (unbalancedRankExtra c p H : ℝ) ≤
      almostPeriodicityWidthConstant (c / 64) * (1 + (3 * H + 1) * p ^ 2) ^ 4 + 1 := by
  have hK := (almostPeriodicityWidthConstant_pos (show 0 < c / 64 by positivity)).le
  unfold unbalancedRankExtra
  exact (Nat.ceil_lt_add_one (by positivity)).le

theorem unbalancedWidthLoss_nonneg (rank : ℕ) {c p H : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hp : 0 ≤ p) (hH : 0 ≤ H) :
    0 ≤ unbalancedWidthLoss rank c p H := by
  have hK := (almostPeriodicityWidthConstant_pos (show 0 < c / 64 by positivity)).le
  have hE := (unbalancedErrorBudget_spec hc hc1).1
  have hlog : 0 ≤ Real.log (2 + (rank : ℝ)) :=
    Real.log_nonneg (by have hr : (0 : ℝ) ≤ (rank : ℝ) := Nat.cast_nonneg rank; linarith)
  unfold unbalancedWidthLoss
  positivity

theorem unbalancedWidthLoss_le_polynomial (rank : ℕ) {c p H : ℝ} (hc : 0 < c) :
    unbalancedWidthLoss rank c p H ≤
      2 * (rank : ℝ) +
        almostPeriodicityWidthConstant (c / 64) * (1 + (3 * H + 1) * p ^ 2) ^ 4 +
        2 * H * p ^ 2 + 2 * p + 2 * unbalancedErrorBudget c + 3209 +
        almostPeriodicityWidthConstant (c / 64) * (3 + (3 * H + 1) * p ^ 2 + rank) := by
  have hK := (almostPeriodicityWidthConstant_pos (show 0 < c / 64 by positivity)).le
  have hR := unbalancedRankExtra_le (p := p) (H := H) hc
  have hlog : Real.log (2 + (rank : ℝ)) ≤ (rank : ℝ) + 2 := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 + (rank : ℝ))
    linarith
  have hmul := mul_le_mul_of_nonneg_left hlog hK
  unfold unbalancedWidthLoss
  push_cast
  nlinarith

end Erdos3.LocalConvolution

end

end OAI
