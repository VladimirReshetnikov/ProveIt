import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Lipschitz

namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem lipschitzWith_of_unit_range_near_nonzero {X : Type*} [PseudoMetricSpace X]
    (f : X → ℝ) (C L : ℝ≥0) (hzero : ∀ x, 0 ≤ f x) (hone : ∀ x, f x ≤ 1)
    (hnear : ∀ x y, f x ≠ 0 → (C : ℝ) * dist x y < 1 →
      |f x - f y| ≤ (L : ℝ) * dist x y) :
    LipschitzWith (max C L) f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  by_cases hclose : (C : ℝ) * dist x y < 1
  · have hxy : |f x - f y| ≤ (L : ℝ) * dist x y := by
      by_cases hx : f x = 0
      · by_cases hy : f y = 0
        · rw [hx, hy, sub_self, abs_zero]
          positivity
        · have h := hnear y x hy (by simpa only [dist_comm] using hclose)
          simpa only [abs_sub_comm, dist_comm] using h
      · exact hnear x y hx hclose
    exact hxy.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_right C L) dist_nonneg)
  · have hxy : |f x - f y| ≤ 1 := abs_le.mpr ⟨by linarith [hzero x, hone y], by linarith [hone x, hzero y]⟩
    exact hxy.trans ((le_of_not_gt hclose).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left C L) dist_nonneg))

end Erdos3

end

end OAI
