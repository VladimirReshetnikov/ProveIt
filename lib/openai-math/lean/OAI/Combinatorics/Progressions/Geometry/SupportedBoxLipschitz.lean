import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Lipschitz

namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem lipschitzWith_of_unit_range_support_box {I : Type*} [Fintype I]
    (f : (I → ℝ) → ℝ) (R L : ℝ≥0)
    (hzero : ∀ x, 0 ≤ f x) (hone : ∀ x, f x ≤ 1)
    (hsupport : ∀ x, f x ≠ 0 → ∀ i, |x i| ≤ R)
    (hlip : LipschitzOnWith L f {x | ∀ i, |x i| ≤ (R : ℝ) + 1}) :
    LipschitzWith (max 1 L) f := by
  have hL : (L : ℝ) ≤ (max 1 L : ℝ≥0) := by exact_mod_cast (le_max_right 1 L)
  have hnear (x y : I → ℝ) (hx : f x ≠ 0) (hxy : dist x y < 1) :
      dist (f x) (f y) ≤ L * dist x y := by
    have hxR : ∀ i, |x i| ≤ (R : ℝ) + 1 := fun i => (hsupport x hx i).trans (by linarith)
    have hyR : ∀ i, |y i| ≤ (R : ℝ) + 1 := by
      intro i
      have hi : |y i - x i| ≤ dist x y := by
        calc
          |y i - x i| ≤ dist y x := by simpa only [Real.dist_eq] using dist_le_pi_dist y x i
          _ = dist x y := dist_comm y x
      calc
        |y i| = |(y i - x i) + x i| := by ring_nf
        _ ≤ |y i - x i| + |x i| := abs_add_le _ _
        _ ≤ (R : ℝ) + 1 := by linarith [hsupport x hx i]
    exact hlip.dist_le_mul x hxR y hyR
  apply LipschitzWith.of_dist_le_mul
  intro x y
  by_cases hxy : dist x y < 1
  · by_cases hx : f x = 0
    · by_cases hy : f y = 0
      · rw [hx, hy, dist_self]
        positivity
      · have h := hnear y x hy (by simpa only [dist_comm] using hxy)
        rw [dist_comm (f y) (f x), dist_comm y x] at h
        exact h.trans (mul_le_mul_of_nonneg_right hL dist_nonneg)
    · exact (hnear x y hx hxy).trans (mul_le_mul_of_nonneg_right hL dist_nonneg)
  · have hdist : dist (f x) (f y) ≤ 1 := by
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [hzero x, hzero y, hone x, hone y]
    have hlarge : (1 : ℝ) ≤ dist x y := le_of_not_gt hxy
    have hmax : (1 : ℝ) ≤ (max 1 L : ℝ≥0) := by exact_mod_cast (le_max_left 1 L)
    exact hdist.trans (hlarge.trans (by nlinarith [dist_nonneg (x := x) (y := y)]))

end Erdos3

end

end OAI
