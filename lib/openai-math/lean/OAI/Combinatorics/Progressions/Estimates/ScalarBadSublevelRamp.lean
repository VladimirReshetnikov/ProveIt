import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Lipschitz

namespace OAI

section

namespace Erdos3
open scoped NNReal

noncomputable def scalarBadSublevelRamp (κ t : ℝ) : ℝ :=
  max 0 (min 1 (2 - 2 * |t| / κ))

theorem scalarBadSublevelRamp_range (κ t : ℝ) :
    scalarBadSublevelRamp κ t ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem scalarBadSublevelRamp_eq_one {κ t : ℝ} (hκ : 0 < κ) (ht : |t| ≤ κ / 2) :
    scalarBadSublevelRamp κ t = 1 := by
  have hr : 2 * |t| / κ ≤ 1 := (div_le_one hκ).mpr (by linarith)
  rw [scalarBadSublevelRamp, min_eq_left (by linarith), max_eq_right zero_le_one]

theorem scalarBadSublevelRamp_eq_zero {κ t : ℝ} (hκ : 0 < κ) (ht : κ ≤ |t|) :
    scalarBadSublevelRamp κ t = 0 := by
  have hr : 2 ≤ 2 * |t| / κ := (le_div_iff₀ hκ).mpr (by linarith)
  rw [scalarBadSublevelRamp, min_eq_right (by linarith), max_eq_left (by linarith)]

theorem scalarBadSublevelRamp_lipschitz {κ : ℝ} (hκ : 0 < κ) :
    LipschitzWith ⟨2 / κ, by positivity⟩ (scalarBadSublevelRamp κ) := by
  have hraw : LipschitzWith ⟨2 / κ, by positivity⟩ (fun t : ℝ => 2 - 2 * |t| / κ) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, Real.dist_eq]
    have he : (2 - 2 * |x| / κ) - (2 - 2 * |y| / κ) = -(2 / κ) * (|x| - |y|) := by ring
    rw [he, abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 2 / κ)]
    exact mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub x y) (by positivity)
  exact (hraw.const_min 1).const_max 0

end Erdos3

end

end OAI
