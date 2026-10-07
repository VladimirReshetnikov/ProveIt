import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Lipschitz

namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem norm_normalize_sub_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {rho : ℝ} (hrho : 0 < rho) (x y : V) (hx : rho ≤ ‖x‖) (hy : rho ≤ ‖y‖) :
    ‖NormedSpace.normalize x - NormedSpace.normalize y‖ ≤ (2 / rho) * ‖x - y‖ := by
  have hy0 : y ≠ 0 := norm_pos_iff.mp (hrho.trans_le hy)
  have hid : ‖x‖ • (NormedSpace.normalize x - NormedSpace.normalize y) =
      (x - y) + (‖y‖ - ‖x‖) • NormedSpace.normalize y := by
    simp only [smul_sub, sub_smul, NormedSpace.norm_smul_normalize]
    abel
  have hscale : ‖x‖ * ‖NormedSpace.normalize x - NormedSpace.normalize y‖ ≤ 2 * ‖x - y‖ := by
    calc
      _ = ‖‖x‖ • (NormedSpace.normalize x - NormedSpace.normalize y)‖ := by
        rw [norm_smul, Real.norm_of_nonneg (norm_nonneg x)]
      _ = ‖(x - y) + (‖y‖ - ‖x‖) • NormedSpace.normalize y‖ := congrArg norm hid
      _ ≤ ‖x - y‖ + ‖(‖y‖ - ‖x‖) • NormedSpace.normalize y‖ := norm_add_le _ _
      _ = ‖x - y‖ + |‖y‖ - ‖x‖| := by
        rw [norm_smul, NormedSpace.norm_normalize hy0, mul_one, Real.norm_eq_abs]
      _ ≤ 2 * ‖x - y‖ := by
        have h := abs_norm_sub_norm_le x y
        rw [abs_sub_comm] at h
        linarith
  have hsmall := (mul_le_mul_of_nonneg_right hx
    (norm_nonneg (NormedSpace.normalize x - NormedSpace.normalize y))).trans hscale
  calc
    _ ≤ (2 * ‖x - y‖) / rho := (le_div_iff₀ hrho).mpr (by nlinarith [hsmall])
    _ = _ := by ring

theorem lipschitzWith_normalize {X V : Type*} [PseudoMetricSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (u : X → V) {rho K : ℝ≥0}
    (hrho : 0 < rho) (hLip : LipschitzWith K u) (hlower : ∀ x, (rho : ℝ) ≤ ‖u x‖) :
    LipschitzWith (2 / rho * K) (fun x => NormedSpace.normalize (u x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  calc
    _ ≤ (2 / (rho : ℝ)) * ‖u x - u y‖ := norm_normalize_sub_le hrho _ _ (hlower x) (hlower y)
    _ ≤ (2 / (rho : ℝ)) * ((K : ℝ) * dist x y) :=
      mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using hLip.dist_le_mul x y) (by positivity)
    _ = ((2 / rho * K : ℝ≥0) : ℝ) * dist x y := by push_cast; ring

end Erdos3

end

end OAI
