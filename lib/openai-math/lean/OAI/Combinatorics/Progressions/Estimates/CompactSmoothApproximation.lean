import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor

namespace OAI

section

namespace Erdos3

open scoped ContDiff
open MeasureTheory

theorem exists_compact_smooth_uniform_approx {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (f : E → ℝ)
    (hf : Continuous f) (hs : HasCompactSupport f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ ∀ x, ‖g x - f x‖ ≤ ε := by
  obtain ⟨u, hu, huf⟩ := (hs.uniformContinuous_of_continuous hf).exists_contDiff_dist_le hε
  obtain ⟨R, hR, hbound⟩ := hs.isCompact.isBounded.exists_pos_norm_le
  let χ : ContDiffBump (0 : E) := ⟨R, R + 1, hR, by linarith⟩
  have hfix (x : E) : χ x * f x = f x := by
    by_cases hx : f x = 0
    · simp only [hx, mul_zero]
    · have hχ : χ x = 1 := χ.one_of_mem_closedBall (by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hbound x (subset_tsupport f hx))
      rw [hχ, one_mul]
  refine ⟨fun x => χ x * u x, χ.contDiff.mul hu, χ.hasCompactSupport.mul_right, ?_⟩
  intro x
  calc
    ‖χ x * u x - f x‖ = ‖χ x * (u x - f x)‖ := by rw [mul_sub, hfix]
    _ = χ x * ‖u x - f x‖ := by rw [norm_mul, Real.norm_of_nonneg χ.nonneg]
    _ ≤ χ x * ε := mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using (huf x).le) χ.nonneg
    _ ≤ ε := mul_le_of_le_one_left hε.le χ.le_one

end Erdos3

end

end OAI
