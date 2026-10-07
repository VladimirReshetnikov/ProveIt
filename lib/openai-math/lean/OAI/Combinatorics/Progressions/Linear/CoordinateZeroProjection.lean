import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Group.Constructions

namespace OAI

section

namespace Erdos3

open scoped ContDiff

variable {D : Type*} [Fintype D] (P : D → Prop) [DecidablePred P]

def coordinateZeroProjection (v : D → ℝ) : D → ℝ := fun d => if P d then 0 else v d

theorem coordinateZeroProjection_lipschitz : LipschitzWith 1 (coordinateZeroProjection P) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro d
  by_cases h : P d
  · simp only [coordinateZeroProjection, h, ite_true, dist_self]
    exact dist_nonneg
  · simpa only [coordinateZeroProjection, h, ite_false] using dist_le_pi_dist v w d

theorem coordinateZeroProjection_contDiff : ContDiff ℝ ∞ (coordinateZeroProjection P) := by
  apply contDiff_pi.mpr
  intro d
  by_cases h : P d
  · simpa only [coordinateZeroProjection, h, ite_true] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : D → ℝ => (0 : ℝ)))
  · simpa only [coordinateZeroProjection, h, ite_false] using
      (contDiff_apply ℝ ℝ d : ContDiff ℝ ∞ (fun v : D → ℝ => v d))

end Erdos3

end

end OAI
