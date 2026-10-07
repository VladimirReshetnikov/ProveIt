import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem factoredDifference_fderiv (F G R : E → Y) (t : ℝ)
    (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) (hR : Differentiable ℝ R)
    (he : ∀ x, F x - G x = t • R x) (x : E) :
    fderiv ℝ F x - fderiv ℝ G x = t • fderiv ℝ R x := by
  rw [← fderiv_sub (hF x) (hG x), show F - G = t • R from funext he,
    fderiv_const_smul (hR x)]

theorem factoredDifference_second_fderiv (F G R : E → Y) (t : ℝ)
    (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) (hR : ContDiff ℝ 2 R)
    (he : ∀ x, F x - G x = t • R x) (x : E) :
    fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ G) x = t • fderiv ℝ (fderiv ℝ R) x := by
  have hF' : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hG' : ContDiff ℝ 1 (fderiv ℝ G) := hG.fderiv_right (by norm_num)
  have hR' : ContDiff ℝ 1 (fderiv ℝ R) := hR.fderiv_right (by norm_num)
  exact factoredDifference_fderiv _ _ _ t (hF'.differentiable one_ne_zero)
    (hG'.differentiable one_ne_zero) (hR'.differentiable one_ne_zero)
    (factoredDifference_fderiv F G R t (hF.differentiable (by norm_num))
      (hG.differentiable (by norm_num)) (hR.differentiable (by norm_num)) he) x

theorem factoredDifference_c2_bounds (F G R : E → Y) (t : ℝ)
    (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) (hR : ContDiff ℝ 2 R)
    (he : ∀ x, F x - G x = t • R x) (x : E) {B₀ B₁ B₂ : ℝ}
    (h₀ : ‖R x‖ ≤ B₀) (h₁ : ‖fderiv ℝ R x‖ ≤ B₁) (h₂ : ‖fderiv ℝ (fderiv ℝ R) x‖ ≤ B₂) :
    ‖F x - G x‖ ≤ |t| * B₀ ∧ ‖fderiv ℝ F x - fderiv ℝ G x‖ ≤ |t| * B₁ ∧
      ‖fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ G) x‖ ≤ |t| * B₂ := by
  rw [he x, factoredDifference_fderiv F G R t (hF.differentiable (by norm_num))
    (hG.differentiable (by norm_num)) (hR.differentiable (by norm_num)) he x,
    factoredDifference_second_fderiv F G R t hF hG hR he x]
  refine ⟨?_, ?_, ?_⟩
  · exact (norm_smul_le t (R x)).trans (mul_le_mul_of_nonneg_left h₀ (abs_nonneg t))
  · exact (ContinuousLinearMap.opNorm_smul_le t (fderiv ℝ R x)).trans
      (mul_le_mul_of_nonneg_left h₁ (abs_nonneg t))
  · exact (ContinuousLinearMap.opNorm_smul_le t (fderiv ℝ (fderiv ℝ R) x)).trans
      (mul_le_mul_of_nonneg_left h₂ (abs_nonneg t))

end Erdos3

end

end OAI
