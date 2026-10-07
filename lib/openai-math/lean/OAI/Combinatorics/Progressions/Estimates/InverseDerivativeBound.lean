import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul

namespace OAI

section

namespace Erdos3

open ContinuousLinearMap

theorem ringInverse_fderiv_norm_le
    {E R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedRing R] [HasSummableGeomSeries R] [NormedAlgebra ℝ R]
    (A : E → R) {x : E} (hA : DifferentiableAt ℝ A x) (hu : IsUnit (A x)) (v : E) :
    ‖fderiv ℝ (fun y => Ring.inverse (A y)) x v‖ ≤
      ‖Ring.inverse (A x)‖ ^ 2 * ‖fderiv ℝ A x v‖ := by
  have hnorm : ‖fderiv ℝ (Ring.inverse : R → R) (A x)‖ ≤ ‖Ring.inverse (A x)‖ ^ 2 := by
    rcases hu with ⟨u, heq⟩
    rw [← heq, fderiv_inverse, norm_neg, Ring.inverse_unit]
    exact (opNorm_mulLeftRight_apply_apply_le ℝ R _ _).trans_eq (by ring)
  change ‖fderiv ℝ (Ring.inverse ∘ A) x v‖ ≤ _
  rw [fderiv_comp x (differentiableAt_inverse hu) hA, ContinuousLinearMap.comp_apply]
  exact ((fderiv ℝ Ring.inverse (A x)).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))

theorem continuousLinearMap_isUnit_of_isInvertible
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A : F →L[ℝ] F} (hA : A.IsInvertible) : IsUnit A := by
  rcases hA with ⟨e, he⟩
  exact ⟨(ContinuousLinearEquiv.unitsEquiv ℝ F).symm e, he⟩

theorem inverseMap_fderiv_norm_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (A : E → F →L[ℝ] F) {x : E} (hA : DifferentiableAt ℝ A x)
    (hu : (A x).IsInvertible) (v : E) :
    ‖fderiv ℝ (fun y => (A y).inverse) x v‖ ≤
      ‖(A x).inverse‖ ^ 2 * ‖fderiv ℝ A x v‖ := by
  have h := ringInverse_fderiv_norm_le A hA (continuousLinearMap_isUnit_of_isInvertible hu) v
  simpa only [ContinuousLinearMap.ringInverse_eq_inverse] using h

end Erdos3

end

end OAI
