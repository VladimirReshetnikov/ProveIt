import Surreal.Surcomplex.DecomposableKernelCriterion
import Mathlib.NumberTheory.Real.Irrational

/-!
# A nonzero kernel without an ordinary or omnific point

The example following `odg:dec:cor:converse`: the form `X - Y` has a
nonzero real and complex kernel, but its level at the real square root of
two has no omnific or Gaussian omnific points. Thus the ordinary-point
hypothesis in the criterion cannot be dropped.
-/

universe u
namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- The coefficient matrix of the two-variable difference form. -/
def differenceFormMatrix : Matrix Unit (Fin 2) ℂ := fun _ k => if k = 0 then 1 else -1

/-- The difference form has a nonzero real kernel, witnessed by the diagonal vector. -/
theorem differenceForm_real_kernel_ne_bot :
    LinearMap.ker (realKernelMatrix differenceFormMatrix).mulVecLin ≠ ⊥ := by
  apply (Submodule.ne_bot_iff _).mpr
  refine ⟨fun _ => 1, ?_, ?_⟩
  · rw [realKernelMatrix_mem_ker_iff]
    intro j
    simp [differenceFormMatrix, Fin.sum_univ_two]
  · intro h
    have := congrFun h 0
    norm_num at this

/-- The difference form also has a nonzero complex kernel. -/
theorem differenceForm_complex_kernel_ne_bot : LinearMap.ker differenceFormMatrix.mulVecLin ≠ ⊥ := by
  apply (Submodule.ne_bot_iff _).mpr
  refine ⟨fun _ => 1, ?_, ?_⟩
  · ext j
    simp [Matrix.mulVec, dotProduct, differenceFormMatrix, Fin.sum_univ_two]
  · intro h
    have := congrFun h 0
    norm_num at this

/-- No difference of real omnific integers is an irrational ordinary real constant. -/
theorem omnific_difference_ne_irrational (r : ℝ) (hr : Irrational r)
    (x y : SignSequence.OmnificInteger.{u}) :
    omnificSupportInclusion x - omnificSupportInclusion y ≠ complexConstants (r : ℂ) := by
  intro h
  have hc := congrArg constantCoeff h
  rw [map_sub, constantCoeff_omnificSupportInclusion, constantCoeff_omnificSupportInclusion,
    constantCoeff_complexConstants] at hc
  have hre := congrArg Complex.re hc
  apply hr.ne_int (SignSequence.omnificConstantCoeff x - SignSequence.omnificConstantCoeff y)
  simpa only [Int.cast_sub, Complex.sub_re, Complex.intCast_re, Complex.ofReal_re] using hre.symm

/-- The same obstruction holds for Gaussian omnific integers. -/
theorem gaussian_difference_ne_irrational (r : ℝ) (hr : Irrational r)
    (x y : GaussianOmnificInteger.{u}) :
    x.val - y.val ≠ complexConstants (r : ℂ) := by
  intro h
  have hc : GaussianInt.toComplex (gaussianOmnificConstantCoeff (x - y)) = (r : ℂ) := by
    rw [gaussianOmnificConstantCoeff_toComplex]
    change constantCoeff (x.val - y.val) = _
    rw [h, constantCoeff_complexConstants]
  apply hr.ne_int (gaussianOmnificConstantCoeff (x - y)).re
  have hre := congrArg Complex.re hc
  rw [← GaussianInt.intCast_re] at hre
  exact hre.symm

/-- The source's square-root-of-two level is empty over the real omnific integers. -/
theorem no_omnific_difference_sqrt_two :
    ¬ ∃ x y : SignSequence.OmnificInteger.{u},
      omnificSupportInclusion x - omnificSupportInclusion y = complexConstants (Real.sqrt 2 : ℂ) := by
  rintro ⟨x, y, h⟩
  exact omnific_difference_ne_irrational (Real.sqrt 2) irrational_sqrt_two x y h

/-- The same square-root-of-two level is empty over the Gaussian omnific integers. -/
theorem no_gaussian_difference_sqrt_two :
    ¬ ∃ x y : GaussianOmnificInteger.{u},
      x.val - y.val = complexConstants (Real.sqrt 2 : ℂ) := by
  rintro ⟨x, y, h⟩
  exact gaussian_difference_ne_irrational (Real.sqrt 2) irrational_sqrt_two x y h

end
end Surreal.Surcomplex
