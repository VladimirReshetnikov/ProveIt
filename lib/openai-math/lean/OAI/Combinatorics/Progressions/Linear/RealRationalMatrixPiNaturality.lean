/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. Import paths are adapted to Mathlib v4.32.0. -/
import OAI.Compat.TensorProduct
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Pi

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem rationalMatrix_piScalarRight_baseChange
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (A : Matrix I J ℚ) (x : ℝ ⊗[ℚ] (J → ℚ)) :
    TensorProduct.piScalarRight ℚ ℝ ℝ I (A.mulVecLin.baseChange ℝ x) =
      (Matrix.mulVecLin (fun i j => (A i j : ℝ)))
        (TensorProduct.piScalarRight ℚ ℝ ℝ J x) := by
  classical
  induction x using TensorProduct.inductionOn with
  | tmul a v =>
    rw [LinearMap.baseChange_tmul]
    simp only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Rat.smul_def]
    funext i
    change ((∑ j, A i j * v j : ℚ) : ℝ) * a =
      ∑ j, (A i j : ℝ) * ((v j : ℝ) * a)
    simp only [Rat.cast_sum, Rat.cast_mul, Finset.sum_mul, mul_assoc]
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3

end

end OAI
