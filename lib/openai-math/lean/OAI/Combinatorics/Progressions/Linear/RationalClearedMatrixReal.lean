import Mathlib.Basic.Real.Basic
import OAI.Combinatorics.Progressions.Sampling.RationalSpanGrid

namespace OAI

section

namespace Erdos3

open scoped Classical

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem matrixDenominator_mul_entry_real (S : Matrix ι κ ℚ) (i : ι) (j : κ) :
    (matrixDenominator S : ℝ) * (S i j : ℝ) = (clearedMatrix S i j : ℝ) := by
  classical
  have h : (clearedMatrix S i j : ℚ) = (matrixDenominator S : ℚ) * S i j :=
    congrFun (congrFun (clearedMatrix_cast S) i) j
  exact_mod_cast h.symm

theorem matrixDenominator_mul_entry_real_integral (S : Matrix ι κ ℚ) (i : ι) (j : κ) :
    ∃ z : ℤ, (matrixDenominator S : ℝ) * (S i j : ℝ) = (z : ℝ) :=
  ⟨clearedMatrix S i j, matrixDenominator_mul_entry_real S i j⟩

end Erdos3

end

end OAI
