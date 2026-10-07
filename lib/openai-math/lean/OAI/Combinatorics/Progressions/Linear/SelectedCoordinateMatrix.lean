import OAI.Combinatorics.Progressions.Geometry.CoordinateInjection
import OAI.Combinatorics.Progressions.Linear.MatrixSupInverse

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem clm_coordinateInjection_matrix {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : (κ → ℝ) →L[ℝ] (ι → ℝ)) (f : ι → κ) :
    A.comp (coordinateInjection f) =
      matrixSupCLM (fun row col => A (Pi.single (f col) 1) row) := by
  ext x row
  change A (coordinateInjection f x) row = _
  rw [coordinateInjection_apply, map_sum, Finset.sum_apply]
  change (∑ i, A (Pi.single (f i) (x i)) row) = ∑ i, A (Pi.single (f i) 1) row * x i
  apply Finset.sum_congr rfl
  intro i _
  have hs : Pi.single (f i) (x i) = (x i) • (Pi.single (f i) (1 : ℝ) : κ → ℝ) := by
    rw [← Pi.single_smul]
    simp
  rw [hs, map_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_comm]

end Erdos3

end

end OAI
