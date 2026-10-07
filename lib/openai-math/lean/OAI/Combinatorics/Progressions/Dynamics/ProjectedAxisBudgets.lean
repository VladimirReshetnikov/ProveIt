import OAI.Combinatorics.Progressions.Lattices.StandardLatticeCoordinates

namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory BohrLattice.MinkowskiSecondBox
open scoped BigOperators

noncomputable def projectedAxisNormBudget (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) * n.factorial * minkowskiSecondConstant n

noncomputable def projectedAxisDefectBudget (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ n * minkowskiSecondConstant n

theorem projectedAxisNormBudget_pos (n : ℕ) : 0 < projectedAxisNormBudget n := by
  unfold projectedAxisNormBudget minkowskiSecondConstant
  positivity

theorem projectedAxisDefectBudget_pos (n : ℕ) : 0 < projectedAxisDefectBudget n := by
  unfold projectedAxisDefectBudget minkowskiSecondConstant
  positivity

theorem exists_projected_basis_with_axis_budgets {J : Type*} [Fintype J]
    (W : Submodule ℝ (EuclideanSpace ℝ J))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice J) W)] :
    let n := finrank ℝ Wᗮ
    ∃ b : Basis (Fin n) ℝ Wᗮ,
      span ℤ (Set.range b) = projectedIntegerLattice W ∧
      (∏ i, ‖b i‖) ≤ projectedAxisDefectBudget n * ZLattice.covolume (projectedIntegerLattice W) ∧
      ∀ i, ‖b i‖ ≤ projectedAxisNormBudget n := by
  let n := finrank ℝ Wᗮ
  obtain ⟨b, hb, hprod, hnorm⟩ := exists_short_projected_integer_basis W
  have hpow : (n : ℝ) ^ n ≤ ((n : ℝ) + 1) ^ n :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (le_add_of_nonneg_right zero_le_one) n
  have hC := minkowskiSecondConstant_nonneg n
  refine ⟨b, hb, ?_, ?_⟩
  · exact hprod.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpow hC)
      (ZLattice.covolume_pos (projectedIntegerLattice W) volume).le)
  · intro i
    exact (hnorm i).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (Nat.cast_nonneg _)) hC)

end Erdos3

end

end OAI
