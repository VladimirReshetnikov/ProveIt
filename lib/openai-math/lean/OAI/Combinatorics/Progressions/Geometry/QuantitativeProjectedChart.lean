import OAI.Combinatorics.Progressions.Dynamics.ProjectedAxisBudgets
import OAI.Combinatorics.Progressions.Fourier.QuarticBohrProgression

namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped BigOperators

theorem exists_normalized_projected_chart {J : Type*} [Fintype J]
    (W : Submodule ℝ (EuclideanSpace ℝ J))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice J) W)] :
    let n := finrank ℝ Wᗮ
    let B := projectedAxisNormBudget n
    let D := projectedAxisDefectBudget n
    ∃ b : Basis (Fin n) ℝ Wᗮ,
      span ℤ (Set.range b) = projectedIntegerLattice W ∧
      (∀ i, 0 < basisAxisScale b i) ∧
      (∀ i, 1 ≤ ‖normalizedAxisBasis b i‖ ∧ ‖normalizedAxisBasis b i‖ ≤ B + 1) ∧
      (∀ x, ‖normalizedOrthogonalChart W b x‖ ≤
        (1 + (n : ℝ) * n.factorial * (B + 1) ^ (n - 1) * D) * ‖x‖) ∧
      (∀ p, ‖(normalizedOrthogonalChart W b).symm p‖ ≤ (1 + (n : ℝ) * (B + 1)) * ‖p‖) ∧
      1 / ((n.factorial : ℝ) * (B + 1) ^ n) ≤
        ZLattice.covolume (latticeSection (standardEuclideanLattice J) W) /
          (∏ i, (basisAxisScale b i : ℝ)) ∧
      ZLattice.covolume (latticeSection (standardEuclideanLattice J) W) /
          (∏ i, (basisAxisScale b i : ℝ)) ≤ D := by
  let n := finrank ℝ Wᗮ
  let o := stdOrthonormalBasis ℝ Wᗮ
  obtain ⟨b, hspan, hprod, hnorm⟩ := exists_projected_basis_with_axis_budgets W
  have hprod' : (∏ i, ‖b i‖) ≤ projectedAxisDefectBudget n *
      ZLattice.covolume (span ℤ (Set.range b)) := by
    rw [hspan]
    exact hprod
  have hpair : ZLattice.covolume (latticeSection (standardEuclideanLattice J) W) *
      ZLattice.covolume (span ℤ (Set.range b)) = 1 := by
    rw [hspan]
    exact projectedIntegerLattice_covolume W
  refine ⟨b, hspan, basisAxisScale_pos b, normalizedAxisBasis_norm_bounds b hnorm,
    ?_, ?_, ?_⟩
  · exact normalizedOrthogonalChart_norm_le W b o (projectedAxisNormBudget_pos n).le
      (projectedAxisDefectBudget_pos n) hnorm hprod'
  · exact normalizedOrthogonalChart_symm_norm_le W b (projectedAxisNormBudget_pos n).le hnorm
  · exact normalizedAxisBasis_covolume_ratio_bounds o b (projectedAxisDefectBudget_pos n)
      hnorm hprod' hpair

end Erdos3

end

section

namespace Erdos3

theorem projectedAxisNormBudget_le_exp (n : ℕ) :
    projectedAxisNormBudget n ≤ Real.exp (4 * ((n : ℝ) + 1) ^ 2) := by
  have hn := Real.add_one_le_exp (n : ℝ)
  have hf := factorial_le_exp_sq n
  have hm := BohrProgression.minkowskiSecondConstant_le_exp n
  have hm0 := BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant_nonneg n
  unfold projectedAxisNormBudget
  calc
    _ ≤ Real.exp n * Real.exp ((n : ℝ) ^ 2) * Real.exp (2 * (n : ℝ) ^ 2) := by
      gcongr
    _ = Real.exp ((n : ℝ) + (n : ℝ) ^ 2 + 2 * (n : ℝ) ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])

theorem projectedAxisDefectBudget_le_exp (n : ℕ) :
    projectedAxisDefectBudget n ≤ Real.exp (4 * ((n : ℝ) + 1) ^ 2) := by
  have hn := Real.add_one_le_exp (n : ℝ)
  have hm := BohrProgression.minkowskiSecondConstant_le_exp n
  have hm0 := BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant_nonneg n
  unfold projectedAxisDefectBudget
  calc
    _ ≤ (Real.exp n) ^ n * Real.exp (2 * (n : ℝ) ^ 2) := by gcongr
    _ = Real.exp ((n : ℝ) * n + 2 * (n : ℝ) ^ 2) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])

theorem projectedAxisNormBudget_add_one_le_exp (n : ℕ) :
    projectedAxisNormBudget n + 1 ≤ Real.exp (5 * ((n : ℝ) + 1) ^ 2) := by
  have h := one_add_le_exp_succ (by positivity : 0 ≤ 4 * ((n : ℝ) + 1) ^ 2)
    (projectedAxisNormBudget_le_exp n)
  calc
    _ ≤ Real.exp (4 * ((n : ℝ) + 1) ^ 2 + 1) := by simpa only [add_comm] using h
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])

theorem projectedChart_forwardBudget_le_exp (n : ℕ) :
    1 + (n : ℝ) * n.factorial * (projectedAxisNormBudget n + 1) ^ (n - 1) *
      projectedAxisDefectBudget n ≤ Real.exp (20 * ((n : ℝ) + 1) ^ 3) := by
  have hn : (n : ℝ) ≤ Real.exp n := by linarith [Real.add_one_le_exp (n : ℝ)]
  have hf := factorial_le_exp_sq n
  have hb := projectedAxisNormBudget_add_one_le_exp n
  have hd := projectedAxisDefectBudget_le_exp n
  have hd0 := (projectedAxisDefectBudget_pos n).le
  have hb0 := (projectedAxisNormBudget_pos n).le
  have hp : (projectedAxisNormBudget n + 1) ^ (n - 1) ≤
      (projectedAxisNormBudget n + 1) ^ n :=
    pow_le_pow_right₀ (by linarith) (Nat.sub_le _ _)
  have hterm : (n : ℝ) * n.factorial * (projectedAxisNormBudget n + 1) ^ (n - 1) *
      projectedAxisDefectBudget n ≤
      Real.exp ((n : ℝ) + (n : ℝ) ^ 2 + n * (5 * ((n : ℝ) + 1) ^ 2) +
        4 * ((n : ℝ) + 1) ^ 2) := by
    calc
      _ ≤ (n : ℝ) * n.factorial * (projectedAxisNormBudget n + 1) ^ n *
          projectedAxisDefectBudget n := by gcongr
      _ ≤ Real.exp n * Real.exp ((n : ℝ) ^ 2) *
          (Real.exp (5 * ((n : ℝ) + 1) ^ 2)) ^ n *
          Real.exp (4 * ((n : ℝ) + 1) ^ 2) := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply (one_add_le_exp_succ (by positivity) hterm).trans
  apply Real.exp_le_exp.mpr
  have hn0 := Nat.cast_nonneg (α := ℝ) n
  have hn3 : 0 ≤ (n : ℝ) ^ 3 := by positivity
  nlinarith

theorem projectedChart_inverseBudget_le_exp (n : ℕ) :
    1 + (n : ℝ) * (projectedAxisNormBudget n + 1) ≤
      Real.exp (20 * ((n : ℝ) + 1) ^ 3) := by
  have hn : (n : ℝ) ≤ Real.exp n := by linarith [Real.add_one_le_exp (n : ℝ)]
  have hb := projectedAxisNormBudget_add_one_le_exp n
  have hb0 := (projectedAxisNormBudget_pos n).le
  have hterm : (n : ℝ) * (projectedAxisNormBudget n + 1) ≤
      Real.exp ((n : ℝ) + 5 * ((n : ℝ) + 1) ^ 2) := by
    calc
      _ ≤ Real.exp n * Real.exp (5 * ((n : ℝ) + 1) ^ 2) := by gcongr
      _ = _ := (Real.exp_add _ _).symm
  apply (one_add_le_exp_succ (by positivity) hterm).trans
  apply Real.exp_le_exp.mpr
  have hn0 := Nat.cast_nonneg (α := ℝ) n
  have hn3 : 0 ≤ (n : ℝ) ^ 3 := by positivity
  nlinarith

theorem projectedChart_volumeBudget_le_exp (n : ℕ) :
    (n.factorial : ℝ) * (projectedAxisNormBudget n + 1) ^ n ≤
      Real.exp (20 * ((n : ℝ) + 1) ^ 3) := by
  have hf := factorial_le_exp_sq n
  have hb := projectedAxisNormBudget_add_one_le_exp n
  have hb0 := (projectedAxisNormBudget_pos n).le
  calc
    _ ≤ Real.exp ((n : ℝ) ^ 2) * (Real.exp (5 * ((n : ℝ) + 1) ^ 2)) ^ n := by gcongr
    _ = Real.exp ((n : ℝ) ^ 2 + n * (5 * ((n : ℝ) + 1) ^ 2)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hn0 := Nat.cast_nonneg (α := ℝ) n
      have hn3 : 0 ≤ (n : ℝ) ^ 3 := by positivity
      nlinarith

theorem projectedChart_defectBudget_le_exp (n : ℕ) :
    projectedAxisDefectBudget n ≤ Real.exp (20 * ((n : ℝ) + 1) ^ 3) := by
  apply (projectedAxisDefectBudget_le_exp n).trans
  apply Real.exp_le_exp.mpr
  have hn0 := Nat.cast_nonneg (α := ℝ) n
  have hn3 : 0 ≤ (n : ℝ) ^ 3 := by positivity
  nlinarith

end Erdos3

end

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped BigOperators

theorem exists_quantitative_projected_chart {J : Type*} [Fintype J]
    (W : Submodule ℝ (EuclideanSpace ℝ J))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice J) W)] :
    let n := finrank ℝ Wᗮ
    let C : ℝ := 20 * ((n : ℝ) + 1) ^ 3
    ∃ b : Basis (Fin n) ℝ Wᗮ,
      span ℤ (Set.range b) = projectedIntegerLattice W ∧
      (∀ i, 0 < basisAxisScale b i) ∧
      (∀ x, ‖normalizedOrthogonalChart W b x‖ ≤ Real.exp C * ‖x‖) ∧
      (∀ p, ‖(normalizedOrthogonalChart W b).symm p‖ ≤ Real.exp C * ‖p‖) ∧
      Real.exp (-C) ≤
        ZLattice.covolume (latticeSection (standardEuclideanLattice J) W) /
          (∏ i, (basisAxisScale b i : ℝ)) ∧
      ZLattice.covolume (latticeSection (standardEuclideanLattice J) W) /
          (∏ i, (basisAxisScale b i : ℝ)) ≤ Real.exp C := by
  let n := finrank ℝ Wᗮ
  obtain ⟨b, hspan, hK, _, hf, hi, hvlo, hvhi⟩ := exists_normalized_projected_chart W
  refine ⟨b, hspan, hK, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (hf x).trans (mul_le_mul_of_nonneg_right (projectedChart_forwardBudget_le_exp n)
      (norm_nonneg x))
  · intro p
    exact (hi p).trans (mul_le_mul_of_nonneg_right (projectedChart_inverseBudget_le_exp n)
      (norm_nonneg p))
  · apply le_trans _ hvlo
    rw [Real.exp_neg, one_div]
    apply (inv_le_inv₀ (Real.exp_pos _) _).2
    · exact projectedChart_volumeBudget_le_exp n
    · have hB := projectedAxisNormBudget_pos n
      positivity
  · exact hvhi.trans (projectedChart_defectBudget_le_exp n)

end Erdos3

end

end OAI
