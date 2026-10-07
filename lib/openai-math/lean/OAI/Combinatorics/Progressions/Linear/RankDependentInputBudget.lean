import OAI.Combinatorics.Progressions.Dynamics.SparseGeneratorBudget

namespace OAI

section

namespace Erdos3

def rankDependentInputBudget (z : ℝ) : ℝ :=
  2 * z + 2 * (z + ((z + 2) ^ 3 + (z + 2) ^ 36)) +
    ((z + 2) ^ 3 + (z + 2) ^ 18 + z) + 2

theorem rankDependentInputBudget_bounds {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ rankDependentInputBudget z ∧ z ≤ rankDependentInputBudget z ∧
      2 * z ≤ rankDependentInputBudget z ∧
      2 * (z + ((z + 2) ^ 3 + (z + 2) ^ 36)) ≤ rankDependentInputBudget z ∧
      2 * (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z)) ≤
        Real.exp (rankDependentInputBudget z) := by
  let D := 2 * (z + ((z + 2) ^ 3 + (z + 2) ^ 36))
  let L := (z + 2) ^ 3 + (z + 2) ^ 18 + z
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hzL : z ≤ L := by
    dsimp only [L]
    have h₁ : 0 ≤ (z + 2) ^ 3 := by positivity
    have h₂ : 0 ≤ (z + 2) ^ 18 := by positivity
    linarith
  have hL : 0 ≤ L := hz.trans hzL
  have hbudget : rankDependentInputBudget z = 2 * z + D + L + 2 := rfl
  have hLbudget : L + 2 ≤ rankDependentInputBudget z := by rw [hbudget]; linarith
  refine ⟨by rw [hbudget]; linarith, by rw [hbudget]; linarith,
    by rw [hbudget]; linarith, ?_, ?_⟩
  · change D ≤ _
    rw [hbudget]
    linarith
  · have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hsum : Real.exp z + Real.exp L ≤ Real.exp (L + 1) := by
      calc
        Real.exp z + Real.exp L ≤ 2 * Real.exp L := by
          linarith [Real.exp_le_exp.mpr hzL]
        _ ≤ Real.exp 1 * Real.exp L := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
        _ = Real.exp (L + 1) := (mul_comm _ _).trans (Real.exp_add L 1).symm
    calc
      2 * (Real.exp z + Real.exp L) ≤ 2 * Real.exp (L + 1) := mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ ≤ Real.exp 1 * Real.exp (L + 1) := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = Real.exp (L + 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (rankDependentInputBudget z) := Real.exp_le_exp.mpr hLbudget

end Erdos3

end

end OAI
