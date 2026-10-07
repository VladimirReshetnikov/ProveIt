import OAI.Combinatorics.Progressions.Estimates.PreparedRelativeFinalPower

namespace OAI

section

namespace Erdos3

theorem allocatedNormalizationExponent_ge_two (s : ℕ) :
    2 ≤ (exists_relative_finite_returned_fiber_normalization.{0, 0} s).choose :=
  (exists_relative_finite_returned_fiber_normalization.{0, 0} s).choose_spec.1

theorem allocatedNormalizedBudget_bounds (s cardVars : ℕ) {childCost : ℝ}
    (hchild : 0 ≤ childCost) :
    let E := (exists_relative_finite_returned_fiber_normalization.{0, 0} s).choose
    let B := ((childCost + (cardVars : ℝ) + 2) + 2) ^ E
    childCost ≤ B ∧ 0 ≤ B ∧ (cardVars : ℝ) ≤ B := by
  dsimp only
  have hE := allocatedNormalizationExponent_ge_two s
  have hcard : (0 : ℝ) ≤ cardVars := Nat.cast_nonneg cardVars
  have hbase : 1 ≤ (childCost + (cardVars : ℝ) + 2) + 2 := by linarith
  have hpower : (childCost + (cardVars : ℝ) + 2) + 2 ≤
      ((childCost + (cardVars : ℝ) + 2) + 2) ^
        (exists_relative_finite_returned_fiber_normalization.{0, 0} s).choose := by
    simpa only [pow_one] using pow_le_pow_right₀ hbase (by omega : 1 ≤
      (exists_relative_finite_returned_fiber_normalization.{0, 0} s).choose)
  exact ⟨by linarith, by linarith, by linarith⟩

end Erdos3

end

end OAI
