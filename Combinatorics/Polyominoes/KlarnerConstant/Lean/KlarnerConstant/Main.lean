import KlarnerConstant.CoefficientSystem
import KlarnerConstant.Growth

/-!
# Conditional supremal growth bounds

This module composes the exact finite recurrence certificate with the generic
growth-supremum theorem.  Its hypotheses isolate the remaining combinatorial
boundary: a natural-valued counting sequence must be dominated, after casting
to `ℚ`, by the `g` coordinate of a system satisfying Bui's seventeen weighted
prefix recurrences.
-/

namespace LeanProofs.KlarnerConstant

/--
Any natural-valued counting sequence dominated by the `g` coordinate of a
weighted Bui recurrence system has supremal exponential growth at most
`9047 / 2000 = 4.5235`.
-/
theorem growthSup_le_9047_div_2000_of_weightedBuiRecurrences
    {A : ℕ → ℕ} {S : CoefficientProfile}
    (R : WeightedBuiRecurrences certificateZeta S)
    (hA : ∀ n, (A n : ℚ) ≤ S.g n) :
    growthSup A ≤ (9047 / 2000 : ℝ) := by
  apply growthSup_le_of_le_pow (by norm_num)
  intro n
  have hq : (A n : ℚ) ≤ (9047 / 2000 : ℚ) ^ n :=
    R.dominatedCoefficient_le_9047_div_2000_pow hA n
  have hcast : ((A n : ℚ) : ℝ) ≤ (((9047 / 2000 : ℚ) ^ n : ℚ) : ℝ) :=
    (Rat.cast_le (K := ℝ)).2 hq
  have hbase : (((9047 / 2000 : ℚ) : ℝ)) = (9047 / 2000 : ℝ) := by
    norm_num
  simpa only [Rat.cast_natCast, Rat.cast_pow, hbase] using hcast

/-- The same supremal growth bound directly from Bui's seventeen pointwise
coefficient recurrences. -/
theorem growthSup_le_9047_div_2000_of_buiCoefficientRecurrences
    {A : ℕ → ℕ} {S : CoefficientProfile}
    (R : BuiCoefficientRecurrences S)
    (hA : ∀ n, (A n : ℚ) ≤ S.g n) :
    growthSup A ≤ (9047 / 2000 : ℝ) :=
  growthSup_le_9047_div_2000_of_weightedBuiRecurrences
    (R.toWeighted (le_of_lt certificateZeta_pos)) hA

end LeanProofs.KlarnerConstant
