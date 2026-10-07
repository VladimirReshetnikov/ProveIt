import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

section

namespace Erdos3

theorem relativeReturnedNormalization_denominator_pos (D s : ℕ) :
    (0 : ℝ) < ((D + 1) * (s + 1) ^ D : ℕ) := by
  positivity

theorem relativeReturnedNormalization_denominator_le_exp (D s : ℕ)
    {cost : ℝ} (hD : (D : ℝ) ≤ cost) :
    (((D + 1) * (s + 1) ^ D : ℕ) : ℝ) ≤ Real.exp (((s : ℝ) + 1) * cost) := by
  have hD1 : ((D + 1 : ℕ) : ℝ) ≤ Real.exp cost := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith only [hD, Real.add_one_le_exp cost]
  have hs1 : ((s + 1 : ℕ) : ℝ) ≤ Real.exp (s : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Real.add_one_le_exp (s : ℝ)
  have hpower : (((s + 1) ^ D : ℕ) : ℝ) ≤ Real.exp ((s : ℝ) * cost) := by
    calc
      _ = ((s + 1 : ℕ) : ℝ) ^ D := Nat.cast_pow _ _
      _ ≤ (Real.exp (s : ℝ)) ^ D := pow_le_pow_left₀ (Nat.cast_nonneg _) hs1 D
      _ = Real.exp ((D : ℝ) * s) := (Real.exp_nat_mul (s : ℝ) D).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg s))
  calc
    _ = ((D + 1 : ℕ) : ℝ) * (((s + 1) ^ D : ℕ) : ℝ) := Nat.cast_mul _ _
    _ ≤ Real.exp cost * Real.exp ((s : ℝ) * cost) :=
      mul_le_mul hD1 hpower (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (((s : ℝ) + 1) * cost) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem relativeReturnedNormalization_mass_pos (D s : ℕ)
    {originalMass normBudget : ℝ} (hmass : 0 < originalMass) :
    0 < (originalMass / ((D + 1) * (s + 1) ^ D : ℕ)) * Real.exp (-normBudget) :=
  mul_pos (div_pos hmass (relativeReturnedNormalization_denominator_pos D s)) (Real.exp_pos _)

theorem relativeReturnedNormalization_mass_expression_lower (D s : ℕ)
    {cost massLog normBudget originalMass : ℝ}
    (hD : (D : ℝ) ≤ cost) (hmass : Real.exp (-massLog) ≤ originalMass) :
    Real.exp (-(massLog + ((s : ℝ) + 1) * cost + normBudget)) ≤
      (originalMass / ((D + 1) * (s + 1) ^ D : ℕ)) * Real.exp (-normBudget) := by
  have hden := relativeReturnedNormalization_denominator_pos D s
  have hbound := relativeReturnedNormalization_denominator_le_exp D s hD
  have hdiv : Real.exp (-massLog) / Real.exp (((s : ℝ) + 1) * cost) ≤
      originalMass / ((D + 1) * (s + 1) ^ D : ℕ) :=
    (div_le_div_of_nonneg_left (Real.exp_nonneg _) hden hbound).trans
      (div_le_div_of_nonneg_right hmass hden.le)
  calc
    _ = (Real.exp (-massLog) / Real.exp (((s : ℝ) + 1) * cost)) *
        Real.exp (-normBudget) := by
      rw [← Real.exp_sub, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hdiv (Real.exp_nonneg _)

theorem relativeReturnedNormalization_mass_lower (D s : ℕ)
    {cost massLog normBudget originalMass normalizedMass : ℝ}
    (hD : (D : ℝ) ≤ cost) (hmass : Real.exp (-massLog) ≤ originalMass)
    (hnormalized : (originalMass / ((D + 1) * (s + 1) ^ D : ℕ)) * Real.exp (-normBudget) ≤
      normalizedMass) :
    Real.exp (-(massLog + ((s : ℝ) + 1) * cost + normBudget)) ≤ normalizedMass :=
  (relativeReturnedNormalization_mass_expression_lower D s hD hmass).trans hnormalized

end Erdos3

end

section

namespace Erdos3

theorem preparedReady_mass_lower {p gain originalMass : ℝ}
    (hgain : Real.exp (-p) ≤ gain) (hmass : gain / 16 < originalMass) :
    Real.exp (-(p + 16)) ≤ originalMass := by
  have h16 : (16 : ℝ) ≤ Real.exp 16 := by
    linarith only [Real.add_one_le_exp (16 : ℝ)]
  have hexp : Real.exp (-(p + 16)) = Real.exp (-p) / Real.exp 16 := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [hexp]
  exact ((div_le_div_of_nonneg_left (Real.exp_nonneg (-p)) (by norm_num) h16).trans
    (div_le_div_of_nonneg_right hgain (by norm_num))).trans hmass.le

theorem preparedReady_normalized_mass_lower (D s : ℕ)
    {p gain originalMass childCost normBudget : ℝ}
    (hD : (D : ℝ) ≤ childCost) (hgain : Real.exp (-p) ≤ gain)
    (hmass : gain / 16 < originalMass) :
    Real.exp (-(p + 16 + ((s : ℝ) + 1) * childCost + normBudget)) ≤
      (originalMass / ((D + 1) * (s + 1) ^ D : ℕ)) * Real.exp (-normBudget) :=
  relativeReturnedNormalization_mass_expression_lower D s hD
    (preparedReady_mass_lower hgain hmass)

theorem preparedReady_capped_normalized_mass_lower (rankBound s : ℕ)
    {p gain originalMass childCost normBudget : ℝ} (hcost : 0 ≤ childCost)
    (hgain : Real.exp (-p) ≤ gain) (hmass : gain / 16 < originalMass) :
    let D := min rankBound ⌊childCost⌋₊
    Real.exp (-(p + 16 + ((s : ℝ) + 1) * childCost + normBudget)) ≤
      (originalMass / ((D + 1) * (s + 1) ^ D : ℕ)) * Real.exp (-normBudget) := by
  apply preparedReady_normalized_mass_lower _ _ _ hgain hmass
  exact (Nat.cast_le.mpr (min_le_right _ _)).trans (Nat.floor_le hcost)

end Erdos3

end

end OAI
