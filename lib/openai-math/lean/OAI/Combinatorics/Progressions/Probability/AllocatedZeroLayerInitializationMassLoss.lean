import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

theorem allocatedZeroLayerInitialization_denominator_bound (s D : ℕ) {r : ℝ}
    (hD : (D : ℝ) ≤ r) :
    4 * (((D + 1) * (s + 1) ^ D : ℕ) : ℝ) ≤
      Real.exp (r + 5 + r * (s + 1)) := by
  have hs : (s + 1 : ℝ) ≤ Real.exp (s + 1) :=
    (le_add_of_nonneg_right (show (0 : ℝ) ≤ 1 by norm_num)).trans
      (Real.add_one_le_exp (s + 1))
  have hpow : ((s + 1 : ℕ) : ℝ) ^ D ≤ Real.exp (r * (s + 1)) := by
    calc
      _ ≤ (Real.exp (s + 1)) ^ D :=
        pow_le_pow_left₀ (by positivity)
          (by simpa only [Nat.cast_add, Nat.cast_one] using hs) D
      _ = Real.exp ((D : ℝ) * (s + 1)) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hD (by positivity))
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by
    linarith [Real.add_one_le_exp (4 : ℝ)]
  have hdim : (D + 1 : ℝ) ≤ Real.exp (r + 1) := by
    linarith [Real.add_one_le_exp (r + 1)]
  calc
    _ = (4 * (D + 1 : ℝ)) * ((s + 1 : ℕ) : ℝ) ^ D := by push_cast; ring
    _ ≤ (Real.exp 4 * Real.exp (r + 1)) * Real.exp (r * (s + 1)) :=
      mul_le_mul (mul_le_mul hfour hdim (by positivity) (Real.exp_nonneg _))
        hpow (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem allocatedZeroLayerInitialization_mass_loss (s D : ℕ) (p r L : ℝ)
    (hD : (D : ℝ) ≤ r) :
    Real.exp (-(L + p + r + 5 + r * (s + 1))) ≤
      ((Real.exp (-p) / 4) / (((D + 1) * (s + 1) ^ D : ℕ) : ℝ)) *
        Real.exp (-L) := by
  let denominator : ℝ := (((D + 1) * (s + 1) ^ D : ℕ) : ℝ)
  have hd0 : 0 < denominator := by dsimp only [denominator]; positivity
  have hden : 4 * denominator ≤ Real.exp (r + 5 + r * (s + 1)) :=
    allocatedZeroLayerInitialization_denominator_bound s D hD
  change Real.exp (-(L + p + r + 5 + r * (s + 1))) ≤
    (Real.exp (-p) / 4 / denominator) * Real.exp (-L)
  rw [div_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity : 0 < 4 * denominator)]
  calc
    _ ≤ Real.exp (-(L + p + r + 5 + r * (s + 1))) *
        Real.exp (r + 5 + r * (s + 1)) :=
      mul_le_mul_of_nonneg_left hden (Real.exp_nonneg _)
    _ = Real.exp (-p) * Real.exp (-L) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end Erdos3

end

end OAI
