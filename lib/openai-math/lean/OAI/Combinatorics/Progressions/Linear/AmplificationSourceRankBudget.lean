import OAI.Combinatorics.Progressions.Estimates.AmplificationFinalCostGrowth

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def amplificationSourceRankLogConstant (b C : ℕ) (K : ℝ) : ℝ :=
  1 + levelCoefficient K * Real.log b + C

theorem amplificationSourceRankLogConstant_pos {b C : ℕ} {K : ℝ}
    (hb : 1 ≤ b) (hK : 1 < K) :
    0 < amplificationSourceRankLogConstant b C K := by
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hprod := mul_nonneg (levelCoefficient_pos hK).le (Real.log_nonneg hb')
  unfold amplificationSourceRankLogConstant
  have := Nat.cast_nonneg (α := ℝ) C
  linarith

theorem log_linear_amplification_rank_le {b C d : ℕ} {K p : ℝ}
    (hb : 1 ≤ b) (hK : 1 < K) (hp : 2 ≤ p)
    (hd : d ≤ b ^ ⌊levelCoefficient K * Real.log p⌋₊ * ⌊(2 + p) ^ C⌋₊) :
    Real.log ((d : ℝ) + 1) ≤
      amplificationSourceRankLogConstant b C K * Real.log (2 + p) := by
  let j := ⌊levelCoefficient K * Real.log p⌋₊
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hbase : 1 ≤ (2 : ℝ) + p := by linarith
  have hbase0 : 0 < (2 : ℝ) + p := by linarith
  have hj : (j : ℝ) ≤ levelCoefficient K * Real.log p :=
    Nat.floor_le (mul_nonneg (levelCoefficient_pos hK).le (Real.log_nonneg (by linarith)))
  have hfloor := Nat.floor_le (pow_nonneg hbase0.le C)
  have hd' : (d : ℝ) ≤ (b : ℝ) ^ j * (2 + p) ^ C := by
    have hcast : (d : ℝ) ≤ (b : ℝ) ^ j * (⌊(2 + p) ^ C⌋₊ : ℝ) := by
      exact_mod_cast hd
    exact hcast.trans (mul_le_mul_of_nonneg_left hfloor (pow_nonneg hb0.le _))
  have hone : 1 ≤ (b : ℝ) ^ j * (2 + p) ^ C :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hb') (one_le_pow₀ hbase)
  have hlog := Real.log_le_log (by positivity : 0 < (d : ℝ) + 1)
    (show (d : ℝ) + 1 ≤ 2 * ((b : ℝ) ^ j * (2 + p) ^ C) by linarith)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlog
  have hjlog : (j : ℝ) * Real.log b ≤
      (levelCoefficient K * Real.log b) * Real.log (2 + p) := by
    calc
      (j : ℝ) * Real.log b ≤ (levelCoefficient K * Real.log p) * Real.log b :=
        mul_le_mul_of_nonneg_right hj (Real.log_nonneg hb')
      _ = (levelCoefficient K * Real.log b) * Real.log p := by ring
      _ ≤ (levelCoefficient K * Real.log b) * Real.log (2 + p) :=
        mul_le_mul_of_nonneg_left
          (Real.log_le_log (by linarith : 0 < p) (by linarith))
          (mul_nonneg (levelCoefficient_pos hK).le (Real.log_nonneg hb'))
  have htwo : Real.log 2 ≤ Real.log (2 + p) :=
    Real.log_le_log (by norm_num) (by linarith)
  unfold amplificationSourceRankLogConstant
  nlinarith

theorem log_linear_amplification_rank_source {b C d : ℕ} {K p : ℝ}
    (hb : 1 ≤ b) (hK : 1 < K) (hp : 2 ≤ p)
    (hd : d ≤ b ^ ⌊levelCoefficient K * Real.log p⌋₊ * ⌊(2 + p) ^ C⌋₊) :
    Real.log ((d : ℝ) + 1) ≤ amplificationSourceRankLogConstant b C K *
      p ^ (levelCoefficient K * Real.log 1) * Real.log (2 + p) := by
  simpa only [Real.log_one, mul_zero, Real.rpow_zero, mul_one] using
    log_linear_amplification_rank_le hb hK hp hd

end Erdos3

end

end OAI
