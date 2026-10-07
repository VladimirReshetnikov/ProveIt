import OAI.Combinatorics.Progressions.Results.Basic

namespace OAI

section

namespace Erdos3

theorem anova_moment_coefficient {k : ℕ} (hk : 0 < k) {n R : ℝ}
    (hn : 0 ≤ n) (h : 4 * n ≤ R ^ 2) :
    Real.exp 1 * n ^ k ≤ R ^ (2 * k) := by
  have he : Real.exp 1 ≤ (4 : ℝ) := Real.exp_one_lt_three.le.trans (by norm_num)
  have hpow : (4 : ℝ) ≤ 4 ^ k := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hk
  calc
    Real.exp 1 * n ^ k ≤ 4 ^ k * n ^ k :=
      mul_le_mul_of_nonneg_right (he.trans hpow) (pow_nonneg hn _)
    _ = (4 * n) ^ k := (mul_pow _ _ _).symm
    _ ≤ (R ^ 2) ^ k := pow_le_pow_left₀ (mul_nonneg (by norm_num) hn) h k
    _ = R ^ (2 * k) := (pow_mul _ _ _).symm

theorem anova_moment_scale {K p : ℝ} (hK : 1 ≤ K) (hp : 0 ≤ p)
    {q k : ℕ} (hk : 0 < k) (hkP : (k : ℝ) ≤ p) (hqP : (q : ℝ) ≤ p + 2) :
    Real.exp 1 * ((q * k : ℕ) : ℝ) ^ k ≤ (4 * (1 + K) * (p + 2)) ^ (2 * k) := by
  apply anova_moment_coefficient hk (by positivity)
  have hprod : ((q * k : ℕ) : ℝ) ≤ (p + 2) ^ 2 := by
    rw [Nat.cast_mul]
    have h := mul_le_mul hqP (show (k : ℝ) ≤ p + 2 by linarith)
      (by positivity : 0 ≤ (k : ℝ)) (by linarith : 0 ≤ p + 2)
    nlinarith
  have hR : 2 * (p + 2) ≤ 4 * (1 + K) * (p + 2) := by nlinarith
  nlinarith [sq_nonneg (4 * (1 + K) * (p + 2) - 2 * (p + 2))]

end Erdos3

end

section

namespace Erdos3

theorem approx_anova_moment_scale {K p : ℝ} (hK : 1 ≤ K) (hp : 0 ≤ p)
    {q k : ℕ} (hk : 0 < k) (hkP : (k : ℝ) ≤ p) (hqP : (q : ℝ) ≤ p + 2) :
    2 * Real.exp 1 * ((q * k : ℕ) : ℝ) ^ k ≤ (8 * (1 + K) * (p + 2)) ^ (2 * k) := by
  let D := 4 * (1 + K) * (p + 2)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have htwo : (2 : ℝ) ≤ 2 ^ (2 * k) := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 1 ≤ 2 * k)
  calc
    _ = 2 * (Real.exp 1 * ((q * k : ℕ) : ℝ) ^ k) := by ring
    _ ≤ 2 * D ^ (2 * k) := mul_le_mul_of_nonneg_left (anova_moment_scale hK hp hk hkP hqP) (by norm_num)
    _ ≤ 2 ^ (2 * k) * D ^ (2 * k) := mul_le_mul_of_nonneg_right htwo (pow_nonneg hD _)
    _ = (2 * D) ^ (2 * k) := (mul_pow _ _ _).symm
    _ = _ := by congr 1; dsimp [D]; ring

end Erdos3

end

end OAI
