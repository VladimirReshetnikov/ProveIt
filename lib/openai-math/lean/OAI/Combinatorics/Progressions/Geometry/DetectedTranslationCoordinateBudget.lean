import OAI.Combinatorics.Progressions.Estimates.RationalPowerHeight

namespace OAI

section

namespace Erdos3

theorem detectedTranslationCoordinate_denominator_le_exp (n k m q : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hn : (n : ℝ) ≤ p) (hk : (k : ℝ) ≤ p)
    (hm : (m : ℝ) ≤ Real.exp p)
    (hq : q ≤ ⌈Real.exp p⌉₊ ^ (n * k) * m) :
    (q : ℝ) ≤ Real.exp ((p + 3) ^ 3) := by
  have hnk : (n : ℝ) * k ≤ p * p :=
    mul_le_mul hn hk (Nat.cast_nonneg _) hp
  have hnk' := mul_le_mul_of_nonneg_right hnk (show 0 ≤ p + 1 by positivity)
  have hlog : ((n * k : ℕ) : ℝ) * (p + 1) + p ≤ (p + 3) ^ 3 := by
    rw [Nat.cast_mul]
    nlinarith [sq_nonneg p]
  calc
    (q : ℝ) ≤ ((⌈Real.exp p⌉₊ ^ (n * k) * m : ℕ) : ℝ) := Nat.cast_le.mpr hq
    _ ≤ Real.exp (((n * k : ℕ) : ℝ) * (p + 1)) * Real.exp p := by
      rw [Nat.cast_mul]
      exact mul_le_mul (ceil_exp_power_le_exp hp (n * k)) hm
        (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (((n * k : ℕ) : ℝ) * (p + 1) + p) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hlog

theorem detectedTranslationCoordinate_slow_factor_le_exp (k : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hk : (k : ℝ) ≤ p) :
    (k : ℝ) * (⌈Real.exp p⌉₊ : ℝ) * Real.exp p ≤ Real.exp ((p + 3) ^ 3) := by
  have hkexp : (k : ℝ) ≤ Real.exp p :=
    hk.trans ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp p))
  calc
    _ ≤ Real.exp p * Real.exp (p + 1) * Real.exp p :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hkexp (ceil_exp_le_exp_add_one hp) (Nat.cast_nonneg _) (Real.exp_nonneg _))
        (Real.exp_nonneg _)
    _ = Real.exp (3 * p + 1) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p, pow_nonneg hp 3])

theorem detectedTranslationCoordinate_bounds (n k m q : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hn : (n : ℝ) ≤ p) (hk : (k : ℝ) ≤ p)
    (hm : (m : ℝ) ≤ Real.exp p)
    (hq : q ≤ ⌈Real.exp p⌉₊ ^ (n * k) * m) :
    (q : ℝ) ≤ Real.exp ((p + 3) ^ 3) ∧
      (k : ℝ) * (⌈Real.exp p⌉₊ : ℝ) * Real.exp p ≤ Real.exp ((p + 3) ^ 3) :=
  ⟨detectedTranslationCoordinate_denominator_le_exp n k m q hp hn hk hm hq,
    detectedTranslationCoordinate_slow_factor_le_exp k hp hk⟩

theorem detectedTranslationCoordinate_logcost {p : ℝ} (hp : 0 ≤ p) :
    p + (p + 3) ^ 3 ≤ (p + 3) ^ 4 := by
  have hp3 : p ≤ (p + 3) ^ 3 := by
    have h := le_power_budget (show 0 ≤ p + 1 by positivity) (by decide : 1 ≤ 3)
    have he : p + 1 + 2 = p + 3 := by ring
    rw [he] at h
    linarith
  calc
    _ ≤ 2 * (p + 3) ^ 3 := by linarith
    _ ≤ (p + 3) * (p + 3) ^ 3 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

end Erdos3

end

end OAI
