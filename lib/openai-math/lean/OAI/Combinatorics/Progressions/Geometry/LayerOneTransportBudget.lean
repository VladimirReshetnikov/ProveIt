import OAI.Combinatorics.Progressions.Estimates.RationalPowerHeight

namespace OAI

section

namespace Erdos3

theorem layerOne_basis_transport_height_le_exp (a m J : ℕ) (C p : ℝ)
    (hp : 0 ≤ p) (ha : (a : ℝ) ≤ p) (hm : (m : ℝ) ≤ Real.exp p)
    (hC0 : 0 ≤ C) (hC : C ≤ Real.exp p) (hJ : (J : ℝ) ≤ Real.exp p) :
    (((a + 1) * (max m (Nat.ceil ((m : ℝ) * C)) * J) ^ a : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ 3) := by
  have hprod : (m : ℝ) * C ≤ Real.exp (2 * p) := by
    calc
      _ ≤ Real.exp p * Real.exp p := mul_le_mul hm hC hC0 (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hheight : ((max m (Nat.ceil ((m : ℝ) * C)) : ℕ) : ℝ) ≤ Real.exp (2 * p + 1) := by
    rw [Nat.cast_max]
    apply max_le
    · exact hm.trans (Real.exp_le_exp.mpr (by linarith))
    · calc
        _ ≤ (Nat.ceil (Real.exp (2 * p)) : ℝ) := Nat.cast_le.mpr (Nat.ceil_mono hprod)
        _ ≤ _ := ceil_exp_le_exp_add_one (by positivity)
  have hHJ : ((max m (Nat.ceil ((m : ℝ) * C)) : ℕ) : ℝ) * J ≤ Real.exp (3 * p + 1) := by
    calc
      _ ≤ Real.exp (2 * p + 1) * Real.exp p :=
        mul_le_mul hheight hJ (Nat.cast_nonneg J) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hpow := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg J)) hHJ a
  rw [← Real.exp_nat_mul] at hpow
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_mul]
  calc
    _ ≤ Real.exp a * Real.exp ((a : ℝ) * (3 * p + 1)) :=
      mul_le_mul (Real.add_one_le_exp a) hpow (by positivity) (Real.exp_nonneg _)
    _ = Real.exp ((a : ℝ) * (3 * p + 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (p * (3 * p + 2)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ha (by positivity))
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hp (sq_nonneg p)])

end Erdos3

end

end OAI
