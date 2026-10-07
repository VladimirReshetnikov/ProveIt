import Mathlib

namespace OAI

section

namespace Erdos3.CyclicCrootSisask

def samplingMomentCost (m k : ℕ) : ℝ :=
  2 * ((8 * (m : ℝ)) ^ m * (k : ℝ) ^ (m - 1) * k * 2 ^ (2 * m))

theorem samplingMomentCost_nonneg (m k : ℕ) : 0 ≤ samplingMomentCost m k := by
  unfold samplingMomentCost
  positivity

theorem samplingMomentCost_error {m k : ℕ} (hm : 0 < m) {epsilon : ℝ}
    (hsize : 256 * (m : ℝ) ≤ epsilon ^ 2 * k) :
    2 ^ (2 * m) * samplingMomentCost m k ≤ (k : ℝ) ^ (2 * m) * epsilon ^ (2 * m) := by
  have hkpow : (k : ℝ) ^ (m - 1) * k = (k : ℝ) ^ m := pow_sub_one_mul hm.ne' _
  have hcoeff : (2 : ℝ) ^ (2 * m) * 2 ^ (2 * m) * (8 * (m : ℝ)) ^ m =
      (128 * (m : ℝ)) ^ m := by
    rw [pow_mul, ← mul_pow, ← mul_pow]
    congr 1
    ring
  have hidentity : (2 : ℝ) ^ (2 * m) * samplingMomentCost m k =
      2 * (128 * (m : ℝ)) ^ m * (k : ℝ) ^ m := by
    unfold samplingMomentCost
    calc
      _ = 2 * ((2 : ℝ) ^ (2 * m) * 2 ^ (2 * m) * (8 * (m : ℝ)) ^ m) *
          ((k : ℝ) ^ (m - 1) * k) := by ring
      _ = _ := by rw [hcoeff, hkpow]
  have htwo : (2 : ℝ) ≤ 2 ^ m := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (show 1 ≤ m by omega)
  have hbase : 2 * (128 * (m : ℝ)) ≤ epsilon ^ 2 * k := by linarith
  have hpower := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 * (128 * (m : ℝ))) hbase m
  have hnum : 2 * (128 * (m : ℝ)) ^ m ≤ epsilon ^ (2 * m) * (k : ℝ) ^ m := by
    calc
      _ ≤ 2 ^ m * (128 * (m : ℝ)) ^ m := mul_le_mul_of_nonneg_right htwo (by positivity)
      _ ≤ (epsilon ^ 2 * k) ^ m := by simpa only [mul_pow] using hpower
      _ = _ := by rw [mul_pow, ← pow_mul]
  rw [hidentity]
  calc
    _ ≤ (epsilon ^ (2 * m) * (k : ℝ) ^ m) * (k : ℝ) ^ m :=
      mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = _ := by rw [pow_mul]; ring

noncomputable def crootSisaskSampleSize (m : ℕ) (epsilon : ℝ) : ℕ :=
  ⌈256 * (m : ℝ) / epsilon ^ 2⌉₊

theorem crootSisaskSampleSize_pos {m : ℕ} (hm : 0 < m) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < crootSisaskSampleSize m epsilon := by
  apply Nat.ceil_pos.mpr
  positivity

theorem crootSisaskSampleSize_bound (m : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    256 * (m : ℝ) ≤ epsilon ^ 2 * crootSisaskSampleSize m epsilon := by
  have h := Nat.le_ceil (256 * (m : ℝ) / epsilon ^ 2)
  have h' := (div_le_iff₀ (sq_pos_of_pos hepsilon)).mp h
  simpa only [crootSisaskSampleSize, mul_comm] using h'

end Erdos3.CyclicCrootSisask

end

end OAI
