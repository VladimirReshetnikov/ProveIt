import Mathlib

namespace OAI

section

namespace Erdos3

theorem polynomial_partition_exponent_step (k p w d : ℕ) :
    (p * (d + 1) ^ (2 * k)) * ((k + 3) * w * (d + 1) ^ 2 + 1) ≤
      (p * ((k + 3) * w + 1)) * (d + 1) ^ (2 * (k + 1)) := by
  have hd : 1 ≤ (d + 1) ^ 2 := one_le_pow₀ (by omega)
  have hfactor : (k + 3) * w * (d + 1) ^ 2 + 1 ≤
      ((k + 3) * w + 1) * (d + 1) ^ 2 := by nlinarith
  have h := Nat.mul_le_mul_left (p * (d + 1) ^ (2 * k)) hfactor
  have hid : (p * (d + 1) ^ (2 * k)) * (((k + 3) * w + 1) * (d + 1) ^ 2) =
      (p * ((k + 3) * w + 1)) * (d + 1) ^ (2 * (k + 1)) := by
    rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
    ring
  rwa [hid] at h

theorem polynomial_partition_error_step (k : ℕ) {L : ℝ} (hL : 0 ≤ L)
    {H T : ℕ} (hH : 0 < H) (hHT : H ≤ T) :
    L / T + (k : ℝ) * L / H ≤ ((k + 1 : ℕ) : ℝ) * L / H := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hHTR : (H : ℝ) ≤ T := by exact_mod_cast hHT
  have h := div_le_div_of_nonneg_left hL hHR hHTR
  calc
    _ ≤ L / H + (k : ℝ) * L / H := add_le_add h le_rfl
    _ = _ := by push_cast; ring

end Erdos3

end

end OAI
