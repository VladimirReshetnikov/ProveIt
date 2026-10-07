import GowersSzemeredi.Proofs13FejerExplicitExponent
import Mathlib.Algebra.Order.Ring.Pow

/-! A sharper elementary comparison in the overlap with the endpoint
argument reduces the printed top length power from 2^70 to 2^61. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section13_improved_printed_top_comparison {alpha : Real}
    (hα : 0 < alpha) (hαupper : alpha ≤ 332 / 333) :
    (2 / alpha) ^ ((2 : Nat) ^ 53) ≤ (1 / alpha) ^ ((2 : Nat) ^ 61) := by
  let t : Real := 1 / alpha
  have ht : 1 + 1 / 332 ≤ t := by
    apply (le_div_iff₀ hα).mpr
    nlinarith only [hαupper]
  have ht1 : 1 ≤ t := by linarith only [ht]
  have hb := one_add_mul_sub_le_pow (by linarith only [ht1] : -1 ≤ t) 15
  have h15 : (347 / 332 : Real) ≤ t ^ (15 : Nat) := by
    norm_num only [Nat.cast_ofNat] at hb
    linarith only [ht, hb]
  have h255 : (2 : Real) ≤ t ^ (255 : Nat) := by
    calc
      _ ≤ (347 / 332 : Real) ^ (17 : Nat) := by norm_num
      _ ≤ (t ^ (15 : Nat)) ^ (17 : Nat) := pow_le_pow_left₀ (by norm_num) h15 17
      _ = _ := by rw [← pow_mul]
  have hstep : 2 * t ≤ t ^ ((2 : Nat) ^ 8) := by
    calc
      _ ≤ t ^ (255 : Nat) * t := mul_le_mul_of_nonneg_right h255 (zero_le_one.trans ht1)
      _ = _ := (pow_succ _ _).symm
  calc
    _ = (2 * t) ^ ((2 : Nat) ^ 53) := by congr 1; dsimp [t]; ring
    _ ≤ (t ^ ((2 : Nat) ^ 8)) ^ ((2 : Nat) ^ 53) := pow_le_pow_left₀ (by positivity) hstep _
    _ = t ^ ((2 : Nat) ^ 61) := by rw [← pow_mul]; congr 1

theorem section13_improved_printed_exponent_comparison {alpha : Real}
    (hα : 0 < alpha) (hαupper : alpha ≤ 332 / 333) :
    (1 / 2 : Real) ^ ((1 / alpha) ^ ((2 : Nat) ^ 61)) ≤
      (1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 53)) :=
  Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
    (section13_improved_printed_top_comparison hα hαupper)

end LeanProofs.GowersSzemeredi
