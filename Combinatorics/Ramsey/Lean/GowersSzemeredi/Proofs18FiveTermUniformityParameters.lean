import GowersSzemeredi.Proofs18GeneralIteration

/-! Polynomial substitution bounds for the five-term interval uniformity parameter. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem intervalUniformityParameter_five_le_density_power {delta : Real}
    (hδ : 0 ≤ delta) (hδone : delta ≤ 1) : intervalUniformityParameter delta 5 ≤ delta ^ 5 := by
  let a := delta ^ 5 / 64000
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have haδ : a ≤ delta ^ 5 := div_le_self (pow_nonneg hδ _) (by norm_num)
  have ha1 : a ≤ 1 := haδ.trans (pow_le_one₀ hδ hδone)
  norm_num only [intervalUniformityParameter, Nat.cast_ofNat, Nat.reduceSub, Nat.reducePow, show (512 : Real) * 5 ^ (3 : Nat) = 64000 by norm_num]
  change a ^ (16 : Nat) ≤ _
  calc
    _ = a ^ (15 : Nat) * a := pow_succ _ _
    _ ≤ 1 * a := mul_le_mul_of_nonneg_right (pow_le_one₀ ha ha1) ha
    _ = a := one_mul _
    _ ≤ _ := haδ

theorem two_div_intervalUniformityParameter_five_le_power {delta : Real}
    (hδ : 0 < delta) (hδone : delta ≤ 1) :
    2 / intervalUniformityParameter delta 5 ≤ (2 / delta) ^ (512 : Nat) := by
  let x := 2 / delta
  have hx : 2 ≤ x := (le_div_iff₀ hδ).mpr (by linarith only [hδone])
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hi : delta⁻¹ ≤ x := by
    simpa only [one_div] using div_le_div_of_nonneg_right (by norm_num : (1 : Real) ≤ 2) hδ.le
  have hc : (64000 : Real) ≤ x ^ (16 : Nat) :=
    (by norm_num : (64000 : Real) ≤ (2 : Real) ^ (16 : Nat)).trans (pow_le_pow_left₀ (by norm_num) hx _)
  have hbase : 64000 / delta ^ (5 : Nat) ≤ x ^ (21 : Nat) := by
    rw [div_eq_mul_inv, ← inv_pow]
    calc
      _ ≤ x ^ (16 : Nat) * x ^ (5 : Nat) := mul_le_mul hc
        (pow_le_pow_left₀ (inv_nonneg.mpr hδ.le) hi _) (by positivity) (by positivity)
      _ = _ := (pow_add _ _ _).symm
  norm_num only [intervalUniformityParameter, Nat.cast_ofNat, Nat.reduceSub, Nat.reducePow, show (512 : Real) * 5 ^ (3 : Nat) = 64000 by norm_num]
  rw [div_eq_mul_inv, ← inv_pow, inv_div]
  calc
    _ ≤ x * (x ^ (21 : Nat)) ^ (16 : Nat) := mul_le_mul hx
      (pow_le_pow_left₀ (by positivity) hbase 16) (by positivity) (by positivity)
    _ = x ^ (337 : Nat) := by rw [← pow_mul, ← pow_succ']
    _ ≤ _ := pow_le_pow_right₀ hx1 (by norm_num)

end LeanProofs.GowersSzemeredi
