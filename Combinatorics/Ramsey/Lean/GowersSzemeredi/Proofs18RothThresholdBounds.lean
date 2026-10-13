import GowersSzemeredi.Proofs18DoubleExponentialBounds

/-! The numerical comparison shared by the short-length Roth thresholds. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Roth's explicit double exponential fits every source tower with top exponent at least three. -/
theorem roth_exp_exp_le_two_tower {u : Real} {n : Nat} (hu : 2 ≤ u) (hn : 3 ≤ n) :
    Real.exp (Real.exp (1000000000000 * u)) ≤
      (2 : Real) ^ ((2 : Real) ^ (u ^ ((2 : Real) ^ ((2 : Real) ^ n)))) := by
  have hu0 : 0 ≤ u := le_trans (by norm_num) hu
  have hC : (1000000000000 : Real) ≤ u ^ (40 : Nat) :=
    (show (1000000000000 : Real) ≤ (2 : Real) ^ (40 : Nat) by norm_num).trans
      (pow_le_pow_left₀ (by norm_num) hu 40)
  have hlinear : 1000000000000 * u ≤ u ^ (41 : Nat) := by
    calc
      _ ≤ u ^ (40 : Nat) * u := mul_le_mul_of_nonneg_right hC hu0
      _ = _ := (pow_succ u 40).symm
  have hE : 41 + 2 ≤ (2 : Nat) ^ (2 ^ n) :=
    (show 41 + 2 ≤ (2 : Nat) ^ (2 ^ 3) by norm_num).trans
      (Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn))
  have h := (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hlinear)).trans
    (exp_exp_pow_le_two_rpow_two_rpow hu hE)
  simpa only [← Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat] using h

end LeanProofs.GowersSzemeredi
