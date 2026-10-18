import GowersSzemeredi.Proofs18LengthSixExponents
import GowersSzemeredi.Proofs18ExponentialProduct

/-! Elementary sums and powers of exponential bounds, shared by the generic
and length-six threshold arguments.

`const_le_exp_pow`, `natpow_le_exp_pow` and `rpow_le_exp_pow` are in
`Proofs18ExponentialCalculusSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem exp_pow_ge_two {X : Real} (hX : 2 ≤ X) (m : Nat) : 2 ≤ Real.exp (X ^ m) := by
  have h := one_le_pow_of_two_le hX m
  have := Real.add_one_le_exp (X ^ m)
  linarith only [h, this]

theorem exp_pow_mono {X : Real} {a b : Nat} (hX : 2 ≤ X) (hab : a ≤ b) :
    Real.exp (X ^ a) ≤ Real.exp (X ^ b) :=
  Real.exp_le_exp.mpr (pow_le_pow_right₀ (le_trans (by norm_num) hX) hab)

theorem exp_add_le {X a b : Real} {m : Nat} (hX : 2 ≤ X)
    (ha : a ≤ Real.exp (X ^ m)) (hb : b ≤ Real.exp (X ^ m)) : a + b ≤ Real.exp (X ^ (m + 1)) := by
  have h2 := exp_pow_ge_two hX m
  have hsq := exp_pow_sq_le hX m
  have : Real.exp (X ^ m) + Real.exp (X ^ m) ≤ Real.exp (X ^ m) * Real.exp (X ^ m) := by
    nlinarith only [h2]
  linarith only [ha, hb, this, hsq]

end LeanProofs.GowersSzemeredi
