import GowersSzemeredi.Proofs18LengthSixExponents
import GowersSzemeredi.Proofs18ExponentialProduct

/-! Elementary sums and powers of exponential bounds, shared by the generic
and length-six threshold arguments. -/
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

/-- `b^e ≤ exp(X^(m+k))` for `1 ≤ b ≤ exp(X^m)` and `0 ≤ e ≤ X^k`. -/
theorem rpow_le_exp_pow {X b e : Real} {m k : Nat} (hX : 2 ≤ X) (hb1 : 1 ≤ b)
    (hb : b ≤ Real.exp (X ^ m)) (he0 : 0 ≤ e) (he : e ≤ X ^ k) :
    b ^ e ≤ Real.exp (X ^ (m + k)) := by
  have hX0 : 0 ≤ X := le_trans (by norm_num) hX
  rw [Real.rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hb1)]
  apply Real.exp_le_exp.mpr
  have hl0 : 0 ≤ Real.log b := Real.log_nonneg hb1
  have hl : Real.log b ≤ X ^ m :=
    (Real.log_le_iff_le_exp (lt_of_lt_of_le zero_lt_one hb1)).mpr hb
  rw [pow_add]
  exact mul_le_mul hl he he0 (pow_nonneg hX0 _)

/-- A constant `c ≤ 2^j` is below `exp(X^j)`. -/
theorem const_le_exp_pow {X c : Real} {j : Nat} (hX : 2 ≤ X) (hc : c ≤ 2 ^ j) :
    c ≤ Real.exp (X ^ j) :=
  le_exp_pow_of_le_pow (const_le_pow hX hc)

/-- A natural power `b^n ≤ exp(X^(m+k))` for `1 ≤ b ≤ exp(X^m)` and `n ≤ X^k`. -/
theorem natpow_le_exp_pow {X b : Real} {n m k : Nat} (hX : 2 ≤ X) (hb1 : 1 ≤ b)
    (hb : b ≤ Real.exp (X ^ m)) (hn : (n : Real) ≤ X ^ k) : b ^ n ≤ Real.exp (X ^ (m + k)) := by
  rw [← Real.rpow_natCast]
  exact rpow_le_exp_pow hX hb1 hb (Nat.cast_nonneg _) hn

end LeanProofs.GowersSzemeredi
