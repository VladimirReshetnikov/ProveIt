import GowersSzemeredi.Proofs18ExponentialCalculus

/-! Declarations of `Proofs18ExponentialCalculus` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- `b^e ≤ exp(X^(m+k))` for `1 ≤ b ≤ exp(X^m)` and `0 ≤ e ≤ X^k`. -/
theorem rpow_le_exp_pow {X b e : Real} {m k : Nat} (hX : 2 ≤ X) (hb1 : 1 ≤ b)
    (hb : b ≤ Real.exp (X ^ m)) (he0 : 0 ≤ e) (he : e ≤ X ^ k) :
    b ^ e ≤ Real.exp (X ^ (m + k)) := by
  have hX0 : 0 ≤ X := le_trans (by norm_num) hX
  rw [Real.rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hb1)]
  apply Real.exp_le_exp.mpr
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
