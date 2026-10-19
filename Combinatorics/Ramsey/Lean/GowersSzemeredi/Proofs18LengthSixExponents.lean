import GowersSzemeredi.Proofs18LengthSixDensity
import GowersSzemeredi.Proofs13ThresholdExponentialEnvelope

/-! Power bounds for exponents: `capped_inv_le_pow` for the capped width exponent,
`cubicBaseExponent_inv_le`, `section16Delta_inv_le_pw`, and the helpers
`one_le_pow_of_two_le` and `le_exp_pow_of_le_pow`.

The exponents of the length-six route (the spectrum count, the capped family
exponent and the width exponents `sixEb`) are in
`Proofs18LengthSixExponentsSide`, outside the final route. -/
set_option autoImplicit false
set_option exponentiation.threshold 1024
noncomputable section
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-! ### The calculus -/

theorem one_le_pow_of_two_le {w : Real} (hw : 2 ≤ w) (n : Nat) : 1 ≤ w ^ n :=
  one_le_pow₀ (le_trans (by norm_num) hw)

theorem le_exp_pow_of_le_pow {w x : Real} {n : Nat} (hx : x ≤ w ^ n) : x ≤ Real.exp (w ^ n) :=
  hx.trans ((Real.add_one_le_exp _).trans' (by linarith only))

/-- The capped width exponent `min e (log 2 / log (max 2 T))`. -/
theorem capped_inv_le_pow {e T w : Real} {r n : Nat} (hw : 2 ≤ w) (he : 0 < e)
    (hei : e⁻¹ ≤ w ^ r) (hT : T ≤ Real.exp (w ^ n)) (hrn : n + 1 ≤ r) :
    (section16CappedWidthExponent e T)⁻¹ ≤ w ^ r := by
  have hw0 : 0 ≤ w := le_trans (by norm_num) hw
  have hn1 := one_le_pow_of_two_le hw n
  have hL : Real.log (max 2 T) ≤ w ^ n := by
    rw [Real.log_le_iff_le_exp (lt_of_lt_of_le (by norm_num) (le_max_left _ _))]
    refine max_le ?_ hT
    calc (2 : Real) ≤ w ^ n + 1 := by linarith only [hn1]
      _ ≤ Real.exp (w ^ n) := Real.add_one_le_exp _
  have hlog2 : (1 : Real) / 2 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith only [this]
  unfold section16CappedWidthExponent
  rcases min_choice e (Real.log 2 / Real.log (max 2 T)) with h | h
  · rw [h]; exact hei
  · rw [h, inv_div]
    calc Real.log (max 2 T) / Real.log 2 ≤ w ^ n / (1 / 2) :=
          div_le_div₀ (pow_nonneg hw0 _) hL (by norm_num) hlog2
      _ = 2 * w ^ n := by ring
      _ ≤ w * w ^ n := mul_le_mul_of_nonneg_right hw (pow_nonneg hw0 _)
      _ = w ^ (n + 1) := (pow_succ' w n).symm
      _ ≤ w ^ r := pow_le_pow_right₀ (le_trans (by norm_num) hw) hrn

/-- `cubicBaseExponent q s = 2^(-27) s³ / q⁴` has `(·)⁻¹ ≤ w^(27 + 3b + 4a)`. -/
theorem cubicBaseExponent_inv_le {q : Nat} {s w : Real} {a b : Nat} (hw : 2 ≤ w) (hq : 0 < q)
    (hqw : (q : Real) ≤ w ^ a) (hs : 0 < s) (hsw : s⁻¹ ≤ w ^ b) :
    (cubicBaseExponent q s)⁻¹ ≤ w ^ (27 + b * 3 + a * 4) := by
  have hw0 : 0 ≤ w := le_trans (by norm_num) hw
  have hq0 : (0 : Real) < q := by exact_mod_cast hq
  have hval : (cubicBaseExponent q s)⁻¹ = (2 : Real) ^ 27 * s⁻¹ ^ 3 * (q : Real) ^ 4 := by
    unfold cubicBaseExponent
    rw [show (-(27 : Real)) = -((27 : Nat) : Real) by norm_num, Real.rpow_neg (by norm_num),
      Real.rpow_natCast]
    field_simp
  rw [hval, pow_add, pow_add, pow_mul, pow_mul]
  have h27 : (2 : Real) ^ 27 ≤ w ^ 27 := pow_le_pow_left₀ (by norm_num) hw 27
  exact mul_le_mul (mul_le_mul h27 (pow_le_pow_left₀ (inv_pos.mpr hs).le hsw 3)
      (pow_nonneg (inv_pos.mpr hs).le _) (pow_nonneg hw0 _))
    (pow_le_pow_left₀ hq0.le hqw 4) (pow_nonneg hq0.le _)
    (mul_nonneg (pow_nonneg hw0 _) (pow_nonneg (pow_nonneg hw0 _) _))

/-- The fixed density loss has a polynomial reciprocal bound. -/
theorem section16Delta_inv_le_pw {t u : Real} {a : Nat} (hu : 2 ≤ u) (ha : 5 ≤ a)
    (ht : 0 < t) (ht1 : t ≤ 1) (hi : t⁻¹ ≤ u ^ (2 ^ a)) :
    (section16Delta t)⁻¹ ≤ u ^ (2 ^ (a + 3)) := by
  have h4t : 4 / t ≤ u ^ (2 ^ a + 2) := by
    rw [div_eq_mul_inv, pow_add, mul_comm]
    exact mul_le_mul hi (by nlinarith only [hu]) (by norm_num) (by positivity)
  have h6 : (4 / t) ^ ((11 : Real) / 2) ≤ (u ^ (2 ^ a + 2)) ^ 6 := by
    have h1 : (1 : Real) ≤ 4 / t := by rw [le_div_iff₀ ht]; linarith
    refine (Real.rpow_le_rpow_of_exponent_le h1 (by norm_num : (11 : Real) / 2 ≤ 6)).trans ?_
    rw [Real.rpow_ofNat]
    gcongr
  unfold section16Delta
  rw [mul_inv, Real.rpow_neg (by norm_num), inv_inv,
    ← Real.inv_rpow (div_nonneg ht.le (by norm_num)), inv_div, Real.rpow_ofNat]
  calc _ ≤ u ^ 37 * (u ^ (2 ^ a + 2)) ^ 6 := by gcongr
    _ = u ^ (37 + (2 ^ a + 2) * 6) := by rw [← pow_mul, ← pow_add]
    _ ≤ u ^ (2 ^ (a + 3)) := pow_le_pow_right₀ (by linarith) (by
        have := Nat.pow_le_pow_right two_pos ha; rw [pow_add]; omega)

end LeanProofs.GowersSzemeredi
