import GowersSzemeredi.Proofs18FejerInverseThresholdEnvelope
import GowersSzemeredi.Sections17_18

/-! The certified cubic exponent is below Theorem 18.1's printed exponent.

The proved cubic inverse theorem certifies only
`1/e ≤ exp((2/α)^(2^61))` for its width exponent `e`
(`fejerCubicDiscrepancyExponent_inv_le_exp`). This module proves that the
certified lower bound `exp(−(2/α)^(2^61))` is strictly below
`section18Exponent α 3 = α^(2^(2^13))` for every `0 < α ≤ 1/2`. So the
certificate cannot give Theorem 18.1 at degree three; the status file
states this, and it is now kernel-checked.

This concerns the certified bound only. A sharper analysis of the same
proof could give a larger `e`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- `exp(−(2/α)^(2^61)) < α^(2^(2^13))` for `0 < α ≤ 1/2`. -/
theorem cubic_certified_exponent_lt_section18Exponent {alpha : Real}
    (ha : 0 < alpha) (ha1 : alpha ≤ 1 / 2) :
    Real.exp (-((2 / alpha) ^ ((2 : Nat) ^ 61))) < section18Exponent alpha 3 := by
  unfold section18Exponent
  set A : Nat := (2 : Nat) ^ ((2 : Nat) ^ (3 + 10)) with hAdef
  set B : Nat := (2 : Nat) ^ 61 with hBdef
  have hAB : A ≤ (2 : Nat) ^ B := by
    rw [hAdef, hBdef]
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hB1 : 1 ≤ B := Nat.one_le_two_pow
  set x : Real := 1 / alpha with hxdef
  have hx2 : 2 ≤ x := by rw [hxdef, le_div_iff₀ ha]; linarith
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  -- rewrite both sides as exponentials
  have hrhs : alpha ^ A = Real.exp (-((A : Real) * Real.log x)) := by
    have hlx : Real.log x = -Real.log alpha := by rw [hxdef, one_div, Real.log_inv]
    rw [hlx, mul_neg, neg_neg, ← Real.log_pow, Real.exp_log (pow_pos ha A)]
  rw [hrhs, Real.exp_lt_exp, neg_lt_neg_iff]
  -- `A log x < 2^B x ≤ (2x)^B = (2/α)^B`
  have hlog : Real.log x < x := by
    have := Real.log_le_sub_one_of_pos hx0
    linarith
  have hA : (A : Real) ≤ (2 : Real) ^ B := by exact_mod_cast hAB
  have hA0 : (0 : Real) < A := by exact_mod_cast Nat.pos_of_ne_zero (by rw [hAdef]; positivity)
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hxB : x ≤ x ^ B := le_self_pow₀ hx1 (by omega)
  have h2x : (2 / alpha) = 2 * x := by rw [hxdef]; ring
  rw [h2x, mul_pow]
  calc (A : Real) * Real.log x < (A : Real) * x := mul_lt_mul_of_pos_left hlog hA0
    _ ≤ (2 : Real) ^ B * x := mul_le_mul_of_nonneg_right hA hx0.le
    _ ≤ (2 : Real) ^ B * x ^ B := mul_le_mul_of_nonneg_left hxB (by positivity)

end LeanProofs.GowersSzemeredi
