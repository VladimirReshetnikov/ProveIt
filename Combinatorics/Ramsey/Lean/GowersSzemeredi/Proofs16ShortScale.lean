import GowersSzemeredi.Section16
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Rounding-safe short-cell scales for the product partition

`section16Zeta_pos_le_half` is in `Proofs16ShortScaleSide`, outside the final
route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Above the singleton scale, ceiling rounding leaves a full unit of
slack in the quadratic budget. This covers the length-minus-one requirement
for changing the common difference of the final axis. -/
theorem section16_short_scale_margin (s zeta : Real) (hs : 0 < s)
    (hz : 0 < zeta) (hzHalf : zeta ≤ 1 / 2)
    (hl : 1 < (zeta / 2) * Real.sqrt s) :
    ∃ v : Nat, 2 ≤ v ∧ (zeta / 2) * Real.sqrt s ≤ (v - 1 : Nat) ∧
      (v : Real) ^ 2 + 1 ≤ s ∧ 2 / s ≤ zeta / v := by
  let l := (zeta / 2) * Real.sqrt s
  let v := Nat.ceil l + 1
  change 1 < l at hl
  have hl0 : 0 < l := by dsimp [l]; positivity
  have hvNat : 2 ≤ v := by
    have hc : 0 < Nat.ceil l := Nat.ceil_pos.mpr hl0
    omega
  have hvr : (0 : Real) < v := by exact_mod_cast (show 0 < v by omega)
  have hceil : l ≤ (v - 1 : Nat) := by simpa only [v, Nat.add_sub_cancel] using Nat.le_ceil l
  have hvle : (v : Real) ≤ l + 2 := by
    have hc := (Nat.ceil_lt_add_one hl0.le).le
    dsimp [v]
    push_cast
    linarith
  have hv3 : (v : Real) ≤ 3 * l := by linarith
  have hr : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  have hrSq : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt hs.le
  have hlr : l ≤ Real.sqrt s / 4 := by
    dsimp [l]
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 / 2 - zeta) hr]
  have hvsqrt : (v : Real) ≤ 3 * Real.sqrt s / 4 := by linarith
  have hvSq : (v : Real) ^ 2 + 1 ≤ s := by
    have hv2 := pow_le_pow_left₀ hvr.le hvsqrt 2
    nlinarith
  have hrs : 3 * Real.sqrt s ≤ s := by nlinarith
  have hbudget : 2 * (v : Real) ≤ zeta * s := by
    have hmul := mul_le_mul_of_nonneg_left hrs hz.le
    dsimp [l] at hv3
    nlinarith
  exact ⟨v, hvNat, hceil, hvSq, (div_le_div_iff₀ hs hvr).mpr hbudget⟩

end LeanProofs.GowersSzemeredi
