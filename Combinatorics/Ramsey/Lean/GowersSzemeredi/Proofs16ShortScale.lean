import GowersSzemeredi.Proofs16RadiusComparison

/-! # Rounding-safe short-cell scales for the product partition -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Above the singleton scale, the ceiling target fits both the quadratic
partition budget and the Bohr-frequency budget. -/
theorem section16_short_scale (s zeta : Real) (hs : 0 < s)
    (hz : 0 < zeta) (hzHalf : zeta ≤ 1 / 2)
    (hl : 1 < (zeta / 2) * Real.sqrt s) :
    ∃ v : Nat, 2 ≤ v ∧ (zeta / 2) * Real.sqrt s ≤ (v - 1 : Nat) ∧
      (v : Real) ^ 2 ≤ s ∧ 2 / s ≤ zeta / v := by
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
  have hr4 : 4 < Real.sqrt s := by linarith
  have hvsqrt : (v : Real) ≤ 3 * Real.sqrt s / 4 := by linarith
  have hvSq : (v : Real) ^ 2 ≤ s := by
    have hv2 := pow_le_pow_left₀ hvr.le hvsqrt 2
    nlinarith
  have hrs : 3 * Real.sqrt s ≤ s := by nlinarith
  have hbudget : 2 * (v : Real) ≤ zeta * s := by
    have hmul := mul_le_mul_of_nonneg_left hrs hz.le
    dsimp [l] at hv3
    nlinarith
  exact ⟨v, hvNat, hceil, hvSq, (div_le_div_iff₀ hs hvr).mpr hbudget⟩

/-- The Section 16 radius is at most one half, uniformly over its stated
parameter range. -/
theorem section16Zeta_pos_le_half {theta gamma : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    0 < section16Zeta theta gamma k ∧ section16Zeta theta gamma k ≤ 1 / 2 := by
  have hp : 0 < theta * gamma := mul_pos ht hg
  have hp1 : theta * gamma ≤ 1 := by nlinarith
  have hb : (1 : Real) ≤ 2 / (theta * gamma) := (le_div_iff₀ hp).mpr (by linarith)
  have hS : 1 ≤ multipleS theta gamma k := one_le_pow₀ hb
  constructor
  · unfold section16Zeta; positivity
  · unfold section16Zeta
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 2) (neg_le_neg hS)
    norm_num at h
    exact h

end LeanProofs.GowersSzemeredi
