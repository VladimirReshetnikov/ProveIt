import GowersSzemeredi.Proofs18GenericEnvelopeBase

/-! **The η and `yIn` steps with a polynomial side condition** (Notes L.16j).

`GenParams.eta_step` and `GenParams.yIn_step` ask for `fixDeg k ≤ m`, with
`fixDeg k = 2^(k+5) + 7`. They use it only to absorb
`2^(2(k+2)³)·2^(k+1)·(2/α)²` and `2·(2(k+3))^(k+3)` into `(2/α)^(2^m)`, and
`m ≥ 3(k+4)²` already suffices (`cube_le_two_pow_sq`). At the class constant
`4` the density degree is about `28·2^k < 32·2^k`, so the printed side
condition would raise one step from `28·2^k` to `32·2^k`. The envelope would
then tend to `64·2^k` and lose `d + 4`. The copies below (generated, proofs
verbatim up to the budget lemma) remove that floor. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The constants of the η and `yIn` steps fit `2^(3(k+4)²)`. -/
theorem cube_le_two_pow_sq (k : Nat) : 2 * (k + 2) ^ 3 + k + 3 ≤ 2 ^ (3 * (k + 4) ^ 2) ∧
    2 * (2 * (k + 3)) ^ (k + 3) ≤ 2 ^ (3 * (k + 4) ^ 2) := by
  constructor
  · have h1 : (k + 2) ^ 3 ≤ (2 ^ (k + 2)) ^ 3 := Nat.pow_le_pow_left Nat.lt_two_pow_self.le 3
    have h2 : (2 ^ (k + 2)) ^ 3 = 2 ^ (3 * k + 6) := by rw [← pow_mul]; ring_nf
    have h3 : k + 3 ≤ 2 ^ (3 * k + 6) :=
      (Nat.lt_two_pow_self (n := k + 3)).le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h4 : 2 ^ (3 * k + 8) = 4 * 2 ^ (3 * k + 6) := by
      rw [show 3 * k + 8 = (3 * k + 6) + 2 by ring, pow_add]; ring
    have h5 : 2 ^ (3 * k + 8) ≤ 2 ^ (3 * (k + 4) ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    omega
  · have hk3 : 2 * (k + 3) ≤ 2 ^ (k + 3) := by
      have := Nat.lt_two_pow_self (n := k + 2); rw [pow_succ]; omega
    calc 2 * (2 * (k + 3)) ^ (k + 3) ≤ 2 * (2 ^ (k + 3)) ^ (k + 3) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hk3 _)
      _ = 2 ^ ((k + 3) * (k + 3) + 1) := by rw [← pow_mul, pow_succ]; ring
      _ ≤ 2 ^ (3 * (k + 4) ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

namespace GenParams

/-- `η` from the single-piece density. -/
theorem eta_step_small {alpha d : Real} {k m : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (hd0 : 0 < d) (hd1 : d ≤ 1) (hdi : d⁻¹ ≤ (2 / alpha) ^ (2 ^ m)) (hm : 3 * (k + 4) ^ 2 ≤ m) :
    0 < (2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)) * (d / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4) ∧
      (2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)) * (d / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4) ≤
        alpha / 8 ∧
      ((2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)) * (d / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4))⁻¹ ≤
        (2 / alpha) ^ (2 ^ (m + 1)) := by
  have hX := two_div_ge_two ha ha2
  have hX1 : (1 : Real) ≤ 2 / alpha := by linarith
  have hz : ((2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)))⁻¹ = 2 ^ (2 * (k + 2) ^ 3) := by
    rw [zpow_neg, inv_inv, show (2 * ((k + 1) + 1) ^ 3 : Int) = ((2 * (k + 2) ^ 3 : Nat) : Int) by
      push_cast; ring, zpow_natCast]
  have hz0 : 0 < (2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)) := zpow_pos (by norm_num) _
  have hz1 : (2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num) (neg_nonpos.mpr (by positivity))
  have h2k : (2 : Real) ≤ 2 ^ (k + 1) := by
    calc (2 : Real) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hin0 : 0 < d / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4 :=
    div_pos (mul_pos (div_pos hd0 (by positivity)) (pow_pos ha 2)) (by norm_num)
  refine ⟨mul_pos hz0 hin0, ?_, ?_⟩
  · have h1 : d / (2 : Real) ^ (k + 1) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have h2 : alpha ^ 2 ≤ alpha / 2 := by nlinarith
    have h3 : d / (2 : Real) ^ (k + 1) * alpha ^ 2 ≤ 1 / 2 * (alpha / 2) :=
      mul_le_mul h1 h2 (by positivity) (by norm_num)
    have h4 : d / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4 ≤ alpha / 8 := by linarith
    calc (2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)) * (d / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4)
        ≤ 1 * (alpha / 8) := mul_le_mul hz1 h4 hin0.le zero_le_one
      _ = alpha / 8 := one_mul _
  · rw [mul_inv, hz]
    have hval : (d / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4)⁻¹ =
        (2 : Real) ^ (k + 1) * (2 / alpha) ^ 2 * d⁻¹ := by
      field_simp; ring
    rw [hval]
    have hcube := (cube_le_two_pow_sq k).1
    have hc : (2 : Real) ^ (2 * (k + 2) ^ 3) * ((2 : Real) ^ (k + 1) * (2 / alpha) ^ 2) ≤
        (2 / alpha) ^ (2 ^ m) := by
      have h1 : (2 : Real) ^ (2 * (k + 2) ^ 3) * (2 : Real) ^ (k + 1) ≤
          (2 / alpha) ^ (2 * (k + 2) ^ 3) * (2 / alpha) ^ (k + 1) :=
        mul_le_mul (pow_le_pow_left₀ (by norm_num) hX _) (pow_le_pow_left₀ (by norm_num) hX _)
          (by positivity) (by positivity)
      have hfix : 2 ^ (3 * (k + 4) ^ 2) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      calc (2 : Real) ^ (2 * (k + 2) ^ 3) * ((2 : Real) ^ (k + 1) * (2 / alpha) ^ 2)
          = (2 : Real) ^ (2 * (k + 2) ^ 3) * (2 : Real) ^ (k + 1) * (2 / alpha) ^ 2 := by ring
        _ ≤ (2 / alpha) ^ (2 * (k + 2) ^ 3) * (2 / alpha) ^ (k + 1) * (2 / alpha) ^ 2 :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (2 / alpha) ^ (2 * (k + 2) ^ 3 + k + 3) := by rw [← pow_add, ← pow_add]; ring_nf
        _ ≤ (2 / alpha) ^ (2 ^ m) := pow_le_pow_right₀ hX1 (by omega)
    calc (2 : Real) ^ (2 * (k + 2) ^ 3) * ((2 : Real) ^ (k + 1) * (2 / alpha) ^ 2 * d⁻¹)
        = (2 : Real) ^ (2 * (k + 2) ^ 3) * ((2 : Real) ^ (k + 1) * (2 / alpha) ^ 2) * d⁻¹ := by ring
      _ ≤ (2 / alpha) ^ (2 ^ (m + 1)) := pw_mul hX (by positivity) (inv_pos.mpr hd0).le hc hdi

/-- `yIn` from `η`. -/
theorem yIn_step_small {alpha e : Real} {k m : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (he0 : 0 < e) (he8 : e ≤ alpha / 8) (hei : e⁻¹ ≤ (2 / alpha) ^ (2 ^ m)) (hm : 3 * (k + 4) ^ 2 ≤ m) :
    0 < (e / 2) / (2 * (k + 1 + 2 : Nat) : Real) ^ (k + 1 + 2) ∧
      (e / 2) / (2 * (k + 1 + 2 : Nat) : Real) ^ (k + 1 + 2) ≤ alpha ∧
      ((e / 2) / (2 * (k + 1 + 2 : Nat) : Real) ^ (k + 1 + 2))⁻¹ ≤ (2 / alpha) ^ (2 ^ (m + 1)) := by
  have hX := two_div_ge_two ha ha2
  have hden1 : (1 : Real) ≤ (2 * (k + 1 + 2 : Nat) : Real) ^ (k + 1 + 2) :=
    one_le_pow₀ (by push_cast; linarith)
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    have : e / 2 ≤ alpha := by linarith
    nlinarith
  · rw [inv_div]
    have hc : 2 * (2 * (k + 1 + 2 : Nat) : Real) ^ (k + 1 + 2) ≤ (2 / alpha) ^ (2 ^ m) := by
      have hnat : (2 * (2 * (k + 1 + 2 : Nat)) ^ (k + 1 + 2) : Nat) ≤ 2 ^ (2 ^ m) := by
        have h1 : 2 * (2 * (k + 3)) ^ (k + 3) ≤ 2 ^ (3 * (k + 4) ^ 2) := (cube_le_two_pow_sq k).2
        have h2 : 2 ^ (3 * (k + 4) ^ 2) ≤ 2 ^ (2 ^ m) :=
          Nat.pow_le_pow_right (by norm_num) (by have := Nat.lt_two_pow_self (n := m); omega)
        rw [show k + 1 + 2 = k + 3 by ring]
        omega
      refine pw_const hX ?_
      exact_mod_cast hnat
    calc (2 * (k + 1 + 2 : Nat) : Real) ^ (k + 1 + 2) / (e / 2)
        = 2 * (2 * (k + 1 + 2 : Nat) : Real) ^ (k + 1 + 2) * e⁻¹ := by
          rw [div_eq_mul_inv, inv_div]; ring
      _ ≤ (2 / alpha) ^ (2 ^ (m + 1)) := pw_mul hX (by positivity) (inv_pos.mpr he0).le hc hei

end GenParams

end LeanProofs.GowersSzemeredi
