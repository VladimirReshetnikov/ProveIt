import GowersSzemeredi.Section16

/-! The printed exponent of Corollary 16.11 does not follow from its proof.

The catalogue states Corollary 16.11 with the exponent its proof supplies,
`section16CorollaryExponent α k = (α/8)·c(r⁻¹α/8, α/2, k)^r` with
`r = 4α⁻²·s(α/4, α/2, k)`. The article instead prints `(α/2)^(2^(2^(k+9)))`.
This module proves that the supplied exponent is **strictly smaller** than
the printed one, for every `0 < α ≤ 1/2` and every `k`. So the printed
statement claims more than its proof gives, which is research notes Part
K.2 kernel-checked.

The reason is that the iteration parameter `r` is at least
`A = 2^(2^(k+8))`, the degree in `c`. Hence
`c^r ≤ (α/2)^(A·r) ≤ (α/2)^(A²) = (α/2)^(2^(2^(k+9)))`, and the extra factor
`α/8 < 1` makes it strict. This does not refute Corollary 16.11 with the
printed exponent; it shows only that the article's argument does not reach
it. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- `2^(k+8) ≤ 4 · 2^(2^(k+6))`. -/
theorem corollaryGap_exponent_nat (k : Nat) : 2 ^ (k + 8) ≤ 4 * 2 ^ (2 ^ (k + 6)) := by
  have h : k + 6 ≤ 2 ^ (k + 6) := (Nat.lt_two_pow_self).le
  calc 2 ^ (k + 8) = 4 * 2 ^ (k + 6) := by rw [show k + 8 = 2 + (k + 6) by omega, pow_add]; norm_num
    _ ≤ 4 * 2 ^ (2 ^ (k + 6)) := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right (by norm_num) h)

/-- The iteration parameter of Corollary 16.11 is at least the degree
`2^(2^(k+8))` of the control function `c`. -/
theorem section16CorollaryIteration_ge_degree {alpha : Real} (k : Nat)
    (ha : 0 < alpha) (ha1 : alpha ≤ 1 / 2) :
    (((2 : Nat) ^ ((2 : Nat) ^ (k + 8)) : Nat) : Real) ≤ section16CorollaryIteration alpha k := by
  have hS : (16 : Real) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6))) ≤ multipleS (alpha / 4) (alpha / 2) k := by
    unfold multipleS
    apply pow_le_pow_left₀ (by norm_num)
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hA : (((2 : Nat) ^ ((2 : Nat) ^ (k + 8)) : Nat) : Real) ≤
      (16 : Real) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6))) := by
    have hnat := corollaryGap_exponent_nat k
    calc (((2 : Nat) ^ ((2 : Nat) ^ (k + 8)) : Nat) : Real) = (2 : Real) ^ ((2 : Nat) ^ (k + 8)) := by
          push_cast; rfl
      _ ≤ (2 : Real) ^ (4 * 2 ^ (2 ^ (k + 6))) := pow_le_pow_right₀ (by norm_num) hnat
      _ = (16 : Real) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6))) := by
          rw [pow_mul]; norm_num
  have hinv : (1 : Real) ≤ alpha ^ (-(2 : Int)) := by
    rw [zpow_neg, zpow_ofNat]
    exact (one_le_inv₀ (by positivity)).mpr (pow_le_one₀ ha.le (by linarith))
  have hSpos : 0 ≤ multipleS (alpha / 4) (alpha / 2) k := by unfold multipleS; positivity
  unfold section16CorollaryIteration
  calc (((2 : Nat) ^ ((2 : Nat) ^ (k + 8)) : Nat) : Real) ≤ multipleS (alpha / 4) (alpha / 2) k := hA.trans hS
    _ ≤ 4 * alpha ^ (-(2 : Int)) * multipleS (alpha / 4) (alpha / 2) k := by
        have h4 : (1 : Real) ≤ 4 * alpha ^ (-(2 : Int)) := by linarith
        nlinarith

/-- **The supplied exponent of Corollary 16.11 is strictly below the printed
one.** -/
theorem section16CorollaryExponent_lt_printed {alpha : Real} (k : Nat)
    (ha : 0 < alpha) (ha1 : alpha ≤ 1 / 2) :
    section16CorollaryExponent alpha k < (alpha / 2) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 9))) := by
  set A : Nat := (2 : Nat) ^ ((2 : Nat) ^ (k + 8)) with hAdef
  set r := section16CorollaryIteration alpha k with hrdef
  have hAr : (A : Real) ≤ r := section16CorollaryIteration_ge_degree k ha ha1
  have hA1 : (1 : Real) ≤ A := by
    have : 1 ≤ A := Nat.one_le_two_pow
    exact_mod_cast this
  have hr1 : 1 ≤ r := hA1.trans hAr
  have hr0 : 0 < r := by linarith
  set x : Real := alpha / 2 * (r⁻¹ * (alpha / 8)) with hxdef
  have hx0 : 0 < x := by positivity
  have hx : x ≤ alpha / 2 := by
    have h1 : r⁻¹ * (alpha / 8) ≤ 1 := by
      have : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr1
      nlinarith
    calc x = alpha / 2 * (r⁻¹ * (alpha / 8)) := rfl
      _ ≤ alpha / 2 * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = alpha / 2 := mul_one _
  have hb0 : 0 < alpha / 2 := by positivity
  have hb1 : alpha / 2 ≤ 1 := by linarith
  -- the exponent `A^2` is the printed degree
  have hdeg : ((A : Real) * A) = (((2 : Nat) ^ ((2 : Nat) ^ (k + 9)) : Nat) : Real) := by
    have h : A * A = (2 : Nat) ^ ((2 : Nat) ^ (k + 9)) := by
      rw [hAdef, ← pow_add]
      congr 1
      rw [show k + 9 = (k + 8) + 1 by omega, pow_succ]
      ring
    exact_mod_cast h
  have hc : multipleC (r⁻¹ * (alpha / 8)) (alpha / 2) k = x ^ A := by
    unfold multipleC
    rfl
  have hpow : (x ^ A) ^ r = x ^ ((A : Real) * r) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
  have hY : 0 < (alpha / 2) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 9))) := by positivity
  have hmain : x ^ ((A : Real) * r) ≤ (alpha / 2) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 9))) := by
    calc x ^ ((A : Real) * r) ≤ (alpha / 2) ^ ((A : Real) * r) :=
          Real.rpow_le_rpow hx0.le hx (by positivity)
      _ ≤ (alpha / 2) ^ ((A : Real) * A) :=
          Real.rpow_le_rpow_of_exponent_ge hb0 hb1
            (mul_le_mul_of_nonneg_left hAr (by positivity))
      _ = (alpha / 2) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 9))) := by
          rw [hdeg, Real.rpow_natCast]
  have hE : section16CorollaryExponent alpha k = alpha / 8 * x ^ ((A : Real) * r) := by
    unfold section16CorollaryExponent
    simp only
    rw [← hrdef, hc, hpow]
  rw [hE]
  have h8 : alpha / 8 < 1 := by linarith
  calc alpha / 8 * x ^ ((A : Real) * r) ≤ alpha / 8 * (alpha / 2) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 9))) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ < 1 * (alpha / 2) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 9))) :=
        mul_lt_mul_of_pos_right h8 hY
    _ = _ := one_mul _

end LeanProofs.GowersSzemeredi
