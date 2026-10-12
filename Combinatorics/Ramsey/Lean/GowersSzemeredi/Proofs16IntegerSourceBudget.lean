import GowersSzemeredi.Proofs16IntegerSourceWidth
import GowersSzemeredi.Proofs16Lemma6Parameters

/-! The source's allowed graph budget in Lemma 16.6 is large enough
to absorb the explicit polynomial integer-recurrence profile. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The source iteration parameter has uniform room even at unit densities. -/
theorem section16T_sixteen_le {delta theta1 : Real} (k : Nat)
    (hd : 0 < delta) (hd1 : delta ≤ 1) (ht : 0 < theta1) (ht1 : theta1 ≤ 1) :
    16 ≤ section16T delta theta1 k := by
  have hinv : 1 ≤ delta ^ (-(2 : Int)) := by
    rw [zpow_neg, zpow_ofNat]
    exact (one_le_inv₀ (pow_pos hd 2)).mpr (pow_le_one₀ hd.le hd1)
  have hprod : 0 < theta1 / 8 * delta := by positivity
  have hprod1 : theta1 / 8 * delta ≤ 1 / 8 := by
    have h := mul_le_mul_of_nonneg_left hd1 (by positivity : 0 ≤ theta1 / 8)
    nlinarith
  have hbase : (16 : Real) ≤ 2 / (theta1 / 8 * delta) :=
    (le_div_iff₀ hprod).mpr (by linarith)
  have hS : 16 ≤ multipleS (theta1 / 8) delta k :=
    hbase.trans (le_self_pow₀ (by linarith) (by positivity))
  unfold section16T
  exact hS.trans (le_mul_of_one_le_left (by linarith) hinv)

/-- The allowed graph count is at least the dimension's full dyadic tower. -/
theorem section16Lemma6QBound_tower_lower {delta theta1 sigma : Real} (k : Nat)
    (hd : 0 < delta) (hd1 : delta ≤ 1) (ht : 0 < theta1) (ht1 : theta1 ≤ 1)
    (hs : 0 < sigma) (hs1 : sigma ≤ 1) :
    (2 : Real) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 8))) ≤
      section16Lemma6QBound sigma delta theta1 k := by
  let t := section16T delta theta1 k
  have ht16 : 16 ≤ t := section16T_sixteen_le k hd hd1 ht ht1
  have ht0 : 0 < t := by linarith
  have hfrac : 0 < sigma / t := div_pos hs ht0
  have hfracHalf : sigma / t ≤ 1 / 2 := (div_le_iff₀ ht0).mpr (by linarith)
  have hb : 0 < delta * (sigma / t) := mul_pos hd hfrac
  have hbHalf : delta * (sigma / t) ≤ 1 / 2 :=
    (mul_le_of_le_one_left hfrac.le hd1).trans hfracHalf
  have hinv : 2 ≤ (delta * (sigma / t))⁻¹ := by
    have h := (inv_le_inv₀ (by norm_num : (0 : Real) < 1 / 2) hb).mpr hbHalf
    norm_num at h
    exact h
  have hQ : (2 : Real) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 8))) ≤ multipleQ (sigma / t) delta k := by
    unfold multipleQ multipleC
    rw [← inv_pow]
    exact pow_le_pow_left₀ (by norm_num) hinv _
  have hQ1 : 1 ≤ multipleQ (sigma / t) delta k := (one_le_pow₀ (by norm_num)).trans hQ
  exact hQ.trans (Real.self_le_rpow_of_one_le hQ1 (by linarith))

/-- The floor of the source budget dominates both explicit profile constants. -/
theorem section16Lemma6QBound_floor_profile {C p : Nat} {delta theta1 sigma : Real} (k : Nat)
    (hconst : (C : Real) + p ≤ (2 : Real) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    (hd : 0 < delta) (hd1 : delta ≤ 1) (ht : 0 < theta1) (ht1 : theta1 ≤ 1)
    (hs : 0 < sigma) (hs1 : sigma ≤ 1) :
    C ≤ ⌊section16Lemma6QBound sigma delta theta1 k⌋₊ ∧
      p ≤ ⌊section16Lemma6QBound sigma delta theta1 k⌋₊ := by
  have hbudget := section16Lemma6QBound_tower_lower k hd hd1 ht ht1 hs hs1
  have hmono : (2 : Real) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))) ≤
      (2 : Real) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 8))) := by
    apply pow_le_pow_right₀ (by norm_num)
    exact Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hsum := hconst.trans (hmono.trans hbudget)
  constructor
  · apply Nat.le_floor
    have := Nat.cast_nonneg (α := Real) p
    linarith
  · apply Nat.le_floor
    have := Nat.cast_nonneg (α := Real) C
    linarith

end LeanProofs.GowersSzemeredi
