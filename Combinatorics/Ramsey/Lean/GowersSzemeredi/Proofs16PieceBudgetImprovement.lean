import GowersSzemeredi.Proofs16JointPowerProfile

/-! Quantitative comparison of the retained common-base extraction count
with the older source-sized refinement count, including integer rounding. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A closed formula displays the smaller density exponent in the actual
piece bound. No positivity or nonzero convention is hidden in the identity. -/
theorem section16CommonBasePieceBound_eq (theta gamma : Real) (k : Nat) :
    section16CommonBasePieceBound theta gamma k =
      (2 : Real) ^ (32 : Nat) * gamma ^ (-(2 : Int)) *
        (4 / (theta * gamma)) ^ (8 * (2 : Nat) ^ ((2 : Nat) ^ (k + 5))) := by
  unfold section16CommonBasePieceBound section16ThetaTwo section16ThetaOne
  rw [Real.rpow_neg (by norm_num : (0 : Real) ≤ 2), Real.rpow_ofNat]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, inv_pow, mul_pow, ← pow_mul]
  ring

/-- The new real budget is at least one on the admissible parameter range. -/
theorem section16CommonBasePieceBound_one_le {theta gamma : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    1 ≤ section16CommonBasePieceBound theta gamma k := by
  rw [section16CommonBasePieceBound_eq]
  have htg : 0 < theta * gamma := mul_pos ht hg
  have htg1 : theta * gamma ≤ 1 := mul_le_one₀ ht1 hg.le hg1
  have hb : (1 : Real) ≤ 4 / (theta * gamma) := (le_div_iff₀ htg).mpr (by linarith)
  have hgamma : 1 ≤ gamma ^ (-(2 : Int)) := by
    rw [zpow_neg, zpow_ofNat]
    exact (one_le_inv₀ (pow_pos hg 2)).mpr (pow_le_one₀ hg.le hg1)
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (by norm_num) hgamma) (one_le_pow₀ hb)

/-- Advancing the source dimension grows its iteration budget by at least
a factor of two, without evaluating the tower exponents. -/
theorem multipleS_two_mul_le_succ {theta gamma : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    2 * multipleS theta gamma k ≤ multipleS theta gamma (k + 1) := by
  have htg : 0 < theta * gamma := mul_pos ht hg
  have htg1 : theta * gamma ≤ 1 := mul_le_one₀ ht1 hg.le hg1
  have hb : (2 : Real) ≤ 2 / (theta * gamma) := (le_div_iff₀ htg).mpr (by linarith)
  have hb1 : (1 : Real) ≤ 2 / (theta * gamma) := (by norm_num : (1 : Real) ≤ 2).trans hb
  have hexp : (2 : Nat) ^ ((2 : Nat) ^ (k + 6)) + 1 ≤
      (2 : Nat) ^ ((2 : Nat) ^ (k + 1 + 6)) := by
    apply Nat.succ_le_of_lt
    apply Nat.pow_lt_pow_right (by norm_num : 1 < 2)
    apply Nat.pow_lt_pow_right (by norm_num : 1 < 2)
    omega
  unfold multipleS
  calc
    _ ≤ (2 / (theta * gamma)) * (2 / (theta * gamma)) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6))) :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    _ = (2 / (theta * gamma)) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6)) + 1) := by rw [pow_succ]; ring
    _ ≤ _ := pow_le_pow_right₀ hb1 hexp

/-- The uniform natural-number refinement budget is strictly smaller too;
rounding up does not erase the improvement. -/
theorem section16PowerPieceBudget_lt_previous {theta gamma : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    section16PowerPieceBudget theta gamma k <
      Nat.ceil (gamma ^ (-(2 : Int)) * multipleS theta gamma (k + 1)) := by
  have h1 := section16CommonBasePieceBound_one_le k ht ht1 hg hg1
  have hprev := section16CommonBasePieceBound_le_previous_dimension k ht ht1 hg hg1
  have hdouble := mul_le_mul_of_nonneg_left (multipleS_two_mul_le_succ k ht ht1 hg hg1)
    (show 0 ≤ gamma ^ (-(2 : Int)) by positivity)
  have hcount : (section16PowerPieceBudget theta gamma k : Real) <
      gamma ^ (-(2 : Int)) * multipleS theta gamma (k + 1) := by
    have hc := Nat.ceil_lt_add_one (zero_le_one.trans h1)
    change (section16PowerPieceBudget theta gamma k : Real) < _ at hc
    nlinarith only [hc, h1, hprev, hdouble]
  exact_mod_cast hcount.trans_le (Nat.le_ceil _)

end LeanProofs.GowersSzemeredi
