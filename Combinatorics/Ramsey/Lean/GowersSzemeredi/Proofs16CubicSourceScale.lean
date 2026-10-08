import GowersSzemeredi.Proofs16CubicSpectrumBudget

/-! Put every outer parameter in the cubic construction on a common scale.
The bounds use U=s(theta,gamma,1), before the preliminary density halving. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Dividing density by 2^n costs at most the (n+1)-st power of its scale. -/
theorem multipleS_div_two_pow_le {theta gamma : Real} (k n : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    multipleS (theta / (2 : Real)^n) gamma k ≤ (multipleS theta gamma k)^(n+1) := by
  have hp : 0 < theta * gamma := mul_pos ht hg
  have hp1 : theta * gamma ≤ 1 := mul_le_one₀ ht1 hg.le hg1
  have hb : (2 : Real) ≤ 2 / (theta * gamma) := (le_div_iff₀ hp).mpr (by linarith)
  have hbase : 2 / (theta / (2 : Real)^n * gamma) ≤ (2 / (theta * gamma))^(n+1) := by
    calc
      _ = (2 : Real)^n * (2 / (theta * gamma)) := by field_simp
      _ ≤ (2 / (theta * gamma))^n * (2 / (theta * gamma)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hb n) (by positivity)
      _ = _ := (pow_succ _ _).symm
  unfold multipleS
  calc
    _ ≤ ((2 / (theta * gamma))^(n+1))^((2 : Nat)^((2 : Nat)^(k+6))) :=
      pow_le_pow_left₀ (by positivity) hbase _
    _ = _ := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- The first-dimensional source scale has substantial fixed numerical slack. -/
theorem multipleS_one_ge_sixteen {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    16 ≤ multipleS theta gamma 1 := by
  have hp : 0 < theta * gamma := mul_pos ht hg
  have hp1 : theta * gamma ≤ 1 := mul_le_one₀ ht1 hg.le hg1
  have hb : (2 : Real) ≤ 2 / (theta * gamma) := (le_div_iff₀ hp).mpr (by linarith)
  calc
    (16 : Real) = 2^(4 : Nat) := by norm_num
    _ ≤ (2 / (theta * gamma))^4 := pow_le_pow_left₀ (by norm_num) hb _
    _ ≤ _ := pow_le_pow_right₀ (by linarith : (1 : Real) ≤ 2 / (theta * gamma)) (by norm_num)

theorem gamma_inverse_square_le_multipleS_one {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    gamma ^ (-(2 : Int)) ≤ multipleS theta gamma 1 := by
  have hp : 0 < theta * gamma := mul_pos ht hg
  have hp1 : theta * gamma ≤ 1 := mul_le_one₀ ht1 hg.le hg1
  have hb : (2 : Real) ≤ 2 / (theta * gamma) := (le_div_iff₀ hp).mpr (by linarith)
  have hginv : gamma⁻¹ ≤ 2 / (theta * gamma) := by
    rw [← one_div]
    apply (div_le_div_iff₀ hg hp).mpr
    nlinarith [mul_le_mul_of_nonneg_right ht1 hg.le]
  calc
    gamma ^ (-(2 : Int)) = (gamma⁻¹)^(2 : Nat) := by rw [zpow_neg, zpow_ofNat, inv_pow]
    _ ≤ (2 / (theta * gamma))^2 := pow_le_pow_left₀ (by positivity) hginv _
    _ ≤ _ := pow_le_pow_right₀ (by linarith : (1 : Real) ≤ 2 / (theta * gamma)) (by norm_num)

/-- The proper-face remainder parameter, including the preliminary density
halving, is at most U^6. -/
theorem section16_cubic_remainder_scale_le {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    section16Lemma9R (theta / 2) gamma 1 ≤ (multipleS theta gamma 1)^6 := by
  have hgU := gamma_inverse_square_le_multipleS_one ht ht1 hg hg1
  have hsU := multipleS_div_two_pow_le 1 4 ht ht1 hg hg1
  calc
    section16Lemma9R (theta / 2) gamma 1 =
        gamma ^ (-(2 : Int)) * multipleS (theta / (2 : Real)^4) gamma 1 := by
      have hcoef : (2 : Real)^(-(1 + 2 : Real)) * (theta / 2) = theta / (2 : Real)^4 := by
        norm_num; ring
      simp only [section16Lemma9R, Nat.pow_one, Nat.reduceSub, Nat.cast_one, one_mul]
      rw [hcoef]
    _ ≤ multipleS theta gamma 1 * (multipleS theta gamma 1)^5 :=
      mul_le_mul hgU hsU (by unfold multipleS; positivity) (by unfold multipleS; positivity)
    _ = _ := by ring

/-- The actual spectrum after preliminary density halving has at most U^2
fixed Freiman graphs. -/
theorem section16_cubic_spectrum_scale_le {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    (section16CubicSpectrumCount (theta / 2) gamma : Real) ≤ (multipleS theta gamma 1)^2 :=
  (section16CubicSpectrumCount_le_iteration (by positivity) (by linarith) hg hg1).trans
    (multipleS_half_le_square 1 ht ht1 hg hg1)

/-- The fixed final-section family count is at most U. -/
theorem section16_cubic_slice_scale_le {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    (section16BaseFamilyBound gamma (theta / 4) : Real) ≤ multipleS theta gamma 1 := by
  have hp : 0 < theta * gamma := mul_pos ht hg
  have hp1 : theta * gamma ≤ 1 := mul_le_one₀ ht1 hg.le hg1
  have hb : (2 : Real) ≤ 2 / (theta * gamma) := (le_div_iff₀ hp).mpr (by linarith)
  have hbase : 2 / (gamma * (theta / 4)) ≤ (2 / (theta * gamma))^3 := by
    calc
      _ = (2 : Real)^2 * (2 / (theta * gamma)) := by ring
      _ ≤ (2 / (theta * gamma))^2 * (2 / (theta * gamma)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hb 2) (by positivity)
      _ = _ := by ring
  calc
    (section16BaseFamilyBound gamma (theta / 4) : Real) ≤ (2 / (gamma * (theta / 4)))^(10002 : Nat) :=
      section16BaseFamilyBound_le_power hg hg1 (by positivity) (by linarith)
    _ ≤ ((2 / (theta * gamma))^3)^(10002 : Nat) := pow_le_pow_left₀ (by positivity) hbase _
    _ = (2 / (theta * gamma))^(30006 : Nat) := by rw [← pow_mul]
    _ ≤ _ := pow_le_pow_right₀ (by linarith : (1 : Real) ≤ 2 / (theta * gamma)) (by norm_num)

end LeanProofs.GowersSzemeredi
