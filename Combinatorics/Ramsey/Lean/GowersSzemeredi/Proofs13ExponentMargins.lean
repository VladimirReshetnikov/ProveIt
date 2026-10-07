import GowersSzemeredi.Proofs13BilinearExtraction

/-! Quantitative margins between the Section 13 recurrence exponents.
Large powers of two are kept symbolic rather than expanded as numerals. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The lower edge-density parameter gives the Fourier cutoff printed in
Lemma 13.6. -/
theorem section13_lambda_formula {alpha : Real} (hα : 0 < alpha) :
    section10Lambda (alpha ^ 32 / 16) = (2 : Real) ^ (-(59 : Int)) * alpha ^ 176 := by
  unfold section10Lambda
  rw [Real.div_rpow (pow_nonneg hα.le _) (by norm_num),
    ← Real.rpow_natCast_mul hα.le]
  have hden : (16 : Real) ^ ((11 : Real) / 2) = (2 : Real) ^ (22 : Nat) := by
    rw [show (16 : Real) = (2 : Real) ^ (4 : Nat) by norm_num,
      ← Real.rpow_natCast_mul (by norm_num)]
    norm_num
  rw [hden]
  norm_num [Real.rpow_neg, zpow_neg]
  ring

/-- A convenient coarser cutoff, preserving a large margin in the spectral
count bound. -/
theorem section13_lambda_lower {alpha : Real} (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    (2 : Real) ^ (-(64 : Real)) * alpha ^ (192 : Real) ≤
      section10Lambda (alpha ^ 32 / 16) := by
  rw [section13_lambda_formula hα, Real.rpow_ofNat alpha 192]
  have hpow : alpha ^ 192 ≤ alpha ^ 176 := pow_le_pow_of_le_one hα.le hαone (by omega)
  have htwo : (2 : Real) ^ (-(64 : Real)) ≤ (2 : Real) ^ (-(59 : Int)) := by
    rw [← Real.rpow_intCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  exact mul_le_mul htwo hpow (pow_nonneg hα.le _) (by positivity)

/-- The actual Stage 13.4 spectrum count is at most half the much larger
parameter used in Lemma 13.6. -/
theorem section13_qBound_le_half_Q {alpha : Real} (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    section13QBound (section10Lambda (alpha ^ 32 / 16)) ≤ section13Q alpha / 2 := by
  let theta := section10Lambda (alpha ^ 32 / 16)
  have hbase : 0 < (2 : Real) ^ (-(64 : Real)) * alpha ^ (192 : Real) := by positivity
  have htheta := section13_lambda_lower hα hαone
  have hrecip : theta ^ (-(10479 : Real)) ≤
      ((2 : Real) ^ (-(64 : Real)) * alpha ^ (192 : Real)) ^ (-(10479 : Real)) :=
    Real.rpow_le_rpow_of_nonpos hbase htheta (by norm_num)
  have hformula : (2 : Real) ^ (1882 : Real) *
      ((2 : Real) ^ (-(64 : Real)) * alpha ^ (192 : Real)) ^ (-(10479 : Real)) =
      (2 : Real) ^ (672538 : Real) * alpha ^ (-(2011968 : Real)) := by
    rw [Real.mul_rpow (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hα.le _),
      ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 2), ← Real.rpow_mul hα.le]
    rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : Real) < 2)]
    congr 1 <;> norm_num
  have hlarge : (2 : Real) ^ (672538 : Real) * alpha ^ (-(2011968 : Real)) ≤
      (2 : Real) ^ (1048575 : Real) * alpha ^ (-(2097152 : Real)) := by
    apply mul_le_mul
    · exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    · exact Real.rpow_le_rpow_of_exponent_ge hα hαone (by norm_num)
    · positivity
    · positivity
  have hQ : (2 : Real) ^ (1048575 : Real) * alpha ^ (-(2097152 : Real)) =
      section13Q alpha / 2 := by
    unfold section13Q
    rw [show (2 : Nat) ^ 20 = 1048576 by norm_num,
      show (2 : Real) ^ (21 : Nat) = 2097152 by norm_num, ← Real.rpow_natCast]
    norm_num only [Nat.cast_ofNat]
    rw [show (1048576 : Real) = 1048575 + 1 by norm_num,
      Real.rpow_add (by norm_num : (0 : Real) < 2), Real.rpow_one]
    ring
  calc
    _ = (2 : Real) ^ (1882 : Real) * theta ^ (-(10479 : Real)) := by
      unfold section13QBound
      simp only [Real.rpow_ofNat, Real.rpow_neg_ofNat, theta]
    _ ≤ (2 : Real) ^ (1882 : Real) *
        ((2 : Real) ^ (-(64 : Real)) * alpha ^ (192 : Real)) ^ (-(10479 : Real)) :=
      mul_le_mul_of_nonneg_left hrecip (by positivity)
    _ = _ := hformula
    _ ≤ _ := hlarge
    _ = _ := hQ

/-- The two Stage 13.4 parameters have an exact reciprocal relation. -/
theorem section13_thetaOne_qBound_product {theta : Real} (hθ : 0 < theta) :
    section13ThetaOne theta * section13QBound theta = theta ^ (-(2 : Int)) := by
  have htwo : (2 : Real) ^ (1882 : Nat) * (2 : Real) ^ (-(1882 : Int)) = 1 := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : Real) ≠ 0)]
    norm_num
  have ht : theta ^ (-(10479 : Int)) * theta ^ (10477 : Nat) = theta ^ (-(2 : Int)) := by
    rw [← zpow_natCast, ← zpow_add₀ hθ.ne']
    norm_num
  unfold section13ThetaOne section13QBound
  calc
    _ = ((2 : Real) ^ (1882 : Nat) * (2 : Real) ^ (-(1882 : Int))) *
        (theta ^ (-(10479 : Int)) * theta ^ (10477 : Nat)) := by ring
    _ = _ := by rw [htwo, ht, one_mul]

/-- An exponential margin sufficient for the Section 13 recurrence powers. -/
theorem two_rpow_seven_mul_gt {Q : Real} (hQ : 1 ≤ Q) :
    2 * Q ^ 3 < (2 : Real) ^ (7 * Q) := by
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hlog : (1 : Real) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : Real) < 2)
    norm_num at h
    exact h
  have hlin := Real.add_one_le_exp (Real.log 2 * (2 * Q))
  have hbase : Q < (2 : Real) ^ (2 * Q) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    nlinarith only [hlin, hlog, hQpos]
  have hpow : Q ^ 3 < ((2 : Real) ^ (2 * Q)) ^ 3 :=
    pow_lt_pow_left₀ hbase hQpos.le (by decide)
  have htwo : (2 : Real) ≤ (2 : Real) ^ Q := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 2) hQ)
  calc
    _ < 2 * ((2 : Real) ^ (2 * Q)) ^ 3 := mul_lt_mul_of_pos_left hpow (by norm_num)
    _ ≤ (2 : Real) ^ Q * ((2 : Real) ^ (2 * Q)) ^ 3 :=
      mul_le_mul_of_nonneg_right htwo (by positivity)
    _ = (2 : Real) ^ (7 * Q) := by
      rw [← Real.rpow_mul_natCast (by norm_num), ← Real.rpow_add (by norm_num)]
      congr 1
      ring

/-- The target exponent for Stage 13.6 is strictly below the exponent
obtained by combining the Stage 13.4 length and Stage 13.5 recurrence.
This strict margin absorbs constants and rounding at sufficiently large N. -/
theorem section13_recurrence_exponent_margin {alpha : Real} (hα : 0 < alpha)
    (hαone : alpha ≤ 1) {q : Nat} (hq : 0 < q)
    (hqBound : (q : Real) ≤ section13QBound (section10Lambda (alpha ^ 32 / 16))) :
    (1 : Real) / (2 : Real) ^ (13 * section13Q alpha) <
      (section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) ^ 2 / (16 * q)) *
        ((1 : Real) / (2 : Real) ^ (12 * q)) := by
  let theta := section10Lambda (alpha ^ 32 / 16)
  let B := section13QBound theta
  let Q := section13Q alpha
  let u := section13ThetaOne theta ^ 2 / (16 * (q : Real))
  have hθ : 0 < theta := by dsimp [theta, section10Lambda]; positivity
  have hθone : theta ≤ 1 := by
    rw [show theta = (2 : Real) ^ (-(59 : Int)) * alpha ^ 176 from section13_lambda_formula hα]
    calc
      _ ≤ (2 : Real) ^ (-(59 : Int)) * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ hα.le hαone) (by positivity)
      _ ≤ 1 := by norm_num
  have hB : 0 < B := by
    exact mul_pos (pow_pos (by norm_num) _) (zpow_pos hθ _)
  have hQB : B ≤ Q / 2 := section13_qBound_le_half_Q hα hαone
  have hQ : 1 ≤ Q := by
    unfold Q section13Q
    calc
      1 = 1 * 1 := by ring
      _ ≤ (2 : Real) ^ ((2 : Nat) ^ 20) * alpha ^ (-((2 : Real) ^ (21 : Nat))) :=
        mul_le_mul (one_le_pow₀ (by norm_num))
          (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hα hαone (neg_nonpos.mpr (by positivity)))
          (by norm_num) (by positivity)
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hqReal : (0 : Real) < q := by exact_mod_cast hq
  have hθlower : 1 / B ≤ section13ThetaOne theta := by
    apply (div_le_iff₀ hB).mpr
    rw [section13_thetaOne_qBound_product hθ]
    exact one_le_zpow_of_nonpos₀ hθ hθone (by norm_num)
  have huB : 1 / (16 * B ^ 3) ≤ u := by
    calc
      _ = (1 / B) ^ 2 / (16 * B) := by field_simp
      _ ≤ section13ThetaOne theta ^ 2 / (16 * (q : Real)) :=
        div_le_div₀ (sq_nonneg _) (pow_le_pow_left₀ (by positivity) hθlower 2)
          (by positivity) (mul_le_mul_of_nonneg_left hqBound (by norm_num))
  have hden : 16 * B ^ 3 ≤ 2 * Q ^ 3 := by
    have hp := pow_le_pow_left₀ hB.le hQB 3
    nlinarith only [hp]
  have hu : 1 / (2 * Q ^ 3) ≤ u := by
    exact (one_div_le_one_div_of_le (by positivity) hden).trans huB
  have he : 1 / (2 : Real) ^ (7 * Q) < u :=
    (one_div_lt_one_div_of_lt (mul_pos (by norm_num) (pow_pos hQpos 3))
      (two_rpow_seven_mul_gt hQ)).trans_le hu
  have hv : 1 / (2 : Real) ^ (6 * Q) ≤ 1 / (2 : Real) ^ (12 * q) := by
    apply one_div_le_one_div_of_le (by positivity)
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    have hqQ : (q : Real) ≤ Q / 2 := hqBound.trans hQB
    linarith
  calc
    _ = (1 / (2 : Real) ^ (7 * Q)) * (1 / (2 : Real) ^ (6 * Q)) := by
      rw [one_div_mul_one_div, ← Real.rpow_add (by norm_num)]
      congr 2
      ring
    _ < u * (1 / (2 : Real) ^ (6 * Q)) := mul_lt_mul_of_pos_right he (by positivity)
    _ ≤ u * (1 / (2 : Real) ^ (12 * q)) :=
      mul_le_mul_of_nonneg_left hv ((one_div_pos.mpr (mul_pos (by norm_num) (pow_pos hQpos 3))).trans_le hu).le

end LeanProofs.GowersSzemeredi
