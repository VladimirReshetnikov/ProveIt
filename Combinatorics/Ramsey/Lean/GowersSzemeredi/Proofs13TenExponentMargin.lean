import GowersSzemeredi.Proofs13UniformDensityParameters

/-! A stronger exponent margin for the common-step row extraction. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem four_mul_cube_lt_two_rpow_four {Q : Real} (hQ : 2 ≤ Q) :
    4 * Q ^ 3 < (2 : Real) ^ (4 * Q) := by
  have hQ0 : 0 ≤ Q := by linarith only [hQ]
  have hlog : (1 : Real) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : Real) < 2)
    norm_num at h
    exact h
  have he := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ Q / 2)
  have hbase : Q < (2 : Real) ^ Q := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    apply lt_of_lt_of_le (b := Real.exp (Q / 2))
    · nlinarith only [he, sq_nonneg (Q - 2)]
    · apply Real.exp_le_exp.mpr
      nlinarith only [mul_nonneg hQ0 (sub_nonneg.mpr hlog)]
  have hpow := pow_lt_pow_left₀ hbase hQ0 (by decide : (3 : Nat) ≠ 0)
  have hfour : (4 : Real) ≤ (2 : Real) ^ Q := by
    calc
      _ = (2 : Real) ^ (2 : Real) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hQ
  calc
    _ < 4 * ((2 : Real) ^ Q) ^ 3 := mul_lt_mul_of_pos_left hpow (by norm_num)
    _ ≤ (2 : Real) ^ Q * ((2 : Real) ^ Q) ^ 3 :=
      mul_le_mul_of_nonneg_right hfour (by positivity)
    _ = _ := by
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : Real) ≤ 2),
        ← Real.rpow_add (by norm_num : (0 : Real) < 2)]
      congr 1
      ring

theorem section13_ten_recurrence_exponent_margin {alpha : Real} (hα : 0 < alpha)
    (hαone : alpha ≤ 1) {q : Nat} (hq : 0 < q)
    (hqBound : (q : Real) ≤ section13QBound (section10Lambda (alpha ^ 32 / 16))) :
    2 * ((1 : Real) / (2 : Real) ^ (10 * section13Q alpha)) <
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
  have hQ : 2 ≤ Q := by
    have hqone : (1 : Real) ≤ q := by exact_mod_cast hq
    have hqQ : (q : Real) ≤ Q / 2 := hqBound.trans hQB
    linarith only [hqone, hqQ]
  have hQpos : 0 < Q := (by linarith only [hQ] : 0 < Q)
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
  have he : 2 / (2 : Real) ^ (4 * Q) < u := by
    have hfour := four_mul_cube_lt_two_rpow_four hQ
    have hlt : 2 / (2 : Real) ^ (4 * Q) < 1 / (2 * Q ^ 3) := by
      apply (div_lt_div_iff₀ (Real.rpow_pos_of_pos (by norm_num) _)
        (mul_pos (by norm_num) (pow_pos hQpos 3))).mpr
      nlinarith only [hfour]
    exact hlt.trans_le hu
  have hv : 1 / (2 : Real) ^ (6 * Q) ≤ 1 / (2 : Real) ^ (12 * q) := by
    apply one_div_le_one_div_of_le (by positivity)
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    have hqQ : (q : Real) ≤ Q / 2 := hqBound.trans hQB
    linarith
  have hexp : (2 : Real) ^ (10 * Q) = (2 : Real) ^ (4 * Q) * (2 : Real) ^ (6 * Q) := by
    rw [← Real.rpow_add (by norm_num)]
    congr 1
    ring
  calc
    _ = (2 / (2 : Real) ^ (4 * Q)) * (1 / (2 : Real) ^ (6 * Q)) := by
      change 2 * (1 / (2 : Real) ^ (10 * Q)) = _
      simp only [hexp, div_eq_mul_inv, mul_inv_rev]
      ring
    _ < u * (1 / (2 : Real) ^ (6 * Q)) := mul_lt_mul_of_pos_right he (by positivity)
    _ ≤ u * (1 / (2 : Real) ^ (12 * q)) :=
      mul_le_mul_of_nonneg_left hv ((one_div_pos.mpr (mul_pos (by norm_num) (pow_pos hQpos 3))).trans_le hu).le

end LeanProofs.GowersSzemeredi
