import GowersSzemeredi.Proofs13SquareThresholdSpectralBound

/-! Polynomial reciprocal budgets for the actual Stage 13.4 recurrence
parameters, including q=0 in the finite threshold maxima. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section13Q_ge_512 {delta : Real} (hδ : 0 < delta) (hδone : delta ≤ 1) :
    512 ≤ section13Q delta := by
  have h := section13_monomial_le_Q hδ hδone (a := 9) (b := 0) (by norm_num) (by norm_num)
  norm_num at h
  exact h

theorem section13ThetaOne_inv_le_Q {delta : Real} (hδ : 0 < delta) (hδone : delta ≤ 1) :
    (section13ThetaOne (section10Lambda (delta ^ 32 / 16)))⁻¹ ≤ section13Q delta := by
  let theta := section10Lambda (delta ^ 32 / 16)
  have hθ : 0 < theta := by dsimp [theta, section10Lambda]; positivity
  have hθone : theta ≤ 1 := by
    rw [show theta = (2 : Real) ^ (-(59 : Int)) * delta ^ 176 from section13_lambda_formula hδ]
    exact (mul_le_mul_of_nonneg_left (pow_le_one₀ hδ.le hδone) (by positivity)).trans (by norm_num)
  have hθ1 : 0 < section13ThetaOne theta := by unfold section13ThetaOne; positivity
  have hfirst : (section13ThetaOne theta)⁻¹ ≤ section13QBound theta := by
    rw [← one_div]
    apply (div_le_iff₀ hθ1).mpr
    rw [mul_comm, section13_thetaOne_qBound_product hθ]
    exact one_le_zpow_of_nonpos₀ hθ hθone (by norm_num)
  have hQ := section13Q_ge_512 hδ hδone
  exact hfirst.trans ((section13_qBound_le_half_Q hδ hδone).trans (by linarith only [hQ]))

theorem section13_initial_coefficient_inv_le_Q_sq {delta : Real}
    (hδ : 0 < delta) (hδone : delta ≤ 1) :
    (section13ThetaOne (section10Lambda (delta ^ 32 / 16)) / (64 * Real.pi))⁻¹ ≤
      section13Q delta ^ 2 := by
  let Q := section13Q delta
  have hQ : 512 ≤ Q := section13Q_ge_512 hδ hδone
  have hQ0 : 0 ≤ Q := by linarith only [hQ]
  have hi := section13ThetaOne_inv_le_Q hδ hδone
  have hc : 64 * Real.pi ≤ Q := by have hp := Real.pi_lt_four; linarith only [hp, hQ]
  rw [inv_div, div_eq_mul_inv]
  exact (mul_le_mul hc hi (by unfold section13ThetaOne section10Lambda; positivity) hQ0).trans_eq (sq Q).symm

theorem section13_initial_exponent_inv_le_Q_four {delta : Real}
    (hδ : 0 < delta) (hδone : delta ≤ 1) {q : Nat} (hq : (q : Real) ≤ section13Q delta) :
    (section13ThetaOne (section10Lambda (delta ^ 32 / 16)) ^ 2 / (16 * (q : Real)))⁻¹ ≤
      section13Q delta ^ 4 := by
  let Q := section13Q delta
  have hQ : 512 ≤ Q := section13Q_ge_512 hδ hδone
  have hQ0 : 0 ≤ Q := by linarith only [hQ]
  have hi := section13ThetaOne_inv_le_Q hδ hδone
  rw [inv_div, div_eq_mul_inv, ← inv_pow]
  calc
    _ ≤ (Q * Q) * Q ^ 2 := mul_le_mul
      (mul_le_mul (by linarith only [hQ] : (16 : Real) ≤ Q) hq (Nat.cast_nonneg _) hQ0)
      (pow_le_pow_left₀ (by unfold section13ThetaOne section10Lambda; positivity) hi 2)
      (by positivity) (mul_nonneg hQ0 hQ0)
    _ = _ := by ring

theorem section13_initial_min_coefficient_inv_le_Q_cube {delta : Real}
    (hδ : 0 < delta) (hδone : delta ≤ 1) :
    (min 1 (section13ThetaOne (section10Lambda (delta ^ 32 / 16)) / (64 * Real.pi) / 2))⁻¹ ≤
      section13Q delta ^ 3 := by
  let d := section13ThetaOne (section10Lambda (delta ^ 32 / 16)) / (64 * Real.pi)
  have hd : 0 < d := by dsimp [d, section13ThetaOne, section10Lambda]; positivity
  have hQ := section13Q_ge_512 hδ hδone
  have hQ0 : 0 ≤ section13Q delta := by linarith only [hQ]
  by_cases h : 1 ≤ d / 2
  · rw [min_eq_left h, inv_one]
    exact one_le_pow₀ (by linarith only [hQ])
  · rw [min_eq_right (le_of_not_ge h), inv_div, div_eq_mul_inv]
    calc
      _ ≤ section13Q delta * section13Q delta ^ 2 :=
        mul_le_mul (by linarith only [hQ] : (2 : Real) ≤ section13Q delta)
          (section13_initial_coefficient_inv_le_Q_sq hδ hδone) (inv_nonneg.mpr hd.le) hQ0
      _ = _ := by ring

theorem real_pow_le_exp_nat_mul {x : Real} (hx : 0 ≤ x) (n : Nat) :
    x ^ n ≤ Real.exp ((n : Real) * x) := by
  have h : x ≤ Real.exp x := by have h := Real.add_one_le_exp x; linarith only [h]
  simpa only [← Real.exp_nat_mul] using pow_le_pow_left₀ hx h n

/-- A ceiling or additive rounding loss costs at most one unit in the
inner argument of a double exponential. -/
theorem double_exp_add_one_le {x : Real} (hx : 0 ≤ x) :
    Real.exp (Real.exp x) + 1 ≤ Real.exp (Real.exp (x + 1)) := by
  have he : 1 ≤ Real.exp x := Real.one_le_exp_iff.mpr hx
  have hee : 1 ≤ Real.exp (Real.exp x) := Real.one_le_exp_iff.mpr (Real.exp_pos _).le
  have htwo : (2 : Real) ≤ Real.exp 1 := by have h := Real.add_one_le_exp (1 : Real); linarith only [h]
  have hinner : Real.exp x + 1 ≤ Real.exp (x + 1) := by
    rw [Real.exp_add]
    nlinarith only [he, mul_le_mul_of_nonneg_left htwo (Real.exp_pos x).le]
  calc
    _ ≤ Real.exp (Real.exp x) * Real.exp 1 := by
      nlinarith only [hee, mul_le_mul_of_nonneg_left htwo (Real.exp_pos (Real.exp x)).le]
    _ = Real.exp (Real.exp x + 1) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hinner

theorem nat_ceil_le_double_exp_add_one {x y : Real} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : y ≤ Real.exp (Real.exp x)) :
    (Nat.ceil y : Real) ≤ Real.exp (Real.exp (x + 1)) :=
  (Nat.ceil_lt_add_one hy).le.trans ((add_le_add h (le_refl (1 : Real))).trans (double_exp_add_one_le hx))

end LeanProofs.GowersSzemeredi
