import GowersSzemeredi.Proofs16CubicSourceScale

/-! Scalar power absorption for the cubic structural budget. The reserve
between U^6 and U^8 pays for the spectrum recurrence and polynomial factors,
uniformly in the inner loss. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section16_cubic_exponent_reserve {U A R : Real}
    (hU : 16 ≤ U) (hA : 1 ≤ A) (hR : R ≤ U^6) :
    5 * A * R + 84 * U^2 + 99 ≤ A * U^8 := by
  have hU0 : 0 ≤ U := by linarith
  have hU1 : 1 ≤ U := by linarith
  have hU2 : (256 : Real) ≤ U^2 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 16) hU 2
    norm_num at hh
    exact hh
  have hp : U^2 ≤ U^6 := pow_le_pow_right₀ hU1 (by norm_num)
  have hres : 84 * U^2 + 99 ≤ U^8 - 5 * R := by
    have hm := mul_nonneg (by linarith : 0 ≤ U^2 - 105) (pow_nonneg hU0 6)
    nlinarith only [hU2, hp, hR, hm]
  have hdiff : 0 ≤ U^8 - 5 * R := by nlinarith [sq_nonneg U]
  have hh := mul_le_mul_of_nonneg_right hA hdiff
  nlinarith only [hres, hh]

/-- Four factors of the small base pay independently for the line width,
slice loss, spectrum recurrence, and outer polynomial denominator. -/
theorem section16_cubic_power_absorption_of_bounds {U A R p t sigma : Real}
    (hU : 16 ≤ U) (hA : 1 ≤ A) (hR : 0 < R) (hRU : R ≤ U^6)
    (hp : 0 < p) (hp1 : p ≤ 1) (hpt : p ≤ t) (hps : p ≤ sigma)
    (hp2 : p ≤ 1 / 2) (hpU : p ≤ U⁻¹) :
    p ^ (A * U^8) ≤ t ^ (5 * A * R) * sigma^(10 : Nat) *
      (2 : Real)^(-(84 * U^2 + 75)) / U^(14 : Nat) := by
  have ht0 : 0 ≤ t := hp.le.trans hpt
  have hs0 : 0 ≤ sigma := hp.le.trans hps
  have hA0 : 0 < A := by linarith
  have hreserve := section16_cubic_exponent_reserve hU hA hRU
  have hfirst : p ^ (5 * A * R) ≤ t ^ (5 * A * R) :=
    Real.rpow_le_rpow hp.le hpt (by positivity)
  have hsecond : p^(10 : Nat) ≤ sigma^(10 : Nat) := pow_le_pow_left₀ hp.le hps _
  have hthird : p ^ (84 * U^2 + 75) ≤ (2 : Real)^(-(84 * U^2 + 75)) := by
    calc
      _ ≤ (1 / 2 : Real) ^ (84 * U^2 + 75) := Real.rpow_le_rpow hp.le hp2 (by positivity)
      _ = _ := by rw [one_div, ← Real.rpow_neg_eq_inv_rpow]
  have hfourth : p^(14 : Nat) ≤ (U^(14 : Nat))⁻¹ := by
    simpa only [inv_pow] using pow_le_pow_left₀ hp.le hpU 14
  calc
    p ^ (A * U^8) ≤ p ^ (5 * A * R + 10 + (84 * U^2 + 75) + 14) :=
      Real.rpow_le_rpow_of_exponent_ge hp hp1 (by linarith only [hreserve])
    _ = p ^ (5 * A * R) * p^(10 : Nat) * p ^ (84 * U^2 + 75) * p^(14 : Nat) := by
      simp only [Real.rpow_add hp, Real.rpow_ofNat]
    _ ≤ _ := by
      rw [div_eq_mul_inv]
      exact mul_le_mul
        (mul_le_mul (mul_le_mul hfirst hsecond (by positivity) (by positivity))
          hthird (by positivity) (by positivity)) hfourth (by positivity) (by positivity)

/-- The actual base gamma*rho/U^8, with rho=4*sigma, satisfies all the
power-absorption bounds on the admissible density range. -/
theorem section16_cubic_power_absorption {U A R gamma sigma : Real}
    (hU : 16 ≤ U) (hA : 1 ≤ A) (hR : 0 < R) (hRU : R ≤ U^6)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hs : 0 < sigma) (hs1 : sigma ≤ 1) :
    (4 * gamma * sigma / U^8) ^ (A * U^8) ≤
      (gamma * sigma / (2 * R)) ^ (5 * A * R) * sigma^(10 : Nat) *
      (2 : Real)^(-(84 * U^2 + 75)) / U^(14 : Nat) := by
  have hU0 : 0 < U := by linarith
  have hU2 : (256 : Real) ≤ U^2 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 16) hU 2
    norm_num at hh
    exact hh
  have hU7 : (4 : Real) ≤ U^7 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 16) hU 7
    norm_num at hh
    linarith
  have hU8 : (8 : Real) ≤ U^8 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 16) hU 8
    norm_num at hh
    linarith
  have hprod : gamma * sigma ≤ 1 := mul_le_one₀ hg1 hs.le hs1
  have hp2 : 4 * gamma * sigma / U^8 ≤ (1 / 2 : Real) := by
    apply (div_le_iff₀ (pow_pos hU0 8)).mpr
    nlinarith only [hprod, hU8]
  apply section16_cubic_power_absorption_of_bounds hU hA hR hRU (by positivity) (by linarith) ?_ ?_ hp2 ?_
  · have hRscale : 8 * R ≤ U^8 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ U^2 - 8) (pow_nonneg hU0.le 6)]
    apply (div_le_div_iff₀ (pow_pos hU0 8) (by positivity : 0 < 2 * R)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hRscale (mul_pos hg hs).le]
  · apply (div_le_iff₀ (pow_pos hU0 8)).mpr
    nlinarith only [hs.le, mul_le_mul_of_nonneg_right hg1 hs.le,
      mul_le_mul_of_nonneg_right hU8 hs.le]
  · rw [← one_div]
    apply (div_le_div_iff₀ (pow_pos hU0 8) hU0).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hprod hU0.le,
      mul_le_mul_of_nonneg_right hU7 hU0.le]

end LeanProofs.GowersSzemeredi
