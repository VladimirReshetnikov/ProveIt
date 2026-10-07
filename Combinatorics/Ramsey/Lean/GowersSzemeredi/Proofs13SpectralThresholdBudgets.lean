import GowersSzemeredi.Proofs13ExplicitFourierExponent
import GowersSzemeredi.Proofs13FejerThresholdPolynomial

/-! The large spectral parameter controls the reciprocal Bohr radii and
polynomial coefficients needed to bound the explicit geometric threshold. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section13Q_inverse_power (delta : Real) :
    section13Q delta = (2 : Real) ^ ((2 : Nat) ^ 20) *
      (delta⁻¹) ^ ((2 : Nat) ^ 21) := by
  unfold section13Q
  rw [Real.rpow_neg_eq_inv_rpow,
    show (2 : Real) ^ (21 : Nat) = (((2 : Nat) ^ 21 : Nat) : Real) by norm_num,
    Real.rpow_natCast]

/-- Every modest fixed monomial in the reciprocal density is bounded by Q. -/
theorem section13_monomial_le_Q {delta : Real} (hδ : 0 < delta) (hδone : delta ≤ 1)
    {a b : Nat} (ha : a ≤ (2 : Nat) ^ 20) (hb : b ≤ (2 : Nat) ^ 21) :
    (2 : Real) ^ a * (delta⁻¹) ^ b ≤ section13Q delta := by
  rw [section13Q_inverse_power]
  exact mul_le_mul (pow_le_pow_right₀ (by norm_num) ha)
    (pow_le_pow_right₀ ((one_le_inv₀ hδ).mpr hδone) hb)
    (by positivity) (by positivity)

/-- The Section 13 Bohr-length coefficient has at most exponential
reciprocal size in the common spectral parameter. -/
theorem section13Zeta_inv_le_spectral_exp {delta : Real}
    (hδ : 0 < delta) (hδone : delta ≤ 1) :
    (section13Zeta delta)⁻¹ ≤ (2 : Real) ^ section13Q delta := by
  let t := delta⁻¹
  let K := section13K delta
  have ht : 1 ≤ t := (one_le_inv₀ hδ).mpr hδone
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hK : 0 ≤ K := by dsimp [K, section13K]; positivity
  have hKi : K = (2 : Real) ^ (114 : Nat) * t ^ (320 : Nat) := by
    simp only [K, section13K, t, zpow_neg, zpow_ofNat, inv_pow]
  have hbudget : 228 * K + 1152 * K * t ≤ section13Q delta := by
    have hpoly : 228 * K + 1152 * K * t ≤ (2 : Real) ^ (125 : Nat) * t ^ (321 : Nat) := by
      have hp := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 228 * K)
      rw [hKi] at hp ⊢
      rw [show (321 : Nat) = 320 + 1 by omega, pow_succ t 320]
      have hc : (1380 : Real) * (2 : Real) ^ (114 : Nat) ≤ (2 : Real) ^ (125 : Nat) := by norm_num
      have hh := mul_le_mul_of_nonneg_right hc (mul_nonneg (pow_nonneg ht0 320) ht0)
      nlinarith only [hp, hh]
    exact hpoly.trans (section13_monomial_le_Q hδ hδone (by norm_num) (by norm_num))
  calc
    _ = (2 : Real) ^ (228 * K) * t ^ (576 * K) := by
      unfold section13Zeta
      rw [mul_inv_rev, ← Real.rpow_neg (by norm_num : (0 : Real) ≤ 2), neg_neg,
        ← Real.inv_rpow hδ.le]
      exact mul_comm _ _
    _ ≤ (2 : Real) ^ (228 * K) * ((2 : Real) ^ (2 * t)) ^ (576 * K) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht0 (le_two_rpow_two_mul ht0) (mul_nonneg (by norm_num) hK))
        (Real.rpow_nonneg (by norm_num) _)
    _ = (2 : Real) ^ (228 * K + 1152 * K * t) := by
      rw [← Real.rpow_mul (by norm_num : (0 : Real) ≤ 2), ← Real.rpow_add (by norm_num : (0 : Real) < 2)]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hbudget

/-- The ceiling in the Section 10 spectral parameter costs only a factor two
relative to the fixed Section 13 polynomial spectral bound. -/
theorem section10SpectrumParameter_le_two_section13K {delta : Real}
    (hδ : 0 < delta) (hδone : delta ≤ 1) :
    (section10SpectrumParameter (delta ^ 32 / 16) : Real) ≤ 2 * section13K delta := by
  have hform : section10SpectrumBound (delta ^ 32 / 16) = section13K delta := by
    unfold section10SpectrumBound section13K
    rw [Real.rpow_neg, Real.rpow_ofNat]
    · rw [div_pow, ← pow_mul]
      norm_num only [show (32 : Nat) * 10 = 320 by omega]
      rw [inv_div, div_eq_mul_inv]
      norm_num [zpow_neg, zpow_ofNat, inv_pow]
      ring
    · positivity
  have hKone : 1 ≤ section13K delta := by
    unfold section13K
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
      (one_le_zpow_of_nonpos₀ hδ hδone (by norm_num))
  unfold section10SpectrumParameter
  rw [hform]
  exact (Nat.ceil_lt_add_one (zero_le_one.trans hKone)).le.trans (by linarith only [hKone])

/-- The corrected Section 10 radius, including its ceiling denominator,
also has reciprocal at most 2^Q at the Section 13 input density. -/
theorem section10Zeta_inv_le_spectral_exp {delta : Real}
    (hδ : 0 < delta) (hδone : delta ≤ 1) :
    (section10Zeta (delta ^ 32 / 16))⁻¹ ≤ (2 : Real) ^ section13Q delta := by
  let t := delta⁻¹
  let u := delta ^ 32 / 16
  let k := section10SpectrumParameter u
  let K := section13K delta
  have ht : 1 ≤ t := (one_le_inv₀ hδ).mpr hδone
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hu : 0 < u := by dsimp [u]; positivity
  have hK : 0 ≤ K := by dsimp [K, section13K]; positivity
  have hKi : K = (2 : Real) ^ (114 : Nat) * t ^ (320 : Nat) := by
    simp only [K, section13K, t, zpow_neg, zpow_ofNat, inv_pow]
  have hui : u⁻¹ = 16 * t ^ (32 : Nat) := by
    dsimp [u, t]
    rw [inv_div, div_eq_mul_inv, inv_pow]
  have hk : (k : Real) ≤ 2 * K := section10SpectrumParameter_le_two_section13K hδ hδone
  have hk0 : (0 : Real) ≤ k := Nat.cast_nonneg _
  have hbudget : 157 * (k : Real) + 36 * k * u⁻¹ ≤ section13Q delta := by
    have hfirst : 157 * (k : Real) + 36 * k * u⁻¹ ≤ 314 * K + 1152 * K * t ^ (32 : Nat) := by
      have h1 := mul_le_mul_of_nonneg_left hk (by norm_num : (0 : Real) ≤ 157)
      have h2 := mul_le_mul_of_nonneg_right hk (by positivity : 0 ≤ 36 * u⁻¹)
      rw [hui] at h2 ⊢
      nlinarith only [h1, h2]
    have ht32 : 1 ≤ t ^ (32 : Nat) := one_le_pow₀ ht
    have hpoly : 314 * K + 1152 * K * t ^ (32 : Nat) ≤
        (2 : Real) ^ (125 : Nat) * t ^ (352 : Nat) := by
      have hp := mul_le_mul_of_nonneg_left ht32 (mul_nonneg (by norm_num : (0 : Real) ≤ 314) hK)
      rw [hKi] at hp ⊢
      rw [show (352 : Nat) = 320 + 32 by omega, pow_add]
      have hc : (1466 : Real) * (2 : Real) ^ (114 : Nat) ≤ (2 : Real) ^ (125 : Nat) := by norm_num
      have hh := mul_le_mul_of_nonneg_right hc (mul_nonneg (pow_nonneg ht0 320) (pow_nonneg ht0 32))
      nlinarith only [hp, hh]
    exact hfirst.trans (hpoly.trans (section13_monomial_le_Q hδ hδone (by norm_num) (by norm_num)))
  calc
    _ = (k : Real) * (2 : Real) ^ (155 * (k : Real)) * (u⁻¹) ^ (18 * k) := by
      change ((2 : Real) ^ (-(155 : Real) * (k : Real)) * u ^ (18 * k) / (k : Real))⁻¹ = _
      rw [inv_div, div_eq_mul_inv, mul_inv_rev, ← inv_pow,
        ← Real.rpow_neg (by norm_num : (0 : Real) ≤ 2)]
      have hh : -(-(155 : Real) * (k : Real)) = 155 * (k : Real) := by ring
      rw [hh]
      ring
    _ ≤ (2 : Real) ^ (2 * (k : Real)) * (2 : Real) ^ (155 * (k : Real)) *
        ((2 : Real) ^ (2 * u⁻¹)) ^ (18 * k) := by
      apply mul_le_mul _ (pow_le_pow_left₀ (inv_nonneg.mpr hu.le)
        (le_two_rpow_two_mul (inv_nonneg.mpr hu.le)) _) (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right (le_two_rpow_two_mul hk0) (Real.rpow_nonneg (by norm_num) _)
    _ = (2 : Real) ^ (157 * (k : Real) + 36 * k * u⁻¹) := by
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : Real) ≤ 2),
        ← Real.rpow_add (by norm_num : (0 : Real) < 2),
        ← Real.rpow_add (by norm_num : (0 : Real) < 2)]
      congr 1
      push_cast
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hbudget

end LeanProofs.GowersSzemeredi
