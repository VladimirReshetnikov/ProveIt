import GowersSzemeredi.Proofs13SpectralExponentBound
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
  have hKi : K = (2 : Real) ^ (114 : Nat) * t ^ (320 : Nat) := by
    simp only [K, section13K, t, zpow_neg, zpow_ofNat, inv_pow]
  have hK : 0 ≤ K := by rw [hKi]; positivity
  have hbudget : 228 * K + 1152 * K * t ≤ section13Q delta := by
    have hpoly : 228 * K + 1152 * K * t ≤ (2 : Real) ^ (125 : Nat) * t ^ (321 : Nat) := by
      rw [hKi]
      linarith [mul_le_mul_of_nonneg_left ht (pow_nonneg ht0 320), pow_nonneg ht0 321]
    exact hpoly.trans (section13_monomial_le_Q hδ hδone (by norm_num) (by norm_num))
  calc
    _ = (2 : Real) ^ (228 * K) * t ^ (576 * K) := by
      rw [section13Zeta, mul_inv, ← Real.rpow_neg zero_le_two, neg_neg, ← Real.inv_rpow hδ.le]
    _ ≤ (2 : Real) ^ (228 * K) * ((2 : Real) ^ (2 * t)) ^ (576 * K) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht0 (le_two_rpow_two_mul ht0)
        (mul_nonneg (by norm_num) hK)) (Real.rpow_nonneg zero_le_two _)
    _ = (2 : Real) ^ (228 * K + 1152 * K * t) := by
      rw [← Real.rpow_mul zero_le_two, ← Real.rpow_add two_pos]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le one_le_two hbudget

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
  have ht : 1 ≤ t := (one_le_inv₀ hδ).mpr hδone
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hk : (k : Real) ≤ 2 * ((2 : Real) ^ (114 : Nat) * t ^ (320 : Nat)) := by
    simpa only [section13K, t, zpow_neg, zpow_ofNat, inv_pow] using
      section10SpectrumParameter_le_two_section13K hδ hδone
  have hbudget : 157 * (k : Real) + 36 * k * u⁻¹ ≤ section13Q delta := by
    have hpoly : 157 * (k : Real) + 36 * k * u⁻¹ ≤ (2 : Real) ^ (125 : Nat) * t ^ (352 : Nat) := by
      rw [show u⁻¹ = 16 * t ^ (32 : Nat) by
        simp only [u, t]; rw [inv_div, div_eq_mul_inv, inv_pow]]
      linarith [mul_le_mul_of_nonneg_right hk (pow_nonneg ht0 32),
        pow_le_pow_right₀ ht (show 320 ≤ 352 by norm_num), pow_nonneg ht0 352]
    exact hpoly.trans (section13_monomial_le_Q hδ hδone (by norm_num) (by norm_num))
  calc
    _ = (k : Real) * (2 : Real) ^ (155 * (k : Real)) * (u⁻¹) ^ (18 * k) := by
      dsimp only [section10Zeta]
      rw [inv_div, div_eq_mul_inv, mul_inv, ← inv_pow, ← Real.rpow_neg zero_le_two, neg_mul,
        neg_neg, mul_assoc]
    _ ≤ (2 : Real) ^ (2 * (k : Real)) * (2 : Real) ^ (155 * (k : Real)) *
        ((2 : Real) ^ (2 * u⁻¹)) ^ (18 * k) := by
      gcongr <;> exact le_two_rpow_two_mul (by positivity)
    _ = (2 : Real) ^ (157 * (k : Real) + 36 * k * u⁻¹) := by
      rw [← Real.rpow_mul_natCast zero_le_two, ← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
      congr 1
      push_cast
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le one_le_two hbudget

end LeanProofs.GowersSzemeredi
