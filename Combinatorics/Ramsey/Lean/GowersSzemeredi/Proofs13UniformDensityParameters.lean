import GowersSzemeredi.Proofs13CompleteSquareExtraction

/-! Uniform density-interval bounds for the Section 13 parameters.

`four_mul_cube_lt_two_rpow_seven`, `section13_double_recurrence_exponent_margin`
and `section13_length_exponent_mono` are in
`Proofs13UniformDensityParametersSide`, outside the final route. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The large spectral parameter decreases with the density. -/
theorem section13Q_antitone {a b : Real} (ha : 0 < a) (hab : a ≤ b) :
    section13Q b ≤ section13Q a := by
  unfold section13Q
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos ha hab (neg_nonpos.mpr (by positivity))) (by positivity)

/-- The Section 13 Bohr-length prefactor increases with the density. -/
theorem section13Zeta_mono {a b : Real} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) :
    section13Zeta a ≤ section13Zeta b := by
  have hbpos : 0 < b := ha.trans_le hab
  have hK : section13K b ≤ section13K a := by
    unfold section13K
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    change (b ^ (320 : Nat))⁻¹ ≤ (a ^ (320 : Nat))⁻¹
    exact inv_anti₀ (pow_pos ha 320) (pow_le_pow_left₀ ha.le hab 320)
  have hKa : 0 ≤ section13K a := by unfold section13K; positivity
  have htwo : (2 : Real) ^ (-(228 * section13K a)) ≤ (2 : Real) ^ (-(228 * section13K b)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hK])
  have hp : a ^ (576 * section13K a) ≤ b ^ (576 * section13K b) := by
    calc
      _ ≤ b ^ (576 * section13K a) := Real.rpow_le_rpow ha.le hab (by positivity)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hbpos hb (by linarith only [hK])
  exact mul_le_mul htwo hp (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg (by norm_num) _)

/-- The common Fourier cutoff increases with density. -/
theorem section13_cutoff_mono {a b : Real} (ha : 0 < a) (hab : a ≤ b) :
    section10Lambda (a ^ 32 / 16) ≤ section10Lambda (b ^ 32 / 16) := by
  rw [section13_lambda_formula ha, section13_lambda_formula (ha.trans_le hab)]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le hab _) (by positivity)

/-- The initial progression coefficient increases with its Fourier cutoff. -/
theorem section13ThetaOne_mono {a b : Real} (ha : 0 ≤ a) (hab : a ≤ b) :
    section13ThetaOne a ≤ section13ThetaOne b := by
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hab _) (by positivity)

/-- The allowed spectrum size decreases with its Fourier cutoff. -/
theorem section13QBound_antitone {a b : Real} (ha : 0 < a) (hab : a ≤ b) :
    section13QBound b ≤ section13QBound a := by
  unfold section13QBound
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  change (b ^ (10479 : Nat))⁻¹ ≤ (a ^ (10479 : Nat))⁻¹
  exact inv_anti₀ (pow_pos ha _) (pow_le_pow_left₀ ha.le hab _)

/-- The length prefactor is at most one throughout the density interval. -/
theorem section13Zeta_le_one {a : Real} (ha : 0 < a) (haone : a ≤ 1) :
    section13Zeta a ≤ 1 := by
  have hK : 0 ≤ section13K a := by unfold section13K; positivity
  have hfirst : (2 : Real) ^ (-(228 * section13K a)) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : Real) ≤ 2) (neg_nonpos.mpr (by positivity) : -(228 * section13K a) ≤ 0)
  have hsecond : a ^ (576 * section13K a) ≤ 1 :=
    Real.rpow_le_one ha.le haone (by positivity)
  exact mul_le_one₀ hfirst (Real.rpow_nonneg ha.le _) hsecond

end LeanProofs.GowersSzemeredi
