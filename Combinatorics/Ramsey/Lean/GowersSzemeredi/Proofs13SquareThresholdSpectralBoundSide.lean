import GowersSzemeredi.Proofs13SquareThresholdSpectralBound

/-! Declarations of `Proofs13SquareThresholdSpectralBound` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- After the improved Fourier-density substitution, the final square
thresholds have a conventional double-exponential power bound. -/
theorem section13_fejer_square_thresholds_le_double_exp {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    let delta := (alpha / 2) ^ (4207554485 : Nat)
    let c := section13Zeta delta / 2
    let e := (1 : Real) / (2 : Real) ^ (13 * section13Q delta)
    let f := (2 : Real) ^ (-(100 : Int)) * delta ^ 448
    let g := cor711Exponent ((2 : Real) ^ (-(135 : Int)) * delta ^ 704) 1
    let W := (2 : Real) ^ 135 * delta ^ (-(704 : Int))
    max (squareScaleThreshold c e f g W) (squarePowerThreshold c e f g) ≤
      Real.exp (Real.exp ((2 / alpha) ^ ((2 : Nat) ^ 54))) := by
  let delta := (alpha / 2) ^ (4207554485 : Nat)
  have hδ : 0 < delta := by dsimp [delta]; positivity
  have hδone : delta ≤ 1 := pow_le_one₀ (by positivity) (by linarith only [hαone])
  apply (section13_square_thresholds_le_spectral_double_exp hδ hδone).trans
  apply Real.exp_le_exp.mpr (Real.exp_le_exp.mpr _)
  have hs := section13_fejer_spectral_upper hα hαone
  have ht : 2 ≤ 2 / alpha := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  have hQ0 : 0 ≤ section13Q delta := by
    unfold section13Q
    exact mul_nonneg (pow_nonneg (by norm_num) _) (Real.rpow_nonneg hδ.le _)
  have h8 : (8 : Real) ≤ (2 / alpha) ^ (3 : Nat) := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 2) ht 3
    norm_num at h ⊢
    exact h
  calc
    _ ≤ (8 * 15) * section13Q delta :=
      mul_le_mul_of_nonneg_right (by norm_num : (112 : Real) ≤ 8 * 15) hQ0
    _ = 8 * (15 * section13Q delta) := mul_assoc _ _ _
    _ ≤ 8 * (2 / alpha) ^ ((2 : Nat) ^ 53) :=
      mul_le_mul_of_nonneg_left hs (by norm_num)
    _ ≤ (2 / alpha) ^ (3 : Nat) * (2 / alpha) ^ ((2 : Nat) ^ 53) :=
      mul_le_mul_of_nonneg_right h8 (by positivity)
    _ = (2 / alpha) ^ (3 + (2 : Nat) ^ 53) := (pow_add _ _ _).symm
    _ ≤ _ := pow_le_pow_right₀ (by linarith only [ht]) (by norm_num)

end LeanProofs.GowersSzemeredi
