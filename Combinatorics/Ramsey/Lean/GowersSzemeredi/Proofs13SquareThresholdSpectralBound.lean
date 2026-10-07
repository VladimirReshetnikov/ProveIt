import GowersSzemeredi.Proofs13SquareThresholdEnvelope
import GowersSzemeredi.Proofs13SpectralThresholdBudgets
import GowersSzemeredi.Proofs13FejerExplicitExponent

/-! Apply the double-exponential envelope to the actual final square
thresholds, including the Fourier-density substitution. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem two_rpow_le_exp {x : Real} (hx : 0 ≤ x) : (2 : Real) ^ x ≤ Real.exp x := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  apply Real.exp_le_exp.mpr
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    linarith only [h]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hlog hx

set_option exponentiation.threshold 512 in
/-- The two final square thresholds are bounded by exp(exp(112*Q)).
The recurrence and integer-budget thresholds are separate earlier stages. -/
theorem section13_square_thresholds_le_spectral_double_exp {delta : Real}
    (hδ : 0 < delta) (hδone : delta ≤ 1) :
    let c := section13Zeta delta / 2
    let e := (1 : Real) / (2 : Real) ^ (13 * section13Q delta)
    let f := (2 : Real) ^ (-(100 : Int)) * delta ^ 448
    let g := cor711Exponent ((2 : Real) ^ (-(135 : Int)) * delta ^ 704) 1
    let W := (2 : Real) ^ 135 * delta ^ (-(704 : Int))
    max (squareScaleThreshold c e f g W) (squarePowerThreshold c e f g) ≤
      Real.exp (Real.exp (112 * section13Q delta)) := by
  dsimp only
  let Q := section13Q delta
  let A := 16 * Q
  let c := section13Zeta delta / 2
  let e := (1 : Real) / (2 : Real) ^ (13 * Q)
  let f := (2 : Real) ^ (-(100 : Int)) * delta ^ 448
  let g := cor711Exponent ((2 : Real) ^ (-(135 : Int)) * delta ^ 704) 1
  let W := (2 : Real) ^ 135 * delta ^ (-(704 : Int))
  have hQ : 4 ≤ Q := by
    have h := section13_monomial_le_Q hδ hδone (a := 2) (b := 0) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have hQ0 : 0 ≤ Q := by linarith only [hQ]
  have hA : 4 ≤ A := by dsimp [A]; linarith only [hQ]
  have hQexp : Q ≤ Real.exp A := by
    have h := Real.add_one_le_exp A
    dsimp [A] at h ⊢
    linarith only [h, hQ]
  have hc : 0 < c := by dsimp [c, section13Zeta]; positivity
  have he : 0 < e := by dsimp [e]; positivity
  have hf : 0 < f := by dsimp [f]; positivity
  have hg : 0 < g := by dsimp [g, cor711Exponent]; positivity
  have hf1 : f ≤ 1 := by
    dsimp [f]
    exact (mul_le_mul_of_nonneg_left (pow_le_one₀ hδ.le hδone (n := 448)) (by positivity)).trans (by norm_num)
  have hgform : g = (2 : Real) ^ (-(284 : Int)) * delta ^ (1408 : Nat) := by
    dsimp [g, cor711Exponent]
    norm_num [Real.rpow_neg, zpow_neg, zpow_ofNat, mul_pow, ← pow_mul]
    ring
  have hg1 : g ≤ 1 := by
    rw [hgform]
    exact (mul_le_mul_of_nonneg_left (pow_le_one₀ hδ.le hδone (n := 1408)) (by positivity)).trans (by norm_num)
  have hcI : c⁻¹ ≤ Real.exp A := by
    have hz := (section13Zeta_inv_le_spectral_exp hδ hδone).trans (two_rpow_le_exp hQ0)
    have htwo : (2 : Real) ≤ Real.exp Q := (by norm_num : (2 : Real) ≤ 8).trans (eight_le_exp_of_four_le hQ)
    calc
      _ = 2 * (section13Zeta delta)⁻¹ := by dsimp [c]; rw [inv_div, div_eq_mul_inv]
      _ ≤ Real.exp Q * Real.exp Q := mul_le_mul htwo hz (by unfold section13Zeta; positivity) (Real.exp_pos _).le
      _ = Real.exp (2 * Q) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [A]; linarith only [hQ])
  have heI : e⁻¹ ≤ Real.exp A := by
    simp only [e, one_div, inv_inv]
    exact (two_rpow_le_exp (by positivity : 0 ≤ 13 * Q)).trans
      (Real.exp_le_exp.mpr (by dsimp [A]; linarith only [hQ]))
  have hfI : f⁻¹ ≤ Real.exp A := by
    have hh : f⁻¹ = (2 : Real) ^ (100 : Nat) * (delta⁻¹) ^ (448 : Nat) := by
      dsimp [f]
      simp only [mul_inv_rev, zpow_neg, inv_inv, zpow_ofNat, inv_pow]
      exact mul_comm _ _
    rw [hh]
    exact (section13_monomial_le_Q hδ hδone (by norm_num) (by norm_num)).trans hQexp
  have hgI : g⁻¹ ≤ Real.exp A := by
    rw [hgform]
    have hh : ((2 : Real) ^ (-(284 : Int)) * delta ^ (1408 : Nat))⁻¹ =
        (2 : Real) ^ (284 : Nat) * (delta⁻¹) ^ (1408 : Nat) := by
      simp only [mul_inv_rev, zpow_neg, inv_inv, zpow_ofNat, inv_pow]
      exact mul_comm _ _
    rw [hh]
    exact (section13_monomial_le_Q hδ hδone (by norm_num) (by norm_num)).trans hQexp
  have hW : W ≤ Real.exp A := by
    have hh : W = (2 : Real) ^ (135 : Nat) * (delta⁻¹) ^ (704 : Nat) := by
      simp only [W, zpow_neg, zpow_ofNat, inv_pow]
    rw [hh]
    exact (section13_monomial_le_Q hδ hδone (by norm_num) (by norm_num)).trans hQexp
  have hs := squareScaleThreshold_le_double_exp hc he hf hg hg1 hA hcI heI hfI hgI hW
  have hp := squarePowerThreshold_le_double_exp hc he hf hf1 hg hg1 hA hcI heI hfI hgI
  change max (squareScaleThreshold c e f g W) (squarePowerThreshold c e f g) ≤ _
  apply max_le
  · apply hs.trans
    apply Real.exp_le_exp.mpr (Real.exp_le_exp.mpr _)
    dsimp [A, Q]
    linarith only [hQ]
  · convert hp using 1 <;> congr 2 <;> dsimp [A, Q] <;> ring

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
