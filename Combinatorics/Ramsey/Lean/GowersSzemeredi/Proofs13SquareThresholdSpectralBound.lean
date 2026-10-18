import GowersSzemeredi.Proofs13SquareThresholdEnvelope
import GowersSzemeredi.Proofs13SpectralThresholdBudgets
import GowersSzemeredi.Proofs13FejerExplicitExponent

/-! Apply the double-exponential envelope to the actual final square
thresholds, including the Fourier-density substitution.

`section13_fejer_square_thresholds_le_double_exp` is in
`Proofs13SquareThresholdSpectralBoundSide`, outside the final route. -/
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
  intro c e f g W
  set Q := section13Q delta with hQdef
  have hQ : 1 ≤ Q := by
    simpa using section13_monomial_le_Q hδ hδone (a := 0) (b := 0) (by norm_num) (by norm_num)
  -- every reciprocal parameter is a monomial in `1/δ`, hence at most `Q ≤ exp (16 Q)`
  have hmono (a b : Nat) (ha : a ≤ 2 ^ 20) (hb : b ≤ 2 ^ 21) :
      ((2 : Real) ^ (-(a : Int)) * delta ^ b)⁻¹ ≤ Real.exp (16 * Q) := by
    rw [mul_inv, zpow_neg, inv_inv, zpow_natCast, ← inv_pow]
    exact (section13_monomial_le_Q hδ hδone ha hb).trans
      (by linarith [Real.add_one_le_exp (16 * Q)])
  have hζ : 0 < section13Zeta delta := by unfold section13Zeta; positivity
  have hgform : g = (2 : Real) ^ (-(284 : Int)) * delta ^ (1408 : Nat) := by
    dsimp [g, cor711Exponent]
    norm_num [Real.rpow_neg, zpow_neg, zpow_ofNat, mul_pow, ← pow_mul]
    ring
  have hf1 : f ≤ 1 :=
    (mul_le_mul_of_nonneg_left (pow_le_one₀ hδ.le hδone) (by positivity)).trans (by norm_num)
  have hg1 : g ≤ 1 := by
    rw [hgform]
    exact (mul_le_mul_of_nonneg_left (pow_le_one₀ hδ.le hδone) (by positivity)).trans (by norm_num)
  have hcI : c⁻¹ ≤ Real.exp (16 * Q) := by
    have hc : c⁻¹ = 2 * (section13Zeta delta)⁻¹ := by simp only [c]; rw [inv_div, div_eq_mul_inv]
    rw [hc, show 16 * Q = Q + 15 * Q by ring, Real.exp_add]
    exact mul_le_mul (by linarith [Real.add_one_le_exp Q])
      ((section13Zeta_inv_le_spectral_exp hδ hδone).trans ((two_rpow_le_exp (by linarith)).trans
        (Real.exp_le_exp.mpr (by linarith)))) (inv_nonneg.mpr hζ.le) (Real.exp_pos _).le
  have heI : e⁻¹ ≤ Real.exp (16 * Q) := by
    simp only [e, one_div, inv_inv]
    exact (two_rpow_le_exp (by positivity)).trans (Real.exp_le_exp.mpr (by linarith))
  have hfI : f⁻¹ ≤ Real.exp (16 * Q) := hmono 100 448 (by norm_num) (by norm_num)
  have hgI : g⁻¹ ≤ Real.exp (16 * Q) := by
    rw [hgform]; exact hmono 284 1408 (by norm_num) (by norm_num)
  have hW : W ≤ Real.exp (16 * Q) := by
    convert hmono 135 704 (by norm_num) (by norm_num) using 1
    simp only [W, mul_inv, zpow_neg, inv_inv, zpow_natCast, zpow_ofNat]
  have hc : 0 < c := half_pos hζ
  have he : 0 < e := by positivity
  have hf : 0 < f := by positivity
  have hg : 0 < g := by rw [hgform]; positivity
  have hA : 4 ≤ 16 * Q := by linarith
  refine max_le ((squareScaleThreshold_le_double_exp hc he hf hg hg1 hA hcI heI hfI hgI hW).trans
    (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by linarith))))
    ((squarePowerThreshold_le_double_exp hc he hf hf1 hg hg1 hA hcI heI hfI hgI).trans_eq ?_)
  ring_nf

end LeanProofs.GowersSzemeredi
