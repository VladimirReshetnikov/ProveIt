import GowersSzemeredi.Proofs18FejerSeedCounts

/-! This module keeps `tightZeta_fejer_one_bounds`; the rest of the development,
with its description, is in `Proofs18FejerSeedExponentsSide`, outside the final
route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The tight radius at the Fejér density: `0 < ζ′ ≤ 1` and
`ζ′⁻¹ ≤ exp(u^(2^40))`, `u = 2/(γθ)`. -/
theorem tightZeta_fejer_one_bounds {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    0 < tightZeta (fejerThetaOne theta gamma 1 / 4) ∧ tightZeta (fejerThetaOne theta gamma 1 / 4) ≤ 1 ∧
      (tightZeta (fejerThetaOne theta gamma 1 / 4))⁻¹ ≤
        Real.exp ((2 / (gamma * theta)) ^ ((2 : Nat) ^ 40)) := by
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨ha0, haS⟩ := fejerThetaOne_one_bounds ht ht1 hg hg1
  obtain ⟨hz0, hzh⟩ := tightZeta_pos_le_half ha0 (by linarith)
  refine ⟨hz0, by linarith, ?_⟩
  have hs := fejer_tightRadiusExponent_le 1 ht ht1 hg hg1
  rw [mul_comm theta gamma] at hs
  set s := tightRadiusExponent (fejerThetaOne theta gamma 1 / 4) with hsdef
  set u := 2 / (gamma * theta)
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu2
  have hs0 : 0 ≤ s := by
    rw [hsdef]; unfold tightRadiusExponent
    exact div_nonneg (by norm_num) (pow_nonneg ha0.le 11)
  have hinv : (tightZeta (fejerThetaOne theta gamma 1 / 4))⁻¹ = (2 : Real) ^ s := by
    unfold tightZeta; rw [← hsdef, Real.rpow_neg (by norm_num), inv_inv]
  rw [hinv]
  have h2e : (2 : Real) ^ s ≤ Real.exp s := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.mpr
    have hl : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : Real) < 2 by norm_num); linarith
    nlinarith
  have hE : 22 * fejerProductExponent 1 + 105 ≤ (2 : Nat) ^ 40 := by
    rw [fejerProductExponent_one]; norm_num
  calc (2 : Real) ^ s ≤ Real.exp s := h2e
    _ ≤ Real.exp (u ^ (22 * fejerProductExponent 1 + 105)) := Real.exp_le_exp.mpr hs
    _ ≤ Real.exp (u ^ ((2 : Nat) ^ 40)) :=
        Real.exp_le_exp.mpr (pow_le_pow_right₀ hu1 hE)

end LeanProofs.GowersSzemeredi
