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
  have hs0 : 0 ≤ tightRadiusExponent (fejerThetaOne theta gamma 1 / 4) :=
    div_nonneg (by norm_num) (pow_nonneg ha0.le 11)
  have hs := fejer_tightRadiusExponent_le 1 ht ht1 hg hg1
  rw [mul_comm theta gamma] at hs
  unfold tightZeta
  rw [Real.rpow_neg zero_le_two, inv_inv]
  calc _ ≤ Real.exp (tightRadiusExponent (fejerThetaOne theta gamma 1 / 4)) :=
        (Real.rpow_le_rpow zero_le_two (by linarith only [Real.add_one_le_exp 1]) hs0).trans_eq
          (Real.exp_one_rpow _)
    _ ≤ _ := Real.exp_le_exp.mpr (hs.trans (pow_le_pow_right₀ (by linarith only [hu2])
        (by rw [fejerProductExponent_one]; norm_num)))

end LeanProofs.GowersSzemeredi
