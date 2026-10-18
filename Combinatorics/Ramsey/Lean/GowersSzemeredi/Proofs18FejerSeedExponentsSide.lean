import GowersSzemeredi.Proofs18FejerSeedExponents
import GowersSzemeredi.Proofs18LengthSixExponentsSide

/-! Declarations of `Proofs18FejerSeedExponents` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- The family-cover exponent of `PolyCoverAt 2` is polynomial:
`polyTwoFejerFamExp ≥ (2/(γθρ))^(-2^46)`. -/
theorem polyTwoFejerFamExp_inv_le_power {K1 p1 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1)
    {gamma theta rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hr : 0 < rho) (hr1 : rho ≤ 1)
    (hK : (K1 : Real) ≤ (2 / (gamma * theta * rho)) ^ 3)
    (hp : (p1 : Real) ≤ (2 / (gamma * theta * rho)) ^ 3) :
    (polyTwoFejerFamExp (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) theta gamma rho)⁻¹ ≤
      (2 / (gamma * theta * rho)) ^ ((2 : Nat) ^ 46) := by
  obtain ⟨hv2, hvw, hrw⟩ := prod_scale_radius_bounds hg hg1 ht ht1 hr hr1
  obtain ⟨hζ0, hζ1, hζi⟩ := tightZeta_fejer_one_bounds hg hg1 ht ht1
  have hm := polyTwoFejerPieces_le_power hg hg1 ht ht1
  have hqs := polyPieceSpecCountW_fejer_le_power hg hg1 ht ht1
  have hqf := polyPieceFaceCountW_fejer_le_power hg hg1 ht ht1
  unfold polyTwoFejerFamExp
  dsimp only
  set ζ := tightZeta (fejerThetaOne theta gamma 1 / 4)
  set m := polyTwoFejerPieces gamma theta
  set qs := polyPieceSpecCountW (fejerThetaOne theta gamma 1)
  set qf := polyPieceFaceCountW (fejerThetaOne theta gamma 1) gamma
  set v := 2 / (gamma * theta) with hv
  set w := 2 / (gamma * theta * rho) with hw
  clear_value v w ζ m qs qf
  have hw2 : 2 ≤ w := hv2.trans hvw
  have hw1 : 1 ≤ w := le_trans (by norm_num) hw2
  have hv0 : 0 ≤ v := le_trans (by norm_num) hv2
  have hm' : (m : Real) ≤ w ^ ((2 : Nat) ^ 38) :=
    le_pow_mono hw2 (by norm_num) (hm.trans (pow_le_pow_left₀ hv0 hvw _))
  have hqs' : (qs : Real) ≤ w ^ ((2 : Nat) ^ 38) := hqs.trans (pow_le_pow_left₀ hv0 hvw _)
  have hqf' : (qf : Real) ≤ w ^ ((2 : Nat) ^ 38) := hqf.trans (pow_le_pow_left₀ hv0 hvw _)
  have hζw : ζ⁻¹ ≤ Real.exp (w ^ ((2 : Nat) ^ 40)) :=
    hζi.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ hv0 hvw _))
  have h := famTwoWidth_inv_le_power hK1 hp1 hw2 hr hr1 hrw hm' hqs' hqf' hK hp hζ0 hζ1 hζw
  exact h.trans (pow_le_pow_right₀ hw1 (by norm_num))

/-- The width exponent of `PolyCoverAt 2`: `polyTwoFejerEb ≥ (2/(γθρ))^(-2^46)`. -/
theorem polyTwoFejerEb_inv_le_power {K1 p1 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1)
    {gamma theta rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hr : 0 < rho) (hr1 : rho ≤ 1)
    (hK : (K1 : Real) ≤ (2 / (gamma * theta * rho)) ^ 3)
    (hp : (p1 : Real) ≤ (2 / (gamma * theta * rho)) ^ 3) :
    (polyTwoFejerEb (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) gamma theta rho)⁻¹ ≤
      (2 / (gamma * theta * rho)) ^ ((2 : Nat) ^ 46) := by
  obtain ⟨hv2, hvw, -⟩ := prod_scale_radius_bounds hg hg1 ht ht1 hr hr1
  have hfam := polyTwoFejerFamExp_inv_le_power hK1 hp1 hg hg1 ht ht1 hr hr1 hK hp
  have hfam0 := polyTwoFejerFamExp_pos (A := familyWidthPrefactor K1) (Bq := familyWidthDivisor 1 p1)
    (theta := theta) (gamma := gamma) (familyWidthDivisor_pos hp1) hr
  have hthr := polyTwoFejerThreshold_le_power hg hg1 ht ht1
  set v := 2 / (gamma * theta) with hv
  set w := 2 / (gamma * theta * rho) with hw
  clear_value v w
  have hw2 : 2 ≤ w := hv2.trans hvw
  have hw1 : 1 ≤ w := le_trans (by norm_num) hw2
  have hv0 : 0 ≤ v := le_trans (by norm_num) hv2
  have hthr' : polyTwoFejerThreshold theta gamma ≤ Real.exp (w ^ ((2 : Nat) ^ 15)) :=
    le_exp_pow_of_le_pow (hthr.trans (pow_le_pow_left₀ hv0 hvw _))
  unfold polyTwoFejerEb
  exact capped_inv_le_pow hw2 hfam0 (hfam.trans (pow_le_pow_right₀ hw1 (by norm_num))) hthr'
    (by norm_num)

end LeanProofs.GowersSzemeredi
