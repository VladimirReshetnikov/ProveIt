import GowersSzemeredi.Proofs18LengthSixExponents
import GowersSzemeredi.Proofs18LengthSixCountsSide

/-! Declarations of `Proofs18LengthSixExponents` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false
set_option exponentiation.threshold 1024

noncomputable section

namespace LeanProofs.GowersSzemeredi

section
open BaseCase

/-- `δ(θ₁)⁻¹ ≤ (2/(γθ))^(2^68)` for `δ = section16Delta`. -/
theorem section16Delta_one_inv_le {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    (section16Delta (section16ThetaOne theta gamma 1))⁻¹ ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 68) := by
  obtain ⟨hu, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨h0, h1, -, -⟩ := section16_theta_delta_bounds 1 ht ht1 hg hg1
  exact (section16Delta_inv_le_pw hu (by norm_num) h0 h1
    (section16ThetaOne_one_inv_le hg hg1 ht ht1))

/-- The spectrum count `polyPieceSpecCount θ γ ≤ (2/(γθ))^(2^84)`. -/
theorem polyPieceSpecCount_le_power {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    (polyPieceSpecCount theta gamma : Real) ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 84) := by
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨-, -, hd0, hd1⟩ := section16_theta_delta_bounds 1 ht ht1 hg hg1
  obtain ⟨hb, hb1⟩ := polyPieceBudget_pos_le hg hg1 ht ht1
  have hdi := section16Delta_one_inv_le hg hg1 ht ht1
  have hbi := polyPieceBudget_inv_le_power hg hg1 ht ht1
  have hBF := section16BaseFamilyBound_le_dyadic_power hd0 hd1 hb hb1
  unfold polyPieceSpecCount
  set d := section16Delta (section16ThetaOne theta gamma 1)
  set b := polyPieceBudget theta gamma
  set u := 2 / (gamma * theta) with hu
  clear_value u d b
  have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu2
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu2
  have hbase : 2 / (d * b) ≤ u ^ (1 + ((2 : Nat) ^ 68 + (2 : Nat) ^ 69)) := by
    rw [show 2 / (d * b) = 2 * (d⁻¹ * b⁻¹) by field_simp, pow_add, pow_one, pow_add]
    exact mul_le_mul hu2 (mul_le_mul hdi hbi (inv_pos.mpr hb).le (pow_nonneg hupos.le _))
      (mul_nonneg (inv_pos.mpr hd0).le (inv_pos.mpr hb).le) hupos.le
  refine hBF.trans ?_
  calc (2 / (d * b)) ^ ((2 : Nat) ^ 14)
      ≤ (u ^ (1 + ((2 : Nat) ^ 68 + (2 : Nat) ^ 69))) ^ ((2 : Nat) ^ 14) :=
        pow_le_pow_left₀ (div_pos (by norm_num) (mul_pos hd0 hb)).le hbase _
    _ = u ^ ((1 + ((2 : Nat) ^ 68 + (2 : Nat) ^ 69)) * (2 : Nat) ^ 14) := (pow_mul _ _ _).symm
    _ ≤ u ^ ((2 : Nat) ^ 84) := pow_le_pow_right₀ hu1 (by norm_num)

/-- The family-cover exponent of `PolyCoverAt 2` is polynomial:
`polyTwoFamExp ≥ (2/(γθρ))^(-2^130)`. -/
theorem polyTwoFamExp_inv_le_power {K1 p1 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1)
    {gamma theta rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hr : 0 < rho) (hr1 : rho ≤ 1)
    (hK : (K1 : Real) ≤ (2 / (gamma * theta * rho)) ^ 3)
    (hp : (p1 : Real) ≤ (2 / (gamma * theta * rho)) ^ 3) :
    (polyTwoFamExp (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) theta gamma rho)⁻¹ ≤
      (2 / (gamma * theta * rho)) ^ ((2 : Nat) ^ 130) := by
  obtain ⟨hv2, hvw, hrw⟩ := prod_scale_radius_bounds hg hg1 ht ht1 hr hr1
  obtain ⟨hζ0, hζ1, hζi⟩ := section16Zeta_one_bounds hg ht
  have hm := polyTwoPieces_le_power hg hg1 ht ht1
  have hqs := polyPieceSpecCount_le_power hg hg1 ht ht1
  have hqf := polyPieceFaceCount_le_power hg hg1 ht ht1
  unfold polyTwoFamExp
  dsimp only
  set ζ := section16Zeta theta gamma 1
  set m := polyTwoPieces gamma theta
  set qs := polyPieceSpecCount theta gamma
  set qf := polyPieceFaceCount theta gamma
  set v := 2 / (gamma * theta) with hv
  set w := 2 / (gamma * theta * rho) with hw
  clear_value v w ζ m qs qf
  have hw2 : 2 ≤ w := hv2.trans hvw
  have hw1 : 1 ≤ w := le_trans (by norm_num) hw2
  have hv0 : 0 ≤ v := le_trans (by norm_num) hv2
  have hm' : (m : Real) ≤ w ^ ((2 : Nat) ^ 84) :=
    le_pow_mono hw2 (by norm_num) (hm.trans (pow_le_pow_left₀ hv0 hvw _))
  have hqs' : (qs : Real) ≤ w ^ ((2 : Nat) ^ 84) := hqs.trans (pow_le_pow_left₀ hv0 hvw _)
  have hqf' : (qf : Real) ≤ w ^ ((2 : Nat) ^ 84) := hqf.trans (pow_le_pow_left₀ hv0 hvw _)
  have hζw : ζ⁻¹ ≤ Real.exp (w ^ ((2 : Nat) ^ 128)) :=
    hζi.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ hv0 hvw _))
  have h := famTwoWidth_inv_le_power hK1 hp1 hw2 hr hr1 hrw hm' hqs' hqf' hK hp hζ0 hζ1 hζw
  exact h.trans (pow_le_pow_right₀ hw1 (by norm_num))

/-- The width exponent of `PolyCoverAt 2`: `polyTwoEb ≥ (2/(γθρ))^(-2^132)`. -/
theorem polyTwoEb_inv_le_power {K1 p1 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1)
    {gamma theta rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hr : 0 < rho) (hr1 : rho ≤ 1)
    (hK : (K1 : Real) ≤ (2 / (gamma * theta * rho)) ^ 3)
    (hp : (p1 : Real) ≤ (2 / (gamma * theta * rho)) ^ 3) :
    (polyTwoEb (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) gamma theta rho)⁻¹ ≤
      (2 / (gamma * theta * rho)) ^ ((2 : Nat) ^ 132) := by
  obtain ⟨hv2, hvw, -⟩ := prod_scale_radius_bounds hg hg1 ht ht1 hr hr1
  have hfam := polyTwoFamExp_inv_le_power hK1 hp1 hg hg1 ht ht1 hr hr1 hK hp
  have hfam0 := polyTwoFamExp_pos (A := familyWidthPrefactor K1) (Bq := familyWidthDivisor 1 p1)
    (theta := theta) (gamma := gamma) (familyWidthDivisor_pos hp1) hr
  have hthr := polyTwoThreshold_le_power hg hg1 ht ht1
  set v := 2 / (gamma * theta) with hv
  set w := 2 / (gamma * theta * rho) with hw
  clear_value v w
  have hw2 : 2 ≤ w := hv2.trans hvw
  have hw1 : 1 ≤ w := le_trans (by norm_num) hw2
  have hv0 : 0 ≤ v := le_trans (by norm_num) hv2
  have hthr' : polyTwoThreshold theta gamma ≤ Real.exp (w ^ ((2 : Nat) ^ 45)) :=
    le_exp_pow_of_le_pow (hthr.trans (pow_le_pow_left₀ hv0 hvw _))
  unfold polyTwoEb
  exact capped_inv_le_pow hw2 hfam0 (hfam.trans (pow_le_pow_right₀ hw1 (by norm_num))) hthr'
    (by norm_num)

/-- **The width exponents of the length-six route are polynomial**:
`(sixEb A Bq l γ θ ρ)⁻¹ ≤ (2/(γθρ))^(2^132)` once `K₁, p₁ ≤ (2/(γθρ))³`. -/
theorem sixEb_inv_le_power (l : Nat) {K1 p1 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1)
    {gamma theta rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hr : 0 < rho) (hr1 : rho ≤ 1)
    (hK : (K1 : Real) ≤ (2 / (gamma * theta * rho)) ^ 3)
    (hp : (p1 : Real) ≤ (2 / (gamma * theta * rho)) ^ 3) :
    (sixEb (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) l gamma theta rho)⁻¹ ≤
      (2 / (gamma * theta * rho)) ^ ((2 : Nat) ^ 132) := by
  unfold sixEb
  split_ifs
  · obtain ⟨hv2, hvw, hrw⟩ := prod_scale_radius_bounds hg hg1 ht ht1 hr hr1
    have hB := section16BaseFamilyBound_le_dyadic_power hg hg1 ht ht1
    have hB0 := section16BaseFamilyBound_pos gamma theta
    set v := 2 / (gamma * theta) with hv
    set w := 2 / (gamma * theta * rho) with hw
    clear_value v w
    have hw2 : 2 ≤ w := hv2.trans hvw
    have hv0 : 0 ≤ v := le_trans (by norm_num) hv2
    have hB' : (section16BaseFamilyBound gamma theta : Real) ≤ w ^ ((2 : Nat) ^ 14) :=
      hB.trans (pow_le_pow_left₀ hv0 hvw _)
    show (cubicBaseExponent (section16BaseFamilyBound gamma theta) rho)⁻¹ ≤ _
    have hrw1 : rho⁻¹ ≤ w ^ 1 := by rw [pow_one]; exact hrw
    exact le_pow_mono hw2 (by norm_num) (cubicBaseExponent_inv_le hw2 hB0 hB' hr hrw1)
  · exact polyTwoEb_inv_le_power hK1 hp1 hg hg1 ht ht1 hr hr1 hK hp

end

end LeanProofs.GowersSzemeredi
