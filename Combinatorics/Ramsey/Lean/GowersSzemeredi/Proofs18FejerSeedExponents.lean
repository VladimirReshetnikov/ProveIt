import GowersSzemeredi.Proofs18FejerSeedCounts

/-! **The dimension-two cover's controls under the Fejér θ₁ and the tight
radius** (Notes L.16d).

The Fejér analogue of the length-six count and exponent bounds, in the base
`w = 2/(γθρ)`:
* `polyTwoFejerFamCount_le_power`: `≤ w^(2^43)` (printed `2^89`);
* `polyTwoFejerQb_le_power`: `≤ w^(2^44)` (printed `2^90`);
* `polyTwoFejerFamExp_inv_le_power`: `≤ w^(2^46)` (printed `2^130`);
* `polyTwoFejerEb_inv_le_power`: `≤ w^(2^46)` (printed `2^132`).

The printed width exponent was dominated by the Bohr radius
(`ζ⁻¹ ≤ exp(w^(2^128))`). Under the tight radius
(`tightZeta_fejer_one_bounds`: `ζ′⁻¹ ≤ exp(u^(2^40))`, from
`s′ ≤ u^(22E+105)`) the counts dominate. So the dimension-two seed of the
split-class recursion has degree about `2^46`, inside the `2^48` of
`split_pair_with_bounds_fourteen`.

The proofs are the corpus proofs with the new exponents, copied by a script
with a guard that no printed quantity survives. -/
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
  set u := 2 / (gamma * theta) with hu
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

theorem polyTwoFejerFamCount_le_power {gamma theta rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) :
    polyTwoFejerFamCount theta gamma rho ≤ (2 / (gamma * theta * rho)) ^ ((2 : Nat) ^ 43) := by
  obtain ⟨hv2, hvw, hrw⟩ := prod_scale_radius_bounds hg hg1 ht ht1 hr hr1
  have hm := polyTwoFejerPieces_le_power hg hg1 ht ht1
  have hq := polyPieceFaceCountW_fejer_le_power hg hg1 ht ht1
  set v := 2 / (gamma * theta) with hv
  set w := 2 / (gamma * theta * rho) with hw
  clear_value v w
  have hw2 : 2 ≤ w := hv2.trans hvw
  have hv0 : 0 ≤ v := le_trans (by norm_num) hv2
  -- both counts below `w^(2^38)`
  have hm' : (polyTwoFejerPieces gamma theta : Real) ≤ w ^ ((2 : Nat) ^ 38) :=
    le_pow_mono hw2 (by norm_num) (hm.trans (pow_le_pow_left₀ hv0 hvw _))
  have hq' : (polyPieceFaceCountW (fejerThetaOne theta gamma 1) gamma : Real) ≤ w ^ ((2 : Nat) ^ 38) :=
    hq.trans (pow_le_pow_left₀ hv0 hvw _)
  unfold polyTwoFejerFamCount
  exact le_pow_mono hw2 (by norm_num) (famTwoCount_le_power hw2 hr hrw hm' hq')

/-! ### The counts of the length-six route -/

/-- `polyTwoFejerQb γ θ ρ ≤ (2/(γθρ))^(2^44)`. -/
theorem polyTwoFejerQb_le_power {gamma theta rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) :
    polyTwoFejerQb gamma theta rho ≤ (2 / (gamma * theta * rho)) ^ ((2 : Nat) ^ 44) := by
  obtain ⟨hv2, hvw, -⟩ := prod_scale_radius_bounds hg hg1 ht ht1 hr hr1
  have hthr3 : (3 : Real) ≤ polyTwoFejerThreshold theta gamma := by
    unfold polyTwoFejerThreshold; exact le_max_left _ _
  have hthr := polyTwoFejerThreshold_le_power hg hg1 ht ht1
  have hfam := polyTwoFejerFamCount_le_power hg hg1 ht ht1 hr hr1
  set v := 2 / (gamma * theta) with hv
  set w := 2 / (gamma * theta * rho) with hw
  clear_value v w
  have hw2 : 2 ≤ w := hv2.trans hvw
  have hv0 : 0 ≤ v := le_trans (by norm_num) hv2
  have hthr' : polyTwoFejerThreshold theta gamma ≤ w ^ ((2 : Nat) ^ 15) :=
    hthr.trans (pow_le_pow_left₀ hv0 hvw _)
  have hceil := ceil_le_pow_succ hw2 (le_trans (by norm_num) hthr3) hthr'
  unfold polyTwoFejerQb
  apply max_le
  · exact le_pow_mono hw2 (by norm_num) hfam
  · rw [Nat.cast_mul]
    exact le_pow_mono hw2 (by norm_num)
      (const_mul_le_pow (j := 4) hw2 (Nat.cast_nonneg _) (by norm_num) (Nat.cast_nonneg _) hceil)


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
