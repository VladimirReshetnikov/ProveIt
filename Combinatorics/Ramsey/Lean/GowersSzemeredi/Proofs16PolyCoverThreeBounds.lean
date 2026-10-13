import GowersSzemeredi.Proofs16PolyCoverThree
import GowersSzemeredi.Proofs16PrintedControls
import GowersSzemeredi.Proofs18LengthSixThresholds

/-! The controls of `PolyCoverAt 3` are polynomial (Notes L.5, D5).

Part A. With `u = 2/(γθ)`, the parameters of a three-dimensional piece are
powers of `u`. The bounds use the calculus of `Proofs18LengthSixCounts` and
`Proofs18LengthSixExponents`:
* `threeBudget⁻¹, threeDelta⁻¹ ≤ u^(2^133)`;
* `polyThreePieces ≤ u^(2^134)`, `threeFaceCount ≤ u^(2^149)`, and the
  dimension-two piece counts `≤ u^(2^205)`;
* `polyThreeThreshold ≤ u^(2^180)`;
* `s(θ, γ, 2) = u^(2^256)`.

Parts B and C. With `B = W₀·2/(γθρ)`, where `W₀` bounds the constants of the
family lemma in dimensions one and two:
* `polyThreeQb_le_power`: the count is at most `B^(2^321)`;
* `polyThreeEb_inv_le_power`: the width exponent is at least `B^(-2^361)`.
The dimension-two pieces are bounded in the base `B^(2^136)`, where
`Proofs16UniformCoverTwoBounds` applies.

As before, no plain `linarith` sees an exponent beyond `2^24`. -/
set_option autoImplicit false
set_option exponentiation.threshold 1024
noncomputable section
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-! ### Part A: the parameters -/

theorem thetaOne_two_inv_le {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    0 < section16ThetaOne theta gamma 2 ∧ section16ThetaOne theta gamma 2 ≤ 1 ∧
      (section16ThetaOne theta gamma 2)⁻¹ ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 129) := by
  obtain ⟨h0, h1, -, -⟩ := section16_theta_delta_bounds 2 ht ht1 hg hg1
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hq := quarter_prod_ge_inv_sq hg ht hu2
  have hq0 : 0 < theta * gamma / 4 := by positivity
  refine ⟨h0, h1, ?_⟩
  set u := 2 / (gamma * theta) with hu
  clear_value u
  have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu2
  have hqi : (theta * gamma / 4)⁻¹ ≤ u ^ 2 := by
    have := inv_anti₀ (inv_pos.mpr (pow_pos hupos 2)) hq
    rwa [inv_inv] at this
  unfold section16ThetaOne
  rw [← inv_pow, show (2 : Nat) ^ 129 = 2 * (2 : Nat) ^ ((2 : Nat) ^ (2 + 5)) by norm_num, pow_mul]
  exact pow_le_pow_left₀ (inv_pos.mpr hq0).le hqi _

theorem threeBudget_bounds {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    0 < threeBudget theta gamma ∧ threeBudget theta gamma ≤ 1 ∧
      (threeBudget theta gamma)⁻¹ ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 133) := by
  obtain ⟨hθ₂pos, hθ₂le⟩ := section16ThetaTwo_pos_le 2 ht ht1 hg hg1
  obtain ⟨t0, -, ti⟩ := thetaOne_two_inv_le hg hg1 ht ht1
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  refine ⟨by unfold threeBudget; positivity, by unfold threeBudget; linarith only [hθ₂le], ?_⟩
  set u := 2 / (gamma * theta) with hu
  clear_value u
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu2
  have hu0 : 0 ≤ u := le_trans (by norm_num) hu2
  have hval : (threeBudget theta gamma)⁻¹ =
      8 * (2 : Real) ^ (32 : Real) * ((section16ThetaOne theta gamma 2)⁻¹) ^ 8 := by
    unfold threeBudget section16ThetaTwo
    rw [Real.rpow_neg (by norm_num)]
    field_simp
  rw [hval, show (32 : Real) = ((32 : Nat) : Real) by norm_num, Real.rpow_natCast]
  have h8 : (8 : Real) * 2 ^ 32 ≤ u ^ 35 := const_le_pow hu2 (by norm_num)
  calc 8 * (2 : Real) ^ 32 * ((section16ThetaOne theta gamma 2)⁻¹) ^ 8
      ≤ u ^ 35 * (u ^ ((2 : Nat) ^ 129)) ^ 8 :=
        mul_le_mul h8 (pow_le_pow_left₀ (inv_pos.mpr t0).le ti 8) (by positivity) (pow_nonneg hu0 _)
    _ = u ^ (35 + (2 : Nat) ^ 129 * 8) := by rw [← pow_mul, ← pow_add]
    _ ≤ u ^ ((2 : Nat) ^ 133) := pow_le_pow_right₀ hu1 (by norm_num)

theorem threeDelta_bounds {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    0 < threeDelta theta gamma ∧ threeDelta theta gamma ≤ 1 ∧
      (threeDelta theta gamma)⁻¹ ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 133) := by
  obtain ⟨-, -, hd0, hd1⟩ := section16_theta_delta_bounds 2 ht ht1 hg hg1
  obtain ⟨t0, t1, ti⟩ := thetaOne_two_inv_le hg hg1 ht ht1
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  refine ⟨hd0, hd1, ?_⟩
  unfold threeDelta
  set t := section16ThetaOne theta gamma 2
  set u := 2 / (gamma * theta) with hu
  clear_value u t
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu2
  have hu0 : 0 ≤ u := le_trans (by norm_num) hu2
  have h4t1 : 1 ≤ 4 / t := by rw [le_div_iff₀ t0]; linarith only [t1]
  have h4t : 4 / t ≤ u ^ (2 + (2 : Nat) ^ 129) := by
    rw [div_eq_mul_inv, pow_add]
    exact mul_le_mul (const_le_pow hu2 (by norm_num)) ti (inv_pos.mpr t0).le (pow_nonneg hu0 _)
  have hval : (section16Delta t)⁻¹ = (2 : Real) ^ (37 : Real) * (4 / t) ^ ((11 : Real) / 2) := by
    unfold section16Delta
    rw [mul_inv, Real.rpow_neg (by norm_num), inv_inv, ← Real.inv_rpow (by positivity), inv_div]
  rw [hval]
  have h37 : (2 : Real) ^ (37 : Real) ≤ u ^ 37 := by
    rw [show (37 : Real) = ((37 : Nat) : Real) by norm_num, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by norm_num) hu2 37
  have h6 : (4 / t) ^ ((11 : Real) / 2) ≤ (4 / t) ^ 6 := by
    rw [show (4 / t) ^ 6 = (4 / t) ^ ((6 : Nat) : Real) by rw [Real.rpow_natCast]]
    exact Real.rpow_le_rpow_of_exponent_le h4t1 (by norm_num)
  calc (2 : Real) ^ (37 : Real) * (4 / t) ^ ((11 : Real) / 2)
      ≤ u ^ 37 * (u ^ (2 + (2 : Nat) ^ 129)) ^ 6 :=
        mul_le_mul h37 (h6.trans (pow_le_pow_left₀ (by positivity) h4t 6))
          (Real.rpow_nonneg (by positivity) _) (pow_nonneg hu0 _)
    _ = u ^ (37 + (2 + (2 : Nat) ^ 129) * 6) := by rw [← pow_mul, ← pow_add]
    _ ≤ u ^ ((2 : Nat) ^ 133) := pow_le_pow_right₀ hu1 (by norm_num)

/-- `2/(γ′θ′) ≤ u^(2^135)` for `γ′ ∈ {γ, δ}` and `θ′ = threeBudget θ γ`. -/
theorem two_div_three_params_le {gamma theta g' : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg' : 0 < g') (hg'i : g'⁻¹ ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 133)) :
    2 / (g' * threeBudget theta gamma) ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 135) := by
  obtain ⟨b0, -, bi⟩ := threeBudget_bounds hg hg1 ht ht1
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  set u := 2 / (gamma * theta) with hu
  clear_value u
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu2
  have hu0 : 0 ≤ u := le_trans (by norm_num) hu2
  rw [show 2 / (g' * threeBudget theta gamma) = 2 * (g'⁻¹ * (threeBudget theta gamma)⁻¹) by
    field_simp]
  have h := mul_le_pow_add (inv_pos.mpr hg').le (inv_pos.mpr b0).le hg'i bi hu0
  have h2 : 2 * (g'⁻¹ * (threeBudget theta gamma)⁻¹) ≤ u ^ (1 + ((2 : Nat) ^ 133 + (2 : Nat) ^ 133)) := by
    rw [pow_add, pow_one]
    exact mul_le_mul hu2 h (by positivity) hu0
  exact h2.trans (pow_le_pow_right₀ hu1 (by norm_num))

theorem polyThreePieces_le_power {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    (polyThreePieces gamma theta : Real) ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 134) := by
  obtain ⟨b0, b1, bi⟩ := threeBudget_bounds hg hg1 ht ht1
  obtain ⟨hu2, hginv, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hb3 : (3 * threeBudget theta gamma)⁻¹ ≤ (threeBudget theta gamma)⁻¹ :=
    inv_anti₀ b0 (by linarith only [b0])
  set u := 2 / (gamma * theta) with hu
  clear_value u
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu2
  have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu2
  have hg2 : gamma ^ (-(2 : Int)) ≤ u ^ 2 := by
    rw [zpow_neg, zpow_ofNat, ← inv_pow]
    exact pow_le_pow_left₀ (inv_pos.mpr hg).le hginv 2
  have hgz : 0 ≤ gamma ^ (-(2 : Int)) := zpow_nonneg hg.le _
  unfold polyThreePieces
  refine (Nat.floor_le (div_nonneg hgz (by positivity))).trans ?_
  calc gamma ^ (-(2 : Int)) / (3 * threeBudget theta gamma)
      ≤ gamma ^ (-(2 : Int)) * (threeBudget theta gamma)⁻¹ := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hb3 hgz
    _ ≤ u ^ 2 * u ^ ((2 : Nat) ^ 133) :=
        mul_le_mul hg2 bi (inv_pos.mpr b0).le (pow_pos hupos _).le
    _ = u ^ (2 + (2 : Nat) ^ 133) := (pow_add _ _ _).symm
    _ ≤ u ^ ((2 : Nat) ^ 134) := pow_le_pow_right₀ hu1 (by norm_num)

theorem threeFaceCount_le_power {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    (threeFaceCount theta gamma : Real) ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 149) := by
  obtain ⟨b0, b1, bi⟩ := threeBudget_bounds hg hg1 ht ht1
  obtain ⟨hu2, hginv, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hBF := section16BaseFamilyBound_le_dyadic_power hg hg1 b0 b1
  have hw := two_div_three_params_le hg hg1 ht ht1 hg
    (hginv.trans (le_self_pow₀ (le_trans (by norm_num) hu2) (by norm_num)))
  unfold threeFaceCount
  refine hBF.trans ?_
  set u := 2 / (gamma * theta) with hu
  clear_value u
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu2
  calc (2 / (gamma * threeBudget theta gamma)) ^ ((2 : Nat) ^ 14)
      ≤ (u ^ ((2 : Nat) ^ 135)) ^ ((2 : Nat) ^ 14) :=
        pow_le_pow_left₀ (by positivity) hw _
    _ = u ^ ((2 : Nat) ^ 135 * (2 : Nat) ^ 14) := (pow_mul _ _ _).symm
    _ ≤ u ^ ((2 : Nat) ^ 149) := pow_le_pow_right₀ hu1 (by norm_num)

/-- The dimension-two piece counts at `(γ′, θ′)`. -/
theorem polyTwoPieces_three_le {gamma theta g' : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg' : 0 < g') (hg'1 : g' ≤ 1)
    (hg'i : g'⁻¹ ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 133)) :
    (polyTwoPieces g' (threeBudget theta gamma) : Real) ≤
      (2 / (gamma * theta)) ^ ((2 : Nat) ^ 205) := by
  obtain ⟨b0, b1, -⟩ := threeBudget_bounds hg hg1 ht ht1
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have h := polyTwoPieces_le_power hg' hg'1 b0 b1
  have hw := two_div_three_params_le hg hg1 ht ht1 hg' hg'i
  refine h.trans ?_
  set u := 2 / (gamma * theta) with hu
  clear_value u
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu2
  calc (2 / (g' * threeBudget theta gamma)) ^ ((2 : Nat) ^ 70)
      ≤ (u ^ ((2 : Nat) ^ 135)) ^ ((2 : Nat) ^ 70) := pow_le_pow_left₀ (by positivity) hw _
    _ = u ^ ((2 : Nat) ^ 135 * (2 : Nat) ^ 70) := (pow_mul _ _ _).symm
    _ ≤ u ^ ((2 : Nat) ^ 205) := pow_le_pow_right₀ hu1 (by norm_num)

/-- The dimension-two thresholds at `(θ′, γ′)`. -/
theorem polyTwoThreshold_three_le {gamma theta g' : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg' : 0 < g') (hg'1 : g' ≤ 1)
    (hg'i : g'⁻¹ ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 133)) :
    polyTwoThreshold (threeBudget theta gamma) g' ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 180) := by
  obtain ⟨b0, b1, -⟩ := threeBudget_bounds hg hg1 ht ht1
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have h := polyTwoThreshold_le_power hg' hg'1 b0 b1
  have hw := two_div_three_params_le hg hg1 ht ht1 hg' hg'i
  refine h.trans ?_
  set u := 2 / (gamma * theta) with hu
  clear_value u
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu2
  calc (2 / (g' * threeBudget theta gamma)) ^ ((2 : Nat) ^ 45)
      ≤ (u ^ ((2 : Nat) ^ 135)) ^ ((2 : Nat) ^ 45) := pow_le_pow_left₀ (by positivity) hw _
    _ = u ^ ((2 : Nat) ^ 135 * (2 : Nat) ^ 45) := (pow_mul _ _ _).symm
    _ ≤ u ^ ((2 : Nat) ^ 180) := pow_le_pow_right₀ hu1 (by norm_num)

/-- Lemma 15.6's threshold at `k = 2`, `β = θ/2`. -/
theorem lemma156ExplicitThreshold_two_le {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    lemma156ExplicitThreshold 2 (theta / 2) gamma ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 81) := by
  obtain ⟨hu2, -, -, h1, h2⟩ := prod_scale_basic hg hg1 ht ht1
  set u := 2 / (gamma * theta) with hu
  clear_value u
  have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu2
  have hbase : (u ^ 3136)⁻¹ ≤ (theta / 2) ^ (7 * 4 ^ (2 + 1)) * gamma ^ (21 * 2 * 4 ^ (2 + 1)) := by
    have hp1 := pow_le_pow_left₀ (inv_pos.mpr hupos).le h1 (7 * 4 ^ (2 + 1))
    have hp2 := pow_le_pow_left₀ (inv_pos.mpr hupos).le h2 (21 * 2 * 4 ^ (2 + 1))
    calc (u ^ 3136)⁻¹ = u⁻¹ ^ (7 * 4 ^ (2 + 1)) * u⁻¹ ^ (21 * 2 * 4 ^ (2 + 1)) := by
          rw [← pow_add, inv_pow]; norm_num
      _ ≤ _ := mul_le_mul hp1 hp2 (by positivity) (by positivity)
  exact lemma156ExplicitThreshold_le_power_of_selection_base (by norm_num) hu2 hbase
    (by norm_num [arrangementSelectionExponent])

theorem polyThreeThreshold_le_power {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    3 ≤ polyThreeThreshold theta gamma ∧
      polyThreeThreshold theta gamma ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 180) := by
  obtain ⟨hu2, hginv, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨d0, d1, di⟩ := threeDelta_bounds hg hg1 ht ht1
  have hL := lemma156ExplicitThreshold_two_le hg hg1 ht ht1
  have hT1 := polyTwoThreshold_three_le hg hg1 ht ht1 d0 d1 di
  have hT2 := polyTwoThreshold_three_le hg hg1 ht ht1 hg hg1
    (hginv.trans (le_self_pow₀ (le_trans (by norm_num) hu2) (by norm_num)))
  set u := 2 / (gamma * theta) with hu
  clear_value u
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu2
  refine ⟨le_max_left _ _, ?_⟩
  unfold polyThreeThreshold threeThreshold
  apply max_le ((show (3 : Real) ≤ u ^ 2 by nlinarith only [hu2]).trans
    (pow_le_pow_right₀ hu1 (by norm_num)))
  exact max_le (hL.trans (pow_le_pow_right₀ hu1 (by norm_num))) (max_le hT1 hT2)

theorem multipleS_two_eq {gamma theta : Real} :
    multipleS theta gamma 2 = (2 / (gamma * theta)) ^ ((2 : Nat) ^ 256) := by
  unfold multipleS; rw [mul_comm theta gamma]; norm_num


/-! ### Part B: the controls in the base `B = W₀·2/(γθρ)` -/

/-- The elementary facts about the base `B = W₀·2/(γθρ)`. -/
theorem three_base_facts {gamma theta rho W0 : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) (hW0 : 1 ≤ W0) :
    2 ≤ W0 * (2 / (gamma * theta * rho)) ∧
      2 / (gamma * theta) ≤ W0 * (2 / (gamma * theta * rho)) ∧
      rho⁻¹ ≤ W0 * (2 / (gamma * theta * rho)) ∧ W0 ≤ W0 * (2 / (gamma * theta * rho)) := by
  obtain ⟨hv2, hvw, hrw⟩ := prod_scale_radius_bounds hg hg1 ht ht1 hr hr1
  have hw2 : 2 ≤ 2 / (gamma * theta * rho) := hv2.trans hvw
  have hle : 2 / (gamma * theta * rho) ≤ W0 * (2 / (gamma * theta * rho)) :=
    le_mul_of_one_le_left (by positivity) hW0
  refine ⟨hw2.trans hle, hvw.trans hle, hrw.trans hle, ?_⟩
  exact le_mul_of_one_le_right (by linarith) (by linarith)

/-- The Bohr radius of a three-dimensional piece: `ζ₂⁻¹ ≤ exp(u^(2^256))`. -/
theorem section16Zeta_two_bounds {gamma theta : Real} (hg : 0 < gamma) (ht : 0 < theta) :
    0 < section16Zeta theta gamma 2 ∧ section16Zeta theta gamma 2 ≤ 1 ∧
      (section16Zeta theta gamma 2)⁻¹ ≤ Real.exp ((2 / (gamma * theta)) ^ ((2 : Nat) ^ 256)) := by
  have hm0 : 0 ≤ multipleS theta gamma 2 := by rw [multipleS_two_eq]; positivity
  unfold section16Zeta
  refine ⟨Real.rpow_pos_of_pos (by norm_num) _, ?_, ?_⟩
  · exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith only [hm0])
  · rw [Real.rpow_neg (by norm_num), inv_inv, Real.rpow_def_of_pos (by norm_num), ← multipleS_two_eq]
    apply Real.exp_le_exp.mpr
    have h : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith only [this]
    calc Real.log 2 * multipleS theta gamma 2 ≤ 1 * multipleS theta gamma 2 :=
          mul_le_mul_of_nonneg_right h hm0
      _ = multipleS theta gamma 2 := one_mul _

/-- **The count control of `PolyCoverAt 3` is polynomial.** -/
theorem polyThreeQb_le_power {K1 p1 : Nat} {gamma theta rho W0 : Real} (hg : 0 < gamma)
    (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1)
    (hW0 : 1 ≤ W0) (hK : (K1 : Real) ≤ W0) (hp : (p1 : Real) ≤ W0) :
    polyThreeQb K1 p1 gamma theta rho ≤ (W0 * (2 / (gamma * theta * rho))) ^ ((2 : Nat) ^ 321) := by
  obtain ⟨hB2, huB, hrB, hWB⟩ := three_base_facts hg hg1 ht ht1 hr hr1 hW0
  obtain ⟨hu2, hginv, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨b0, b1, bi⟩ := threeBudget_bounds hg hg1 ht ht1
  have hginv' : gamma⁻¹ ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 133) :=
    hginv.trans (le_self_pow₀ (le_trans (by norm_num) hu2) (by norm_num))
  have hm := polyThreePieces_le_power hg hg1 ht ht1
  have hmf := polyTwoPieces_three_le hg hg1 ht ht1 hg hg1 hginv'
  have hq3 := threeFaceCount_le_power hg hg1 ht ht1
  obtain ⟨-, hthr⟩ := polyThreeThreshold_le_power hg hg1 ht ht1
  have hvF := two_div_three_params_le hg hg1 ht ht1 hg hginv'
  -- abstract the base
  set u := 2 / (gamma * theta) with hu
  set B := W0 * (2 / (gamma * theta * rho)) with hBdef
  set tF := threeBudget theta gamma with htF
  set m := polyThreePieces gamma theta
  set mf := polyTwoPieces gamma tF
  set q3 := threeFaceCount theta gamma
  clear_value u B
  have hB1 : 1 ≤ B := le_trans (by norm_num) hB2
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB2
  have hu0 : 0 ≤ u := le_trans (by norm_num) hu2
  have lift : ∀ (x : Real) (n : Nat), x ≤ u ^ n → x ≤ B ^ n := fun x n h =>
    h.trans (pow_le_pow_left₀ hu0 huB n)
  have hm' := lift _ _ hm
  have hmf' := lift _ _ hmf
  have hq3' := lift _ _ hq3
  have hthr' := lift _ _ hthr
  have hvF' := lift _ _ hvF
  -- the dimension-two base `w₂ = B^(2^136)`
  set w2 := B ^ ((2 : Nat) ^ 136) with hw2def
  have hw2B : ∀ n : Nat, n ≤ (2 : Nat) ^ 136 → B ^ n ≤ w2 := fun n hn => pow_le_pow_right₀ hB1 hn
  have hvw2 : 2 / (gamma * tF) ≤ w2 := hvF'.trans (hw2B _ (by norm_num))
  have hr32 : (rho / 8 / 4)⁻¹ ≤ w2 := by
    rw [show (rho / 8 / 4)⁻¹ = 32 * rho⁻¹ by field_simp; ring]
    have h : 32 * rho⁻¹ ≤ B ^ 5 * B ^ 1 := by
      rw [pow_one]; exact mul_le_mul (const_le_pow hB2 (by norm_num)) hrB (inv_pos.mpr hr).le
        (pow_nonneg hB0 _)
    rw [← pow_add] at h
    exact h.trans (hw2B _ (by norm_num))
  have hMf : ((m * mf : Nat) : Real) ≤ w2 ^ ((2 : Nat) ^ 84) := by
    have h := nat_mul_le_pow hB2 hm' hmf'
    refine h.trans ?_
    rw [hw2def, ← pow_mul]
    exact pow_le_pow_right₀ hB1 (by norm_num)
  -- the face counts `Q₁ = Q₂`
  have hQ1 : uniTwoCount tF gamma (m * mf) (rho / 8 / 4) ≤ B ^ ((2 : Nat) ^ 225) := by
    have h := uniTwoCount_le_power hg hg1 b0 b1 (by positivity) (by linarith only [hr1]) hvw2 hr32 hMf
    refine h.trans ?_
    rw [hw2def, ← pow_mul]
    exact pow_le_pow_right₀ hB1 (by norm_num)
  have h27 : ((3 ^ (2 + 1) * (m * mf) : Nat) : Real) ≤ B ^ ((2 : Nat) ^ 225) := by
    rw [Nat.cast_mul]
    exact le_pow_mono hB2 (by norm_num) (const_mul_le_pow (j := 5) hB2 (by positivity) (by norm_num)
      (Nat.cast_nonneg _) (nat_mul_le_pow hB2 hm' hmf'))
  have hmax1 : max (uniTwoCount tF gamma (m * mf) (rho / 8 / 4))
      ((3 ^ (2 + 1) * (m * mf) : Nat) : Real) ≤ B ^ ((2 : Nat) ^ 225) := max_le hQ1 h27
  have hmq3 : ((m * q3 + 1 : Nat) : Real) ≤ B ^ ((2 : Nat) ^ 134 + (2 : Nat) ^ 149 + 1) := by
    have h := nat_mul_le_pow hB2 hm' hq3'
    push_cast; push_cast at h
    exact add_le_pow_succ hB2 h (one_le_pow_of_two_le hB2 _)
  have hmax3 : max (max ((3 * (m * q3 + 1) : Nat) : Real) ((3 ^ (1 + 1) * (m * q3 + 1) : Nat) : Real))
      ((3 ^ (2 + 1) * (m * q3 + 1) : Nat) : Real) ≤ B ^ ((2 : Nat) ^ 225) := by
    have hc : ∀ c : Nat, (c : Real) ≤ 2 ^ 5 → ((c * (m * q3 + 1) : Nat) : Real) ≤ B ^ ((2 : Nat) ^ 225) := by
      intro c hc
      rw [Nat.cast_mul]
      exact le_pow_mono hB2 (by norm_num) (const_mul_le_pow (j := 5) hB2 (Nat.cast_nonneg _) hc
        (Nat.cast_nonneg _) hmq3)
    exact max_le (max_le (hc 3 (by norm_num)) (hc _ (by norm_num))) (hc _ (by norm_num))
  -- the remainder count `famThreeQr` at `ρ/8`
  have hQr : famThreeQr tF gamma q3 m (rho / 8) ≤ B ^ ((2 : Nat) ^ 227) := by
    show (max (uniTwoCount tF gamma (m * mf) (rho / 8 / 4)) ((3 ^ (2 + 1) * (m * mf) : Nat) : Real) *
        max (uniTwoCount tF gamma (m * mf) (rho / 8 / 4)) ((3 ^ (2 + 1) * (m * mf) : Nat) : Real)) *
      max (max ((3 * (m * q3 + 1) : Nat) : Real) ((3 ^ (1 + 1) * (m * q3 + 1) : Nat) : Real))
        ((3 ^ (2 + 1) * (m * q3 + 1) : Nat) : Real) ≤ _
    have h0 : 0 ≤ max (uniTwoCount tF gamma (m * mf) (rho / 8 / 4)) ((3 ^ (2 + 1) * (m * mf) : Nat) : Real) :=
      le_max_of_le_right (Nat.cast_nonneg _)
    have h00 : 0 ≤ max (max ((3 * (m * q3 + 1) : Nat) : Real) ((3 ^ (1 + 1) * (m * q3 + 1) : Nat) : Real))
        ((3 ^ (2 + 1) * (m * q3 + 1) : Nat) : Real) := le_max_of_le_right (Nat.cast_nonneg _)
    have h := mul_le_pow_add (mul_nonneg h0 h0) h00 (mul_le_pow_add h0 h0 hmax1 hmax1 hB0) hmax3 hB0
    exact h.trans (pow_le_pow_right₀ hB1 (by norm_num))
  -- samples, slice counts and the graph bound
  have hS := famPieceSamples_le_power (Qr := famThreeQr tF gamma q3 m) hB2 hr hrB hQr hm'
  set Sp := famPieceSamples (famThreeQr tF gamma q3 m) m rho
  have hbase : threeSliceBase tF gamma K1 p1 (m * Sp) (rho / 4) ≤ B ^ ((2 : Nat) ^ 229) := by
    unfold threeSliceBase
    rw [abs_of_pos (by positivity : (0 : Real) < rho / 4)]
    have hmS : ((m * Sp : Nat) : Real) + 1 ≤ B ^ ((2 : Nat) ^ 134 + ((2 : Nat) ^ 227 + (2 : Nat) ^ 134 + 7) + 1) := by
      have h := nat_mul_le_pow hB2 hm' hS
      exact add_le_pow_succ hB2 h (one_le_pow_of_two_le hB2 _)
    have hmf1 : (mf : Real) + 1 ≤ B ^ ((2 : Nat) ^ 205 + 1) :=
      add_le_pow_succ hB2 hmf' (one_le_pow_of_two_le hB2 _)
    have hKp : (K1 : Real) + p1 + 1 ≤ B ^ 3 := by
      have h3 : (3 : Real) * W0 ≤ B ^ 3 := by
        rw [pow_succ]
        exact mul_le_mul (const_le_pow hB2 (by norm_num)) hWB (by linarith only [hW0]) (pow_nonneg hB0 _)
      linarith only [h3, hK, hp, hW0]
    have hrho : 2 / (gamma * tF * (rho / 4)) ≤ B ^ ((2 : Nat) ^ 135 + 3) := by
      rw [show 2 / (gamma * tF * (rho / 4)) = 2 / (gamma * tF) * (4 * rho⁻¹) by field_simp,
        pow_add]
      have h4 : 4 * rho⁻¹ ≤ B ^ 2 * B ^ 1 := by
        rw [pow_one]; exact mul_le_mul (const_le_pow hB2 (by norm_num)) hrB (inv_pos.mpr hr).le (pow_nonneg hB0 _)
      rw [← pow_add] at h4
      exact mul_le_mul hvF' h4 (by positivity) (pow_nonneg hB0 _)
    have hpos1 : (0 : Real) ≤ ((m * Sp : Nat) : Real) + 1 := by positivity
    have hpos2 : (0 : Real) ≤ (mf : Real) + 1 := by positivity
    have hpos3 : (0 : Real) ≤ (K1 : Real) + p1 + 1 := by positivity
    have h := mul_le_pow_add (mul_nonneg (mul_nonneg hpos1 hpos2) hpos3) (by positivity)
      (mul_le_pow_add (mul_nonneg hpos1 hpos2) hpos3 (mul_le_pow_add hpos1 hpos2 hmS hmf1 hB0) hKp hB0)
      hrho hB0
    push_cast at h ⊢
    exact h.trans (pow_le_pow_right₀ hB1 (by norm_num))
  have hP : famThreePb tF gamma K1 p1 m Sp (rho / 4) ≤ B ^ ((2 : Nat) ^ 318) := by
    show threeSliceBase tF gamma K1 p1 (m * Sp) (rho / 4) ^ ((2 : Nat) ^ 89) ≤ _
    have h0 : 0 ≤ threeSliceBase tF gamma K1 p1 (m * Sp) (rho / 4) := by
      unfold threeSliceBase; positivity
    refine (pow_le_pow_left₀ h0 hbase _).trans ?_
    rw [← pow_mul]
    exact pow_le_pow_right₀ hB1 (by norm_num)
  have hP0 : 0 ≤ famThreePb tF gamma K1 p1 m Sp (rho / 4) := by
    show 0 ≤ threeSliceBase tF gamma K1 p1 (m * Sp) (rho / 4) ^ ((2 : Nat) ^ 89)
    apply pow_nonneg; unfold threeSliceBase; positivity
  have hG := famPieceGraphBound_le_power (Qr := famThreeQr tF gamma q3 m)
    (Pb := famThreePb tF gamma K1 p1 m) hB2 hm' hS hP0 hP
  -- the count control
  unfold polyThreeQb polyThreeFamCount
  apply max_le (max_le (hG.trans (pow_le_pow_right₀ hB1 (by norm_num))) ?_)
  · have h3thr := (polyThreeThreshold_le_power hg hg1 ht ht1).1
    have hceil := ceil_le_pow_succ hB2 (by linarith only [h3thr]) hthr'
    rw [Nat.cast_mul]
    exact le_pow_mono hB2 (by norm_num) (const_mul_le_pow (j := 5) hB2 (by positivity) (by norm_num)
      (Nat.cast_nonneg _) hceil)
  · rw [Nat.cast_mul]
    exact le_pow_mono hB2 (by norm_num) (const_mul_le_pow (j := 5) hB2 (by positivity) (by norm_num)
      (Nat.cast_nonneg _) hm')

/-! ### Part C: the width exponent -/

/-- **The width exponent of `PolyCoverAt 3` is polynomial.** -/
theorem polyThreeEb_inv_le_power {K1 p1 C2 p2 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1)
    (hC2 : 1 ≤ C2) (hp2 : 0 < p2) {gamma theta rho W0 : Real} (hg : 0 < gamma)
    (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1)
    (hW0 : 1 ≤ W0) (hK : (K1 : Real) ≤ W0) (hp : (p1 : Real) ≤ W0) (hC : (C2 : Real) ≤ W0)
    (hq : (p2 : Real) ≤ W0) :
    0 < polyThreeEb (familyWidthPrefactor C2) (familyWidthDivisor 2 p2) K1 p1 gamma theta rho ∧
    (polyThreeEb (familyWidthPrefactor C2) (familyWidthDivisor 2 p2) K1 p1 gamma theta rho)⁻¹ ≤
      (W0 * (2 / (gamma * theta * rho))) ^ ((2 : Nat) ^ 361) := by
  have hB2' : ∀ q, 0 < familyWidthDivisor 2 p2 q := familyWidthDivisor_pos hp2
  have hB1' : ∀ q, 0 < familyWidthDivisor 1 p1 q := familyWidthDivisor_pos hp1
  have hfam0 := polyThreeFamExp_pos (A2 := familyWidthPrefactor C2) hB2' (K1 := K1) hp1 ht ht1 hg hg1
    hr hr1
  obtain ⟨hB2, huB, hrB, hWB⟩ := three_base_facts hg hg1 ht ht1 hr hr1 hW0
  obtain ⟨hu2, hginv, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨b0, b1, bi⟩ := threeBudget_bounds hg hg1 ht ht1
  obtain ⟨d0, d1, di⟩ := threeDelta_bounds hg hg1 ht ht1
  obtain ⟨z0, z1, zi⟩ := section16Zeta_two_bounds hg ht
  have hginv' : gamma⁻¹ ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 133) :=
    hginv.trans (le_self_pow₀ (le_trans (by norm_num) hu2) (by norm_num))
  have hm := polyThreePieces_le_power hg hg1 ht ht1
  have hmf := polyTwoPieces_three_le hg hg1 ht ht1 hg hg1 hginv'
  have hms := polyTwoPieces_three_le hg hg1 ht ht1 d0 d1 di
  have hq3 := threeFaceCount_le_power hg hg1 ht ht1
  obtain ⟨h3thr, hthr⟩ := polyThreeThreshold_le_power hg hg1 ht ht1
  have hvF := two_div_three_params_le hg hg1 ht ht1 hg hginv'
  have hvS := two_div_three_params_le hg hg1 ht ht1 d0 di
  set u := 2 / (gamma * theta) with hu
  set B := W0 * (2 / (gamma * theta * rho)) with hBdef
  set tF := threeBudget theta gamma with htF
  set δ := threeDelta theta gamma with hδ
  set m := polyThreePieces gamma theta
  set mf := polyTwoPieces gamma tF
  set ms := polyTwoPieces δ tF
  set q3 := threeFaceCount theta gamma
  clear_value u B
  have hB1 : 1 ≤ B := le_trans (by norm_num) hB2
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB2
  have hu0 : 0 ≤ u := le_trans (by norm_num) hu2
  have lift : ∀ (x : Real) (n : Nat), x ≤ u ^ n → x ≤ B ^ n := fun x n h =>
    h.trans (pow_le_pow_left₀ hu0 huB n)
  have hm' := lift _ _ hm
  have hmf' := lift _ _ hmf
  have hms' := lift _ _ hms
  have hq3' := lift _ _ hq3
  have hthr' := lift _ _ hthr
  have hvF' := lift _ _ hvF
  have hvS' := lift _ _ hvS
  have hzi' : (section16Zeta theta gamma 2)⁻¹ ≤ Real.exp (B ^ ((2 : Nat) ^ 256)) :=
    zi.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ hu0 huB _))
  -- the dimension-two base
  set w2 := B ^ ((2 : Nat) ^ 136) with hw2def
  have hw2B : ∀ n : Nat, n ≤ (2 : Nat) ^ 136 → B ^ n ≤ w2 := fun n hn => pow_le_pow_right₀ hB1 hn
  have hvw2F : 2 / (gamma * tF) ≤ w2 := hvF'.trans (hw2B _ (by norm_num))
  have hvw2S : 2 / (δ * tF) ≤ w2 := hvS'.trans (hw2B _ (by norm_num))
  have hrc : ∀ c : Real, c ≤ 2 ^ 5 → c * rho⁻¹ ≤ w2 := by
    intro c hc
    have h : c * rho⁻¹ ≤ B ^ 5 * B ^ 1 := by
      rw [pow_one]; exact mul_le_mul (const_le_pow hB2 hc) hrB (inv_pos.mpr hr).le (pow_nonneg hB0 _)
    rw [← pow_add] at h
    exact h.trans (hw2B _ (by norm_num))
  have hr8 : (rho / 8)⁻¹ ≤ w2 := by
    rw [show (rho / 8)⁻¹ = 8 * rho⁻¹ by field_simp]; exact hrc 8 (by norm_num)
  have hr32 : (rho / 8 / 4)⁻¹ ≤ w2 := by
    rw [show (rho / 8 / 4)⁻¹ = 32 * rho⁻¹ by field_simp; ring]; exact hrc 32 (by norm_num)
  have hM : ∀ x : Nat, (x : Real) ≤ B ^ ((2 : Nat) ^ 205) →
      ((m * x : Nat) : Real) ≤ w2 ^ ((2 : Nat) ^ 84) := by
    intro x hx
    refine (nat_mul_le_pow hB2 hm' hx).trans ?_
    rw [hw2def, ← pow_mul]
    exact pow_le_pow_right₀ hB1 (by norm_num)
  have hKw : (K1 : Real) ≤ w2 ^ 3 :=
    hK.trans (hWB.trans ((hw2B 1 (by norm_num) |>.trans' (by rw [pow_one])).trans
      (le_self_pow₀ (le_trans hB1 (hw2B 1 (by norm_num) |>.trans' (by rw [pow_one]))) (by norm_num))))
  have hpw : (p1 : Real) ≤ w2 ^ 3 :=
    hp.trans (hWB.trans ((hw2B 1 (by norm_num) |>.trans' (by rw [pow_one])).trans
      (le_self_pow₀ (le_trans hB1 (hw2B 1 (by norm_num) |>.trans' (by rw [pow_one]))) (by norm_num))))
  have hw2pow : ∀ n : Nat, w2 ^ n = B ^ ((2 : Nat) ^ 136 * n) := fun n => by rw [hw2def, ← pow_mul]
  -- the spectrum count and exponent at `ρ/8`
  have hQb : famThreeQb tF δ m (rho / 8) ≤ B ^ ((2 : Nat) ^ 225) := by
    have h := uniTwoCount_le_power d0 d1 b0 b1 (by positivity) (by linarith only [hr1]) hvw2S hr8
      (hM ms hms')
    exact h.trans (by rw [hw2pow]; exact pow_le_pow_right₀ hB1 (by norm_num))
  have hEb : (famThreeEb (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) tF δ m (rho / 8))⁻¹ ≤
      B ^ ((2 : Nat) ^ 266) := by
    have h := uniTwoExp_inv_le_power hK1 hp1 d0 d1 b0 b1 (by positivity) (by linarith only [hr1])
      hvw2S hr8 (hM ms hms') hKw hpw
    exact h.trans (by rw [hw2pow]; exact pow_le_pow_right₀ hB1 (by norm_num))
  have hEb0 : 0 < famThreeEb (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) tF δ m (rho / 8) :=
    uniTwoExp_pos hB1' _ (by positivity)
  -- the remainder exponent at `ρ/8`
  have hE1 : (uniTwoExp (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) tF gamma (m * mf)
      (rho / 8 / 4))⁻¹ ≤ B ^ ((2 : Nat) ^ 266) := by
    have h := uniTwoExp_inv_le_power hK1 hp1 hg hg1 b0 b1 (by positivity) (by linarith only [hr1])
      hvw2F hr32 (hM mf hmf') hKw hpw
    exact h.trans (by rw [hw2pow]; exact pow_le_pow_right₀ hB1 (by norm_num))
  have hE10 : 0 < uniTwoExp (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) tF gamma (m * mf)
      (rho / 8 / 4) := uniTwoExp_pos hB1' _ (by positivity)
  have hmq3 : ((m * q3 + 1 : Nat) : Real) ≤ B ^ ((2 : Nat) ^ 134 + (2 : Nat) ^ 149 + 1) := by
    have h := nat_mul_le_pow hB2 hm' hq3'
    push_cast; push_cast at h
    exact add_le_pow_succ hB2 h (one_le_pow_of_two_le hB2 _)
  have hr16 : (rho / 8 / 2)⁻¹ ≤ B ^ 5 := by
    rw [show (rho / 8 / 2)⁻¹ = 16 * rho⁻¹ by field_simp; ring, show (5 : Nat) = 4 + 1 from rfl,
      pow_add, pow_one]
    exact mul_le_mul (const_le_pow hB2 (by norm_num)) hrB (inv_pos.mpr hr).le (pow_nonneg hB0 _)
  have hcub := cubicBaseExponent_inv_le hB2 (Nat.succ_pos (m * q3)) hmq3 (by positivity) hr16
  have hcub0 := cubicBaseExponent_pos (Nat.succ_pos (m * q3)) (show 0 < rho / 8 / 2 by positivity)
  set E := uniTwoExp (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) tF gamma (m * mf)
    (rho / 8 / 4) with hEdef
  set c := cubicBaseExponent (m * q3 + 1) (rho / 8 / 2) with hcdef
  have hErval : famThreeEr (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) tF gamma q3 m
      (rho / 8) = E / 16 * (E / 16) * (c / 16 / 16) := rfl
  have hEr0 : 0 < famThreeEr (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) tF gamma q3 m
      (rho / 8) := by
    rw [hErval]
    exact mul_pos (mul_pos (div_pos hE10 (by norm_num)) (div_pos hE10 (by norm_num)))
      (div_pos (div_pos hcub0 (by norm_num)) (by norm_num))
  have hEr : (famThreeEr (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) tF gamma q3 m
      (rho / 8))⁻¹ ≤ B ^ ((2 : Nat) ^ 268) := by
    rw [hErval, show (E / 16 * (E / 16) * (c / 16 / 16))⁻¹ = 16 ^ 4 * (E⁻¹ * (E⁻¹ * c⁻¹)) by
      field_simp]
    have h := mul_le_pow_add (inv_pos.mpr hE10).le (mul_nonneg (inv_pos.mpr hE10).le
      (inv_pos.mpr hcub0).le) hE1 (mul_le_pow_add (inv_pos.mpr hE10).le (inv_pos.mpr hcub0).le
        hE1 hcub hB0) hB0
    have h2 := const_mul_le_pow (c := (16 : Real) ^ 4) (j := 16) hB2 (by norm_num) (by norm_num)
      (mul_nonneg (inv_pos.mpr hE10).le (mul_nonneg (inv_pos.mpr hE10).le (inv_pos.mpr hcub0).le)) h
    exact h2.trans (pow_le_pow_right₀ hB1 (by norm_num))
  -- the line exponent
  have hfl : ((⌊famThreeQb tF δ m (rho / 8)⌋₊ : Nat) : Real) ≤ B ^ ((2 : Nat) ^ 225) :=
    (Nat.floor_le (uniTwoCount_nonneg _ _ _ _)).trans hQb
  have hfl1 : ((⌊famThreeQb tF δ m (rho / 8)⌋₊ + 1 : Nat) : Real) ≤ B ^ ((2 : Nat) ^ 225 + 1) := by
    rw [Nat.cast_succ]; exact add_le_pow_succ hB2 hfl (one_le_pow_of_two_le hB2 _)
  have hBq : familyWidthDivisor 2 p2 ⌊famThreeQb tF δ m (rho / 8)⌋₊ ≤ B ^ ((2 : Nat) ^ 230) := by
    have hval : familyWidthDivisor 2 p2 ⌊famThreeQb tF δ m (rho / 8)⌋₊ =
        8 * ((p2 : Real) * ((⌊famThreeQb tF δ m (rho / 8)⌋₊ + 1 : Nat) : Real) ^ 16) := by
      unfold familyWidthDivisor; push_cast; ring
    rw [hval]
    have h16 : ((⌊famThreeQb tF δ m (rho / 8)⌋₊ + 1 : Nat) : Real) ^ 16 ≤
        B ^ (((2 : Nat) ^ 225 + 1) * 16) := by
      rw [pow_mul]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) hfl1 16
    have h := mul_le_pow_add (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
      (show (p2 : Real) ≤ B ^ 1 by rw [pow_one]; exact hq.trans hWB) h16 hB0
    exact (const_mul_le_pow (j := 3) hB2 (by norm_num) (by norm_num) (by positivity) h).trans
      (pow_le_pow_right₀ hB1 (by norm_num))
  set L := pieceLineExponent (familyWidthDivisor 2 p2) (famThreeQb tF δ m)
    (famThreeEb (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) tF δ m)
    (famThreeEr (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) tF gamma q3 m) rho with hLdef
  have hL0 : 0 < L := by
    rw [hLdef]; unfold pieceLineExponent
    exact div_pos (mul_pos hEr0 hEb0) (hB2' _)
  have hLi : L⁻¹ ≤ B ^ ((2 : Nat) ^ 269) := by
    rw [hLdef]; unfold pieceLineExponent
    rw [inv_div, div_eq_mul_inv, mul_inv]
    have h := mul_le_pow_add (hB2' _).le (mul_nonneg (inv_pos.mpr hEr0).le (inv_pos.mpr hEb0).le)
      hBq (mul_le_pow_add (inv_pos.mpr hEr0).le (inv_pos.mpr hEb0).le hEr hEb hB0) hB0
    exact h.trans (pow_le_pow_right₀ hB1 (by norm_num))
  -- the slice exponent
  have hQr : famThreeQr tF gamma q3 m (rho / 8) ≤ B ^ ((2 : Nat) ^ 227) := by
    have hQ1 : uniTwoCount tF gamma (m * mf) (rho / 8 / 4) ≤ B ^ ((2 : Nat) ^ 225) := by
      have h := uniTwoCount_le_power hg hg1 b0 b1 (by positivity) (by linarith only [hr1]) hvw2F
        hr32 (hM mf hmf')
      exact h.trans (by rw [hw2pow]; exact pow_le_pow_right₀ hB1 (by norm_num))
    have h27 : ((3 ^ (2 + 1) * (m * mf) : Nat) : Real) ≤ B ^ ((2 : Nat) ^ 225) := by
      rw [Nat.cast_mul]
      exact le_pow_mono hB2 (by norm_num) (const_mul_le_pow (j := 5) hB2 (by positivity)
        (by norm_num) (Nat.cast_nonneg _) (nat_mul_le_pow hB2 hm' hmf'))
    have hmax1 := max_le hQ1 h27
    have hmax3 : max (max ((3 * (m * q3 + 1) : Nat) : Real) ((3 ^ (1 + 1) * (m * q3 + 1) : Nat) : Real))
        ((3 ^ (2 + 1) * (m * q3 + 1) : Nat) : Real) ≤ B ^ ((2 : Nat) ^ 225) := by
      have hc : ∀ c : Nat, (c : Real) ≤ 2 ^ 5 →
          ((c * (m * q3 + 1) : Nat) : Real) ≤ B ^ ((2 : Nat) ^ 225) := by
        intro c hc
        rw [Nat.cast_mul]
        exact le_pow_mono hB2 (by norm_num) (const_mul_le_pow (j := 5) hB2 (Nat.cast_nonneg _) hc
          (Nat.cast_nonneg _) hmq3)
      exact max_le (max_le (hc 3 (by norm_num)) (hc _ (by norm_num))) (hc _ (by norm_num))
    show (max (uniTwoCount tF gamma (m * mf) (rho / 8 / 4)) ((3 ^ (2 + 1) * (m * mf) : Nat) : Real) *
        max (uniTwoCount tF gamma (m * mf) (rho / 8 / 4)) ((3 ^ (2 + 1) * (m * mf) : Nat) : Real)) *
      max (max ((3 * (m * q3 + 1) : Nat) : Real) ((3 ^ (1 + 1) * (m * q3 + 1) : Nat) : Real))
        ((3 ^ (2 + 1) * (m * q3 + 1) : Nat) : Real) ≤ _
    have h0 : 0 ≤ max (uniTwoCount tF gamma (m * mf) (rho / 8 / 4)) ((3 ^ (2 + 1) * (m * mf) : Nat) : Real) :=
      le_max_of_le_right (Nat.cast_nonneg _)
    have h00 : 0 ≤ max (max ((3 * (m * q3 + 1) : Nat) : Real) ((3 ^ (1 + 1) * (m * q3 + 1) : Nat) : Real))
        ((3 ^ (2 + 1) * (m * q3 + 1) : Nat) : Real) := le_max_of_le_right (Nat.cast_nonneg _)
    have h := mul_le_pow_add (mul_nonneg h0 h0) h00 (mul_le_pow_add h0 h0 hmax1 hmax1 hB0) hmax3 hB0
    exact h.trans (pow_le_pow_right₀ hB1 (by norm_num))
  have hS := famPieceSamples_le_power (Qr := famThreeQr tF gamma q3 m) hB2 hr hrB hQr hm'
  set Sp := famPieceSamples (famThreeQr tF gamma q3 m) m rho
  have hbase : threeSliceBase tF gamma K1 p1 (m * Sp) (rho / 4) ≤ B ^ ((2 : Nat) ^ 229) := by
    unfold threeSliceBase
    rw [abs_of_pos (by positivity : (0 : Real) < rho / 4)]
    have hmS : ((m * Sp : Nat) : Real) + 1 ≤
        B ^ ((2 : Nat) ^ 134 + ((2 : Nat) ^ 227 + (2 : Nat) ^ 134 + 7) + 1) := by
      have h := nat_mul_le_pow hB2 hm' hS
      exact add_le_pow_succ hB2 h (one_le_pow_of_two_le hB2 _)
    have hmf1 : (mf : Real) + 1 ≤ B ^ ((2 : Nat) ^ 205 + 1) :=
      add_le_pow_succ hB2 hmf' (one_le_pow_of_two_le hB2 _)
    have hKp : (K1 : Real) + p1 + 1 ≤ B ^ 3 := by
      have h3 : (3 : Real) * W0 ≤ B ^ 3 := by
        rw [pow_succ]
        exact mul_le_mul (const_le_pow hB2 (by norm_num)) hWB (by linarith only [hW0]) (pow_nonneg hB0 _)
      linarith only [h3, hK, hp, hW0]
    have hrho : 2 / (gamma * tF * (rho / 4)) ≤ B ^ ((2 : Nat) ^ 135 + 3) := by
      rw [show 2 / (gamma * tF * (rho / 4)) = 2 / (gamma * tF) * (4 * rho⁻¹) by field_simp,
        pow_add]
      have h4 : 4 * rho⁻¹ ≤ B ^ 3 := by
        rw [pow_succ]
        exact mul_le_mul (const_le_pow hB2 (by norm_num)) hrB (inv_pos.mpr hr).le (pow_nonneg hB0 _)
      exact mul_le_mul hvF' h4 (by positivity) (pow_nonneg hB0 _)
    have hpos1 : (0 : Real) ≤ ((m * Sp : Nat) : Real) + 1 := by positivity
    have hpos2 : (0 : Real) ≤ (mf : Real) + 1 := by positivity
    have hpos3 : (0 : Real) ≤ (K1 : Real) + p1 + 1 := by positivity
    have h := mul_le_pow_add (mul_nonneg (mul_nonneg hpos1 hpos2) hpos3) (by positivity)
      (mul_le_pow_add (mul_nonneg hpos1 hpos2) hpos3 (mul_le_pow_add hpos1 hpos2 hmS hmf1 hB0) hKp hB0)
      hrho hB0
    push_cast at h ⊢
    exact h.trans (pow_le_pow_right₀ hB1 (by norm_num))
  have hbase2 : 2 ≤ threeSliceBase tF gamma K1 p1 (m * Sp) (rho / 4) :=
    threeSliceBase_two_le b0 b1 hg hg1 K1 p1 (m * Sp) (by positivity) (by linarith only [hr1])
  set S := famPieceSliceExponent (famThreeQr tF gamma q3 m) (famThreeEs tF gamma K1 p1 m) m rho
    with hSdef
  have hSval : S = (threeSliceBase tF gamma K1 p1 (m * Sp) (rho / 4) ^ ((2 : Nat) ^ 130))⁻¹ := by
    rw [hSdef]; rfl
  have hS0 : 0 < S := by rw [hSval]; exact inv_pos.mpr (pow_pos (by linarith only [hbase2]) _)
  have hS1 : S ≤ 1 := by
    rw [hSval]; exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith only [hbase2]))
  have hSi : S⁻¹ ≤ B ^ ((2 : Nat) ^ 359) := by
    rw [hSval, inv_inv]
    refine (pow_le_pow_left₀ (by linarith only [hbase2]) hbase _).trans ?_
    rw [← pow_mul]
    exact pow_le_pow_right₀ hB1 (by norm_num)
  -- the scale
  have hA : familyWidthPrefactor C2 ⌊famThreeQb tF δ m (rho / 8)⌋₊ ≤ B ^ ((2 : Nat) ^ 226) := by
    unfold familyWidthPrefactor
    rw [Nat.cast_mul]
    have h := mul_le_pow_add (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (show (C2 : Real) ≤ B ^ 1 by rw [pow_one]; exact hC.trans hWB) hfl1 hB0
    exact (const_mul_le_pow (j := 2) hB2 (by norm_num) (by norm_num) (by positivity) h).trans
      (pow_le_pow_right₀ hB1 (by norm_num))
  have hA1 : 1 ≤ familyWidthPrefactor C2 ⌊famThreeQb tF δ m (rho / 8)⌋₊ := by
    unfold familyWidthPrefactor
    have : (1 : Real) ≤ ((C2 * (⌊famThreeQb tF δ m (rho / 8)⌋₊ + 1) : Nat) : Real) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    linarith only [this]
  set z := pieceWidthScale (familyWidthPrefactor C2) (famThreeQb tF δ m)
    (section16Zeta theta gamma 2) rho with hzdef
  have hzval : z = section16Zeta theta gamma 2 / familyWidthPrefactor C2 ⌊famThreeQb tF δ m (rho / 8)⌋₊ :=
    by rw [hzdef]; rfl
  have hz0 : 0 < z := by rw [hzval]; exact div_pos z0 (lt_of_lt_of_le zero_lt_one hA1)
  have hz1 : z ≤ 1 := by
    rw [hzval, div_le_one (lt_of_lt_of_le zero_lt_one hA1)]; exact z1.trans hA1
  have hzi : z⁻¹ ≤ Real.exp (B ^ ((2 : Nat) ^ 256 + 1)) := by
    rw [hzval, inv_div, div_eq_mul_inv]
    have hAe : familyWidthPrefactor C2 ⌊famThreeQb tF δ m (rho / 8)⌋₊ ≤ Real.exp (B ^ ((2 : Nat) ^ 256)) :=
      le_exp_pow_of_le_pow (le_pow_mono hB2 (by norm_num) hA)
    exact exp_mul_le hB2 (inv_pos.mpr z0).le hAe hzi'
  -- the two caps
  have hfam : (polyThreeFamExp (familyWidthPrefactor C2) (familyWidthDivisor 2 p2) K1 p1 theta gamma
      rho)⁻¹ ≤ B ^ ((2 : Nat) ^ 360) := by
    have h := capped_rounded_inv_le hB2 (show 6 ≤ (2 : Nat) ^ 256 + 1 by norm_num) hL0 hLi hS0 hS1
      hSi hz0 hz1 hzi
    unfold polyThreeFamExp
    exact h.trans (pow_le_pow_right₀ hB1 (by norm_num))
  have hthre : polyThreeThreshold theta gamma ≤ Real.exp (B ^ ((2 : Nat) ^ 180)) :=
    le_exp_pow_of_le_pow hthr'
  unfold polyThreeEb
  exact ⟨section16CappedWidthExponent_pos hfam0,
    capped_inv_le_pow hB2 hfam0 (hfam.trans (pow_le_pow_right₀ hB1 (by norm_num))) hthre
      (by norm_num)⟩
end LeanProofs.GowersSzemeredi
