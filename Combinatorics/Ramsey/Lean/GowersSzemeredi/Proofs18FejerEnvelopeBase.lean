import GowersSzemeredi.Proofs18GenericThresholds
import GowersSzemeredi.Proofs16SinglePieceCoverGlobalWith
import GowersSzemeredi.Proofs16ClassStepBoundsFejer
import GowersSzemeredi.Proofs16RadiusComparison

/-! **The fixed parameters of the Section 18 step under the Fejér θ₁**
(Notes L.16d).

The Section 18 envelope bounds the fixed parameters of dimension `k` at
`X = 2/α` (`Proofs18GenericEnvelopeBase`, `lemma156_gen_le`). The Fejér
density is at least the printed one,
`section16ThetaOne α (α/2) k ≤ fejerThetaOne α (α/2) k`
(`section16ThetaOne_le_fejer`, from `fejerProductExponent k ≤ 2^(2^(k+5))`),
and the budget, `θ₂/2`, `δ` and the radius are monotone in it. So each
printed bound transfers, at the same exponent:
* `budget_gen_bounds_fejer`, `T2_gen_bounds_fejer`, `delta_gen_bounds_fejer`
  (`X^(2^fixDeg k)`);
* `zeta_gen_bounds_fejer`: `tightZeta(θ₁′/4) ≥ section16Zeta`, because the
  tight exponent `2^83/(θ₁′/4)^11` is at most `2^83/(θ₁/4)^11 ≤ multipleS`
  (`section16_radius_exponent_budget`);
* `lemma156_gen_le_fejer`: the Fejér Lemma 15.6 threshold is at most
  `X^(2·fejerStepP k) ≤ X^(2^(2^(k+4)+4k+13))`, the printed slot.

The envelope then changes only through the class degree (`uDeg23` in place
of `uDeg68`). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem fejerProductExponent_le_printed (k : Nat) :
    fejerProductExponent k ≤ (2 : Nat) ^ ((2 : Nat) ^ (k + 5)) := by
  refine (fejerProductExponent_le k).trans (Nat.pow_le_pow_right (by norm_num) ?_)
  have h1 : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  have h2 : 2 ^ (k + 5) = 32 * 2 ^ k := by rw [pow_add]; ring
  omega

/-- **The Fejér density is at least the printed one.** -/
theorem section16ThetaOne_le_fejer {theta gamma : Real} (k : Nat) (ht : 0 < theta)
    (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    section16ThetaOne theta gamma k ≤ fejerThetaOne theta gamma k := by
  unfold section16ThetaOne fejerThetaOne
  have h0 : 0 ≤ theta * gamma / 4 := by positivity
  have h1 : theta * gamma / 4 ≤ 1 := by nlinarith
  exact pow_le_pow_of_le_one h0 h1 (fejerProductExponent_le_printed k)

theorem section16ThetaTwo_mono {s t : Real} (hs : 0 ≤ s) (hst : s ≤ t) :
    section16ThetaTwo s ≤ section16ThetaTwo t := by
  unfold section16ThetaTwo
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hst 8) (by positivity)

theorem section16Delta_mono {s t : Real} (hs : 0 ≤ s) (hst : s ≤ t) :
    section16Delta s ≤ section16Delta t := by
  unfold section16Delta
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (div_nonneg hs (by norm_num)) (div_le_div_of_nonneg_right hst (by norm_num))
      (by norm_num)) (by positivity)

section Fixed

variable {alpha : Real}

theorem fejer_theta_ge_printed (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    section16ThetaOne alpha (alpha / 2) k ≤ fejerThetaOne alpha (alpha / 2) k :=
  section16ThetaOne_le_fejer k ha (by linarith) (half_pos ha) (by linarith)

theorem fejer_alpha_bounds (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < fejerThetaOne alpha (alpha / 2) k / 4 ∧ fejerThetaOne alpha (alpha / 2) k / 4 ≤ 1 / 36 :=
  fejerThetaOne_bounds k ha (by linarith) (half_pos ha) (by linarith)

theorem budget_gen_bounds_fejer (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k ∧
      globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k ≤ 1 ∧
      (globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k)⁻¹ ≤ (2 / alpha) ^ (2 ^ fixDeg k) := by
  obtain ⟨hfa0, hfaS⟩ := fejer_alpha_bounds k ha ha2
  obtain ⟨h0, h1⟩ := section16ThetaTwo_pos_le_with hfa0 hfaS
  obtain ⟨p0, -, pi⟩ := budget_gen_bounds k ha ha2
  have hden : (1 : Real) ≤ 2 * (2 ^ k + 1) := by
    have : (1 : Real) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    linarith
  have hle : globalBudget alpha (alpha / 2) k ≤ globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k := by
    unfold globalBudget globalBudgetW
    exact div_le_div_of_nonneg_right (section16ThetaTwo_mono (thetaOne_gen_bounds k ha ha2).1.le
      (fejer_theta_ge_printed k ha ha2)) (by positivity)
  refine ⟨lt_of_lt_of_le p0 hle, ?_, (inv_anti₀ p0 hle).trans pi⟩
  unfold globalBudgetW
  rw [div_le_one (by positivity)]
  linarith

theorem T2_gen_bounds_fejer (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < globalTheta2W (fejerThetaOne alpha (alpha / 2) k) ∧
      globalTheta2W (fejerThetaOne alpha (alpha / 2) k) ≤ 1 ∧
      (globalTheta2W (fejerThetaOne alpha (alpha / 2) k))⁻¹ ≤ (2 / alpha) ^ (2 ^ fixDeg k) := by
  obtain ⟨hfa0, hfaS⟩ := fejer_alpha_bounds k ha ha2
  obtain ⟨h0, h1⟩ := globalTheta2W_pos_le hfa0 hfaS
  obtain ⟨p0, -, pi⟩ := T2_gen_bounds k ha ha2
  have hle : globalTheta2 alpha (alpha / 2) k ≤ globalTheta2W (fejerThetaOne alpha (alpha / 2) k) := by
    unfold globalTheta2 globalTheta2W
    exact div_le_div_of_nonneg_right (section16ThetaTwo_mono (thetaOne_gen_bounds k ha ha2).1.le
      (fejer_theta_ge_printed k ha ha2)) (by norm_num)
  exact ⟨h0, h1, (inv_anti₀ p0 hle).trans pi⟩

theorem delta_gen_bounds_fejer (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < section16Delta (fejerThetaOne alpha (alpha / 2) k) ∧
      section16Delta (fejerThetaOne alpha (alpha / 2) k) ≤ 1 ∧
      (section16Delta (fejerThetaOne alpha (alpha / 2) k))⁻¹ ≤ (2 / alpha) ^ (2 ^ fixDeg k) := by
  obtain ⟨hfa0, hfaS⟩ := fejer_alpha_bounds k ha ha2
  obtain ⟨-, -, d0, d1⟩ := section16_theta_delta_bounds_with hfa0 hfaS
  obtain ⟨p0, -, pi⟩ := delta_gen_bounds k ha ha2
  have hle : section16Delta (section16ThetaOne alpha (alpha / 2) k) ≤
      section16Delta (fejerThetaOne alpha (alpha / 2) k) :=
    section16Delta_mono (thetaOne_gen_bounds k ha ha2).1.le (fejer_theta_ge_printed k ha ha2)
  exact ⟨d0, d1, (inv_anti₀ p0 hle).trans pi⟩

/-- The tight radius at the Fejér density is at least the printed radius. -/
theorem section16Zeta_le_tight_fejer (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    section16Zeta alpha (alpha / 2) k ≤ tightZeta (fejerThetaOne alpha (alpha / 2) k / 4) := by
  have ha1 : alpha ≤ 1 := by linarith
  obtain ⟨t0, -, -⟩ := thetaOne_gen_bounds k ha ha2
  have hge := fejer_theta_ge_printed k ha ha2
  have hbud := section16_radius_exponent_budget k ha ha1 (half_pos ha) (by linarith)
  have hq0 : 0 < section16ThetaOne alpha (alpha / 2) k / 4 := by positivity
  have hpow : (section16ThetaOne alpha (alpha / 2) k / 4) ^ 11 ≤
      (fejerThetaOne alpha (alpha / 2) k / 4) ^ 11 :=
    pow_le_pow_left₀ hq0.le (div_le_div_of_nonneg_right hge (by norm_num)) 11
  have hexp : tightRadiusExponent (fejerThetaOne alpha (alpha / 2) k / 4) ≤
      multipleS alpha (alpha / 2) k := by
    unfold tightRadiusExponent
    refine le_trans ?_ hbud
    exact div_le_div_of_nonneg_left (by positivity) (pow_pos hq0 11) hpow
  unfold section16Zeta tightZeta
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg hexp)

theorem zeta_gen_bounds_fejer (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < tightZeta (fejerThetaOne alpha (alpha / 2) k / 4) ∧
      (tightZeta (fejerThetaOne alpha (alpha / 2) k / 4))⁻¹ ≤
        Real.exp ((2 / alpha) ^ (2 ^ (2 ^ (k + 6) + 1))) := by
  obtain ⟨z0, zi⟩ := zeta_gen_bounds k ha ha2
  have hle := section16Zeta_le_tight_fejer k ha ha2
  exact ⟨lt_of_lt_of_le z0 hle, (inv_anti₀ z0 hle).trans zi⟩

/-- **The Fejér Lemma 15.6 threshold in the printed slot.** -/
theorem lemma156_gen_le_fejer {k : Nat} (hk : 1 ≤ k) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    fejerProductThreshold k (alpha / 2) (alpha / 2) ≤
      (2 / alpha) ^ (2 ^ (2 ^ (k + 4) + 4 * k + 13)) := by
  have ha1 : alpha ≤ 1 := by linarith
  have hX := two_div_ge_two ha ha2
  have h := fejerProductThreshold_le_gen (gamma := alpha / 2) (theta := alpha) hk (half_pos ha)
    (by linarith) ha ha1
  have hu : 2 / (alpha / 2 * alpha) = (2 / alpha) ^ 2 := by field_simp
  rw [hu, ← pow_mul] at h
  refine h.trans (pow_le_pow_right₀ (le_trans (by norm_num) hX) ?_)
  have hP := fejerStepP_le k
  have hk2 : 5 * k + 21 ≤ 2 ^ (k + 4) + 4 * k + 13 := by
    have h1 : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
    have h16 : 2 ^ (k + 4) = 16 * 2 ^ k := by rw [pow_add]; ring
    omega
  calc 2 * fejerStepP k ≤ 2 * 2 ^ (5 * k + 20) := Nat.mul_le_mul_left 2 hP
    _ = 2 ^ (5 * k + 21) := by rw [pow_succ]; ring
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hk2

/-- The base slice density at the Fejér budget (`GenParams.baseC` with
`globalBudgetW` in place of `globalBudget`). -/
def baseCF (V : Real) (D k : Nat) (alpha : Real) : Real → Real :=
  fun s => s / 2 / uCount V D (alpha / 2) (globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k) (s / 2)

/-- **The Fejér base density is a reciprocal power** (`GenParams.baseC_recipPowerLB`). -/
theorem baseCF_recipPowerLB {V : Real} {D k μV μ0 : Nat} (ha : 0 < alpha)
    (ha2 : alpha ≤ 1 / 2) (hV : 1 ≤ V) (hVμ : V ≤ 2 ^ (2 ^ μV))
    (hμ0 : max μV (fixDeg k) + 2 ≤ μ0) :
    RecipPowerLB (2 / alpha) (baseCF V D k alpha) (D * 2 ^ μ0 + 1) (D + 1) := by
  have hX := two_div_ge_two ha ha2
  obtain ⟨hB0, hB1, hBi⟩ := budget_gen_bounds_fejer k ha ha2
  have hc := GenParams.slice_const_le (V := V) (B := globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k)
    (μV := μV) (k := k) (μ0 := μ0) ha ha2 hV hVμ hB0 hBi hμ0
  intro s hs hs1
  have hs2 : 0 < s / 2 := half_pos hs
  have hs21 : s / 2 ≤ 1 := by linarith
  have hg : 0 < alpha / 2 := half_pos ha
  have hg1 : alpha / 2 ≤ 1 := by linarith
  set B := globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k with hBdef
  have hQ1 := one_le_uCount V D (alpha / 2) B (s / 2)
  have hQ0 : 0 < uCount V D (alpha / 2) B (s / 2) := lt_of_lt_of_le zero_lt_one hQ1
  have hQeq := uCount_eq hV D hg hg1 hB0 hB1 hs2 hs21
  rw [GenParams.uniformBase_slice V ha hB0 hs] at hQeq
  show 0 < s / 2 / uCount V D (alpha / 2) B (s / 2) ∧
    s / 2 / uCount V D (alpha / 2) B (s / 2) ≤ 1 ∧
    (s / 2 / uCount V D (alpha / 2) B (s / 2))⁻¹ ≤
      (2 / alpha) ^ (D * 2 ^ μ0 + 1) * s⁻¹ ^ (D + 1)
  refine ⟨div_pos hs2 hQ0, (div_le_one hQ0).mpr (by linarith), ?_⟩
  rw [inv_div, hQeq]
  set X := 2 / alpha with hXdef
  have hsi : 0 ≤ s⁻¹ := (inv_pos.mpr hs).le
  have hcs : 8 * V * X * B⁻¹ * s⁻¹ ≤ X ^ (2 ^ μ0) * s⁻¹ := mul_le_mul_of_nonneg_right hc hsi
  have hpow := pow_le_pow_left₀ (by positivity) hcs D
  have h2X : (2 : Real) ≤ X ^ 1 := by rw [pow_one]; exact hX
  calc (8 * V * X * B⁻¹ * s⁻¹) ^ D / (s / 2) = 2 * (s⁻¹ * (8 * V * X * B⁻¹ * s⁻¹) ^ D) := by
        rw [div_eq_mul_inv, inv_div]; ring
    _ ≤ X ^ 1 * (s⁻¹ * (X ^ (2 ^ μ0) * s⁻¹) ^ D) :=
        mul_le_mul h2X (mul_le_mul_of_nonneg_left hpow hsi) (by positivity) (by positivity)
    _ = X ^ (D * 2 ^ μ0 + 1) * s⁻¹ ^ (D + 1) := by ring

end Fixed

end LeanProofs.GowersSzemeredi
