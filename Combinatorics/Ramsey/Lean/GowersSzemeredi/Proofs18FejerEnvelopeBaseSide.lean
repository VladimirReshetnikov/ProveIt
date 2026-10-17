import GowersSzemeredi.Proofs18FejerEnvelopeBase
import GowersSzemeredi.Proofs18GenericEnvelopeBaseSide

/-! Declarations of `Proofs18FejerEnvelopeBase` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

section
variable {alpha : Real}

theorem budget_gen_bounds_fejer (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k ∧
      globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k ≤ 1 ∧
      (globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k)⁻¹ ≤ (2 / alpha) ^ (2 ^ fixDeg k) := by
  obtain ⟨hfa0, hfaS⟩ := fejer_alpha_bounds k ha ha2
  obtain ⟨_, h1⟩ := section16ThetaTwo_pos_le_with hfa0 hfaS
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
    exact le_trans (div_le_div_of_nonneg_left (by positivity) (pow_pos hq0 11) hpow) hbud
  unfold section16Zeta tightZeta
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg hexp)

theorem zeta_gen_bounds_fejer (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < tightZeta (fejerThetaOne alpha (alpha / 2) k / 4) ∧
      (tightZeta (fejerThetaOne alpha (alpha / 2) k / 4))⁻¹ ≤
        Real.exp ((2 / alpha) ^ (2 ^ (2 ^ (k + 6) + 1))) := by
  obtain ⟨z0, zi⟩ := zeta_gen_bounds k ha ha2
  have hle := section16Zeta_le_tight_fejer k ha ha2
  exact ⟨lt_of_lt_of_le z0 hle, (inv_anti₀ z0 hle).trans zi⟩

/-- **The Fejér base density is a reciprocal power** (`GenParams.baseC_recipPowerLB`). -/
theorem baseCF_recipPowerLB {V : Real} {D k μV μ0 : Nat} (ha : 0 < alpha)
    (ha2 : alpha ≤ 1 / 2) (hV : 1 ≤ V) (hVμ : V ≤ 2 ^ (2 ^ μV))
    (hμ0 : max μV (fixDeg k) + 2 ≤ μ0) :
    RecipPowerLB (2 / alpha) (baseCF V D k alpha) (D * 2 ^ μ0 + 1) (D + 1) := by
  obtain ⟨hB0, hB1, hBi⟩ := budget_gen_bounds_fejer k ha ha2
  exact uniform_baseC_recipPowerLB_of_budget ha ha2 hV hVμ hB0 hB1
    (show 7 ≤ fixDeg k from Nat.le_add_left 7 _) hBi hμ0

end

end LeanProofs.GowersSzemeredi
