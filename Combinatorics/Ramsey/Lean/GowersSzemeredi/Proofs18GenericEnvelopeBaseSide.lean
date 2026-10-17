import GowersSzemeredi.Proofs18GenericEnvelopeBase
import GowersSzemeredi.Proofs18LengthSixCountsSide

/-! Declarations of `Proofs18GenericEnvelopeBase` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

section
variable {alpha : Real}

theorem thetaOne_gen_bounds (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < section16ThetaOne alpha (alpha / 2) k ∧ section16ThetaOne alpha (alpha / 2) k ≤ 1 ∧
      (section16ThetaOne alpha (alpha / 2) k)⁻¹ ≤ (2 / alpha) ^ (2 ^ (2 ^ (k + 5) + 2)) := by
  have ha1 : alpha ≤ 1 := by linarith
  obtain ⟨h0, h1, -, -⟩ := section16_theta_delta_bounds k ha ha1 (half_pos ha) (by linarith)
  have hX := two_div_ge_two ha ha2
  have hq0 : 0 < alpha * (alpha / 2) / 4 := by positivity
  refine ⟨h0, h1, ?_⟩
  unfold section16ThetaOne
  rw [← inv_pow]
  have hq := quarter_base_inv_le ha ha2
  calc (alpha * (alpha / 2) / 4)⁻¹ ^ (2 ^ 2 ^ (k + 5)) ≤ ((2 / alpha) ^ 3) ^ (2 ^ 2 ^ (k + 5)) :=
        pow_le_pow_left₀ (inv_pos.mpr hq0).le hq _
    _ = (2 / alpha) ^ (3 * 2 ^ 2 ^ (k + 5)) := by rw [← pow_mul]
    _ ≤ (2 / alpha) ^ (2 ^ (2 ^ (k + 5) + 2)) := by
        apply pow_le_pow_right₀ (le_trans (by norm_num) hX)
        have h : 2 ^ (2 ^ (k + 5) + 2) = 2 ^ (2 ^ (k + 5)) * 4 := by rw [pow_add]; norm_num
        omega

theorem thetaTwo_gen_bounds (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < section16ThetaTwo (section16ThetaOne alpha (alpha / 2) k) ∧
      section16ThetaTwo (section16ThetaOne alpha (alpha / 2) k) ≤ 1 ∧
      (section16ThetaTwo (section16ThetaOne alpha (alpha / 2) k))⁻¹ ≤
        (2 / alpha) ^ (2 ^ (2 ^ (k + 5) + 6)) := by
  obtain ⟨h0, h1⟩ := section16ThetaTwo_pos_le (gamma := alpha / 2) k ha
    (by linarith) (half_pos ha) (by linarith)
  obtain ⟨t0, -, ti⟩ := thetaOne_gen_bounds k ha ha2
  refine ⟨h0, h1, ?_⟩
  exact (section16ThetaTwo_inv_le_pw (two_div_ge_two ha ha2)
    (by have := Nat.lt_two_pow_self (n := k + 5); omega) t0 ti)

theorem budget_gen_bounds (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < globalBudget alpha (alpha / 2) k ∧ globalBudget alpha (alpha / 2) k ≤ 1 ∧
      (globalBudget alpha (alpha / 2) k)⁻¹ ≤ (2 / alpha) ^ (2 ^ fixDeg k) := by
  have hk : k + 2 ≤ 2 ^ (k + 5) + 6 := by
    have := Nat.lt_two_pow_self (n := k + 5); omega
  exact density_div_bounds_pw (two_div_ge_two ha ha2) (thetaTwo_gen_bounds k ha ha2)
    (by have : (1 : Real) ≤ 2 ^ k := one_le_pow₀ (by norm_num); linarith)
    (budget_denominator_le_pw (two_div_ge_two ha ha2) hk)

theorem T2_gen_bounds (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < globalTheta2 alpha (alpha / 2) k ∧ globalTheta2 alpha (alpha / 2) k ≤ 1 ∧
      (globalTheta2 alpha (alpha / 2) k)⁻¹ ≤ (2 / alpha) ^ (2 ^ fixDeg k) := by
  exact density_div_bounds_pw (two_div_ge_two ha ha2) (thetaTwo_gen_bounds k ha ha2)
    (by norm_num) ((two_div_ge_two ha ha2).trans (pw_X (two_div_ge_two ha ha2) _))

theorem delta_gen_bounds (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < section16Delta (section16ThetaOne alpha (alpha / 2) k) ∧
      section16Delta (section16ThetaOne alpha (alpha / 2) k) ≤ 1 ∧
      (section16Delta (section16ThetaOne alpha (alpha / 2) k))⁻¹ ≤ (2 / alpha) ^ (2 ^ fixDeg k) := by
  obtain ⟨t0, t1, d0, d1⟩ := section16_theta_delta_bounds k ha (by linarith)
    (half_pos ha) (by linarith)
  have hi := (section16Delta_inv_le_pw (two_div_ge_two ha ha2)
    (by have := Nat.lt_two_pow_self (n := k + 5); omega) t0 t1
    (thetaOne_gen_bounds k ha ha2).2.2)
  exact ⟨d0, d1, pw_mono (two_div_ge_two ha ha2) hi (by unfold fixDeg; omega)⟩

end

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

/-- The uniform slice density is a reciprocal power, independently of any
single-piece parameter structure. -/
theorem uniform_baseC_recipPowerLB {alpha V : Real} {D k μV μ0 : Nat} (ha : 0 < alpha)
    (ha2 : alpha ≤ 1 / 2) (hV : 1 ≤ V) (hVμ : V ≤ 2 ^ (2 ^ μV))
    (hμ0 : max μV (fixDeg k) + 2 ≤ μ0) :
    RecipPowerLB (2 / alpha)
      (fun s => s / 2 / uCount V D (alpha / 2) (globalBudget alpha (alpha / 2) k) (s / 2))
      (D * 2 ^ μ0 + 1) (D + 1) := by
  obtain ⟨hB0, hB1, hBi⟩ := budget_gen_bounds k ha ha2
  exact uniform_baseC_recipPowerLB_of_budget ha ha2 hV hVμ hB0 hB1
    (show 7 ≤ fixDeg k from Nat.le_add_left 7 _) hBi hμ0

/-- **Lemma 15.6's threshold in dimension `k ≥ 1`.** -/
theorem lemma156_gen_le {alpha : Real} {k : Nat} (hk : 1 ≤ k) (ha : 0 < alpha)
    (ha2 : alpha ≤ 1 / 2) :
    lemma156ExplicitThreshold k (alpha / 2) (alpha / 2) ≤
      (2 / alpha) ^ (2 ^ (2 ^ (k + 4) + 4 * k + 13)) := by
  have hX := two_div_ge_two ha ha2
  have hXa : (alpha / 2)⁻¹ = 2 / alpha := inv_div _ _
  set u := 2 / alpha
  have hinv : u⁻¹ = alpha / 2 := by rw [← hXa, inv_inv]
  set N1 := 7 * 4 ^ (k + 1) + 21 * k * 4 ^ (k + 1)
  set E := arrangementSelectionExponent k
  have hdeg := selection_degree_le k
  -- the selection base `a = (α/2)^N1 = u^(-N1)`
  have hbase : (u ^ N1)⁻¹ = (alpha / 2) ^ (7 * 4 ^ (k + 1)) * (alpha / 2) ^ (21 * k * 4 ^ (k + 1)) := by
    rw [← pow_add, ← hinv, inv_pow]
  have hexp : 2 ^ (k + 5) + k + ((N1 + 46) * E + 2) ≤ 2 ^ (2 ^ (k + 4) + 4 * k + 13) := by
    have h1 : 2 ^ (k + 5) + k + 2 ≤ 2 ^ (2 ^ (k + 4) + 4 * k + 11) := by
      have h := Nat.lt_two_pow_self (n := k + 5)
      have : 2 * 2 ^ (k + 5) ≤ 2 ^ (2 ^ (k + 4) + 4 * k + 11) := by
        rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by
          have := Nat.lt_two_pow_self (n := k + 4); omega)
      omega
    have h2 : 2 ^ (2 ^ (k + 4) + 4 * k + 13) = 4 * 2 ^ (2 ^ (k + 4) + 4 * k + 11) := by
      rw [show 2 ^ (k + 4) + 4 * k + 13 = (2 ^ (k + 4) + 4 * k + 11) + 2 by ring, pow_add]; ring
    generalize (N1 + 46) * E = P at hdeg ⊢
    omega
  exact lemma156ExplicitThreshold_le_power_of_selection_base hk hX hbase.le (by
    simpa only [show 32 * 2 ^ k = 2 ^ (k + 5) by rw [pow_add]; ring] using hexp)

end LeanProofs.GowersSzemeredi
