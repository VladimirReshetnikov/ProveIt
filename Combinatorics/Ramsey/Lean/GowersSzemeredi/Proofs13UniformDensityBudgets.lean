import GowersSzemeredi.Proofs13UniformRoundedBudgets

/-! Bohr-model integer budgets uniform over the actual density. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Filter

/-- The radius in the corrected Section 10 model is positive. -/
theorem section10Zeta_pos {a : Real} (ha : 0 < a) : 0 < section10Zeta a := by
  have hk : 0 < section10SpectrumParameter a := by
    apply Nat.ceil_pos.mpr
    unfold section10SpectrumBound
    positivity
  exact div_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (pow_pos ha _))
    (by exact_mod_cast hk)

/-- Fixed-q integer budgets, with a threshold uniform in every actual density
above delta. The target still uses the actual density, so no mass or length
parameter is silently replaced. -/
theorem section13_eventually_density_integer_budgets {delta : Real}
    (hδ : 0 < delta) {q : Nat} (hq : 0 < q) :
    ∀ᶠ N : Nat in atTop, ∀ alpha : Real, delta ≤ alpha → alpha ≤ 1 →
      (q : Real) ≤ section13QBound (section10Lambda (alpha ^ 32 / 16)) → ∀ p L Q : Nat,
      IsNatFloor (section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) /
        (64 * Real.pi) * (N : Real) ^
          (section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) ^ 2 / (16 * (q : Real)))) p →
      (L = p ∨ L + 1 = p) →
      (L : Real) ^ ((1 : Real) / (2 : Real) ^ (12 * q)) / 2 ≤ Q →
      ∃ m : Nat, 0 < m ∧ m * m ≤ N ∧ m + 1 ≤ Q ∧
        section13Zeta alpha / 2 *
          (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q alpha)) ≤ m ∧
        (L : Real) ^ (-((1 : Real) / (2 : Real) ^ (11 * q))) ≤
          section10Zeta (alpha ^ 32 / 16) / m := by
  let theta := section10Lambda (delta ^ 32 / 16)
  let d₀ := section13ThetaOne theta / (64 * Real.pi)
  let d := min 1 (d₀ / 2)
  let u₀ := section13ThetaOne theta ^ 2 / (16 * (q : Real))
  let c₀ := section13Zeta delta / 2
  let e₀ := (1 : Real) / (2 : Real) ^ (13 * section13Q delta)
  let z₀ := section10Zeta (delta ^ 32 / 16)
  have hθ : 0 < theta := by dsimp [theta, section10Lambda]; positivity
  have hθ₁ : 0 < section13ThetaOne theta := by unfold section13ThetaOne; positivity
  have hd₀ : 0 < d₀ := div_pos hθ₁ (mul_pos (by norm_num) Real.pi_pos)
  have hd : 0 < d := lt_min zero_lt_one (div_pos hd₀ (by norm_num))
  have hu₀ : 0 < u₀ := div_pos (pow_pos hθ₁ _) (mul_pos (by norm_num) (by exact_mod_cast hq))
  have hc₀ : 0 < c₀ := by dsimp [c₀, section13Zeta]; positivity
  have he₀ : 0 < e₀ := by dsimp [e₀]; positivity
  have hz₀ : 0 < z₀ := section10Zeta_pos (by positivity)
  obtain ⟨N₀, hN₀⟩ := uniform_rounded_power_budgets hc₀ hd (min_le_left _ _) hz₀ he₀
  filter_upwards [eventually_ge_atTop N₀, eventually_ge_atTop (1 : Nat),
    eventually_nat_mul_rpow_le (C := 4) hu₀ hd₀] with N hN hNpos hfloor
  intro alpha hδα hαone hqB p L Q hp hL hQlen
  have hα : 0 < alpha := hδ.trans_le hδα
  have hNreal : (1 : Real) ≤ N := by exact_mod_cast hNpos
  let u := section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) ^ 2 / (16 * (q : Real))
  let e := (1 : Real) / (2 : Real) ^ (13 * section13Q alpha)
  let v := (1 : Real) / (2 : Real) ^ (12 * q)
  let w := (1 : Real) / (2 : Real) ^ (11 * q)
  have ht := section13ThetaOne_mono hθ.le (section13_cutoff_mono hδ hδα)
  have hdle : d₀ ≤ section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) / (64 * Real.pi) :=
    div_le_div_of_nonneg_right ht (by positivity)
  have hule : u₀ ≤ u := div_le_div_of_nonneg_right (pow_le_pow_left₀ hθ₁.le ht 2)
    (by positivity)
  have hfour : 4 ≤ d₀ * (N : Real) ^ u := by
    calc
      _ ≤ d₀ * (N : Real) ^ u₀ := by simpa only [Real.rpow_zero, mul_one] using hfloor
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hNreal hule) hd₀.le
  have hPlower : d * (N : Real) ^ u ≤ (L : Real) := by
    have hpupper := hp.2
    have hlower := mul_le_mul_of_nonneg_right hdle (Real.rpow_nonneg (Nat.cast_nonneg N) u)
    have hhalf : d₀ / 2 * (N : Real) ^ u ≤ (L : Real) := by
      rcases hL with hL | hL
      · subst L
        nlinarith only [hpupper, hlower, hfour]
      · have hLc : (L : Real) + 1 = p := by exact_mod_cast hL
        nlinarith only [hpupper, hlower, hfour, hLc]
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.rpow_nonneg (Nat.cast_nonneg N) u)).trans hhalf
  have hcc : c₀ ≤ section13Zeta alpha / 2 :=
    div_le_div_of_nonneg_right (section13Zeta_mono hδ hδα hαone) (by norm_num)
  have hcmax : section13Zeta alpha / 2 ≤ 1 / 2 :=
    div_le_div_of_nonneg_right (section13Zeta_le_one hα hαone) (by norm_num)
  have hee : e₀ ≤ e := section13_length_exponent_mono hδ hδα
  have hQ : 1 ≤ section13Q alpha := by
    have hqone : (1 : Real) ≤ q := by exact_mod_cast hq
    have hqQ := hqB.trans (section13_qBound_le_half_Q hα hαone)
    linarith only [hqone, hqQ]
  have htwo : (2 : Real) ≤ (2 : Real) ^ (13 * section13Q alpha) := by
    calc
      _ = (2 : Real) ^ (1 : Real) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hQ])
  have hemax : 2 * e ≤ 1 := by
    dsimp [e]
    exact (by simpa only [div_eq_mul_inv, one_mul] using
      (div_le_one (Real.rpow_pos_of_pos (by norm_num : (0 : Real) < 2) _)).mpr htwo)
  have hv : 0 < v := by dsimp [v]; positivity
  have hw : 0 < w := by dsimp [w]; positivity
  have hvone : v ≤ 1 := by
    dsimp [v]
    apply (div_le_one (by positivity)).mpr
    exact one_le_pow₀ (by norm_num)
  have hwone : w ≤ 1 := by
    dsimp [w]
    apply (div_le_one (by positivity)).mpr
    exact one_le_pow₀ (by norm_num)
  have hz : z₀ ≤ section10Zeta (alpha ^ 32 / 16) := by
    apply section10Zeta_mono (by positivity)
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ hδ.le hδα 32) (by norm_num))
    have hh := pow_le_one₀ hα.le hαone (n := 32)
    linarith only [hh]
  have hrec : 2 * e < u * v := section13_double_recurrence_exponent_margin hα hαone hq hqB
  have hvw : v ≤ w := by
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by omega : 11 * q ≤ 12 * q)
  have hbohr : 2 * e ≤ u * w := hrec.le.trans
    (mul_le_mul_of_nonneg_left hvw (hu₀.le.trans hule))
  obtain ⟨m, hm, hmsq, hmQ, hmlower, hmbohr⟩ := hN₀ N hN
    (section13Zeta alpha / 2) e u v w (section10Zeta (alpha ^ 32 / 16)) L Q
    hcc hcmax hee hemax hv hvone hw hwone hz hrec.le hbohr hPlower hQlen
  exact ⟨m, hm, by simpa only [pow_two] using hmsq, by exact_mod_cast hmQ, hmlower, hmbohr⟩

/-- One threshold supplies the Bohr integer budgets simultaneously for every
actual density in [delta,1], every permitted spectrum size, and all floor data. -/
theorem section13_uniform_density_integer_budgets {delta : Real} (hδ : 0 < delta) :
    ∃ N₀ : Nat, ∀ N : Nat, N₀ ≤ N → ∀ alpha : Real, delta ≤ alpha → alpha ≤ 1 →
      ∀ q p L Q : Nat, 0 < q →
      (q : Real) ≤ section13QBound (section10Lambda (alpha ^ 32 / 16)) →
      IsNatFloor (section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) /
        (64 * Real.pi) * (N : Real) ^
          (section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) ^ 2 / (16 * (q : Real)))) p →
      (L = p ∨ L + 1 = p) →
      (L : Real) ^ ((1 : Real) / (2 : Real) ^ (12 * q)) / 2 ≤ Q →
      ∃ m : Nat, 0 < m ∧ m * m ≤ N ∧ m + 1 ≤ Q ∧
        section13Zeta alpha / 2 *
          (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q alpha)) ≤ m ∧
        (L : Real) ^ (-((1 : Real) / (2 : Real) ^ (11 * q))) ≤
          section10Zeta (alpha ^ 32 / 16) / m := by
  let B := section13QBound (section10Lambda (delta ^ 32 / 16))
  have hall : ∀ᶠ N : Nat in atTop, ∀ q ∈ Finset.range (Nat.floor B + 1),
      0 < q → ∀ alpha : Real, delta ≤ alpha → alpha ≤ 1 →
      (q : Real) ≤ section13QBound (section10Lambda (alpha ^ 32 / 16)) → ∀ p L Q : Nat,
      IsNatFloor (section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) /
        (64 * Real.pi) * (N : Real) ^
          (section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) ^ 2 / (16 * (q : Real)))) p →
      (L = p ∨ L + 1 = p) →
      (L : Real) ^ ((1 : Real) / (2 : Real) ^ (12 * q)) / 2 ≤ Q →
      ∃ m : Nat, 0 < m ∧ m * m ≤ N ∧ m + 1 ≤ Q ∧
        section13Zeta alpha / 2 *
          (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q alpha)) ≤ m ∧
        (L : Real) ^ (-((1 : Real) / (2 : Real) ^ (11 * q))) ≤
          section10Zeta (alpha ^ 32 / 16) / m := by
    apply (eventually_all_finset _).mpr
    intro q _
    by_cases hq : 0 < q
    · filter_upwards [section13_eventually_density_integer_budgets hδ hq] with N hN
      exact fun _ => hN
    · exact Eventually.of_forall (fun _ h => (hq h).elim)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hall
  refine ⟨N₀, fun N hN alpha hδα hαone q p L Q hq hqB => ?_⟩
  have hθ : 0 < section10Lambda (delta ^ 32 / 16) := by unfold section10Lambda; positivity
  have hqfloor : q ≤ Nat.floor B := Nat.le_floor (hqB.trans
    (section13QBound_antitone hθ (section13_cutoff_mono hδ hδα)))
  exact hN₀ N hN q (Finset.mem_range.mpr (by omega)) hq alpha hδα hαone hqB p L Q

/-- Stage 13.6 with a threshold depending only on the density lower bound;
the constructed progression retains the actual-density length estimate. -/
theorem lemma_13_6_uniform_density {delta : Real} (hδ : 0 < delta) :
    ∃ N₀ : Nat, ∀ (N : Nat) [Fact N.Prime]
      (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N),
      delta ≤ S.alpha → N₀ ≤ N →
      IsStage134Data S (section10Lambda (S.alpha ^ 32 / 16)) D →
      IsStage135Data S D E →
      ∃ F : Stage136Data N, IsStage136Data S D E F ∧ F.R.length ≤ E.Q.length := by
  obtain ⟨N₀, hN₀⟩ := section13_uniform_density_integer_budgets hδ
  refine ⟨N₀, fun N _ S D E hS hN h134 h135 => ?_⟩
  obtain ⟨m, hm, hsize, hupper, hlower, hbudget⟩ :=
    hN₀ N hN S.alpha hS S.alpha_at_most_one D.q D.m D.P.length E.Q.length
      h134.1 h134.2.2.2.2.1 h134.2.2.2.2.2.1 h134.2.2.2.2.2.2.1 h135.2.2.2.1
  exact lemma_13_6_from_initial_stages_all_densities S D E m
    h134 h135 hm hsize hupper hlower hbudget

end LeanProofs.GowersSzemeredi
