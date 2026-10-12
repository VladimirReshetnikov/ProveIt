import GowersSzemeredi.Proofs18FejerEnvelopeBase

/-! **The Fejér fixed parameters at the base budget of `V`** (Notes L.16i).

`Proofs18FejerEnvelopeBase` transfers the printed bounds at
`X^(2^fixDeg k)`, `fixDeg k = 2^(k+5) + 7`, which keeps the base budget at
`μ₀ ≈ 32·2^k`. The Fejér density is much larger: `θ₁′⁻¹ ≤ X^(2^(5k+16))`
(`thetaOne_fejer_bounds`, from `F ≤ 2^(5k+14)`). So the budget, `θ₂/2` and δ
are above `X^(-2^(5k+21))` (`…_fejer_bounds5`, generated from the printed
proofs with the atom `2^(k+5)` replaced by `5k + 14`), and hence above
`X^(-2^fixDegQ k)` with

  `fixDegQ k = fixDeg (k − 1) = 2^(k+4) + 7`   (k ≥ 1),

the size of the class-base term `tightMuV k = 2^(k+4) + 1`. Stating it as
`fixDeg (k − 1)` lets every generic step lemma be reused at `k − 1`.
* `budget_gen_bounds_fejerQ`, `T2_gen_bounds_fejerQ`,
  `delta_gen_bounds_fejerQ`;
* `baseCFQ_recipPowerLB`: `baseCF_recipPowerLB` at `fixDegQ`;
* `fixDeg_le_two_fixDegQ`, `k_succ_le_two_pow_fixDegQ`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The base-budget log-degree at the class base: `fixDeg (k − 1)`. -/
def fixDegQ (k : Nat) : Nat := fixDeg (k - 1)

theorem fixDegQ_eq {k : Nat} (hk : 1 ≤ k) : fixDegQ k = 2 ^ (k + 4) + 7 := by
  unfold fixDegQ fixDeg
  rw [show k - 1 + 5 = k + 4 by omega]

theorem fixDeg_le_two_fixDegQ (k : Nat) : fixDeg k ≤ 2 * fixDegQ k := by
  unfold fixDegQ fixDeg
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · norm_num
  · rw [show k - 1 + 5 = k + 4 by omega, show k + 5 = (k + 4) + 1 by ring, pow_succ]
    omega

theorem five_k_le_fixDegQ (k : Nat) : 5 * k + 21 ≤ fixDegQ k := by
  unfold fixDegQ fixDeg
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · norm_num
  · rw [show k - 1 + 5 = k + 4 by omega]
    have h : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
    have h16 : 2 ^ (k + 4) = 16 * 2 ^ k := by rw [pow_add]; ring
    omega

theorem k_succ_le_two_pow_fixDegQ (k : Nat) : k + 1 ≤ 2 ^ fixDegQ k := by
  have h1 : k + 1 ≤ 2 ^ (5 * k + 21) := by
    have := Nat.lt_two_pow_self (n := 5 * k + 21); omega
  exact h1.trans (Nat.pow_le_pow_right (by norm_num) (five_k_le_fixDegQ k))

section Fixed

variable {alpha : Real}

/-- `θ₁′⁻¹ ≤ X^(2^(5k+16))`. -/
theorem thetaOne_fejer_bounds (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < fejerThetaOne alpha (alpha / 2) k ∧ fejerThetaOne alpha (alpha / 2) k ≤ 1 ∧
      (fejerThetaOne alpha (alpha / 2) k)⁻¹ ≤ (2 / alpha) ^ (2 ^ (5 * k + 16)) := by
  obtain ⟨h0, h1⟩ := fejer_alpha_bounds k ha ha2
  have hX := two_div_ge_two ha ha2
  have hq0 : 0 < alpha * (alpha / 2) / 4 := by positivity
  refine ⟨by linarith, by linarith, ?_⟩
  unfold fejerThetaOne
  rw [← inv_pow]
  have hq := quarter_base_inv_le ha ha2
  have hF := fejerProductExponent_le k
  calc (alpha * (alpha / 2) / 4)⁻¹ ^ fejerProductExponent k
      ≤ ((2 / alpha) ^ 3) ^ fejerProductExponent k := pow_le_pow_left₀ (inv_pos.mpr hq0).le hq _
    _ = (2 / alpha) ^ (3 * fejerProductExponent k) := by rw [← pow_mul]
    _ ≤ (2 / alpha) ^ (2 ^ (5 * k + 16)) := by
        apply pow_le_pow_right₀ (le_trans (by norm_num) hX)
        have h : 2 ^ (5 * k + 16) = 4 * 2 ^ (5 * k + 14) := by
          rw [show 5 * k + 16 = (5 * k + 14) + 2 by ring, pow_add]; ring
        omega

theorem thetaTwo_fejer_bounds (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < section16ThetaTwo (fejerThetaOne alpha (alpha / 2) k) ∧
      section16ThetaTwo (fejerThetaOne alpha (alpha / 2) k) ≤ 1 ∧
      (section16ThetaTwo (fejerThetaOne alpha (alpha / 2) k))⁻¹ ≤
        (2 / alpha) ^ (2 ^ ((5 * k + 14) + 6)) := by
  have ha1 : alpha ≤ 1 := by linarith
  obtain ⟨h0, h1⟩ := section16ThetaTwo_pos_le_with (fejer_alpha_bounds k ha ha2).1 (fejer_alpha_bounds k ha ha2).2
  obtain ⟨t0, -, ti⟩ := thetaOne_fejer_bounds k ha ha2
  have hX := two_div_ge_two ha ha2
  have hX0 : (0 : Real) ≤ 2 / alpha := by linarith
  refine ⟨h0, h1, ?_⟩
  unfold section16ThetaTwo
  have h32 : ((2 : Real) ^ (-(32 : Real)))⁻¹ ≤ (2 / alpha) ^ (2 ^ ((5 * k + 14) + 2)) := by
    rw [Real.rpow_neg (by norm_num), inv_inv,
      show (32 : Real) = ((32 : Nat) : Real) by norm_num, Real.rpow_natCast]
    refine (pow_le_pow_left₀ (by norm_num) hX 32).trans (pw_natpow hX ?_)
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ ((5 * k + 14) + 2) := Nat.pow_le_pow_right (by norm_num) (by
          omega)
  have h8 : ((fejerThetaOne alpha (alpha / 2) k) ^ 8)⁻¹ ≤
      (2 / alpha) ^ (2 ^ ((5 * k + 14) + 2 + 3)) := by
    rw [← inv_pow]
    exact pw_pow hX (inv_pos.mpr t0).le ti (by norm_num)
  rw [mul_inv]
  have := pw_mul hX (by positivity) (by positivity) (pw_mono hX h32 (by omega)) h8
  exact pw_mono hX this (by omega)


theorem budget_fejer_bounds5 (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k ∧ globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k ≤ 1 ∧
      (globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k)⁻¹ ≤ (2 / alpha) ^ (2 ^ (5 * k + 21)) := by
  obtain ⟨h0, h1, hi⟩ := thetaTwo_fejer_bounds k ha ha2
  have hX := two_div_ge_two ha ha2
  have hden : (1 : Real) ≤ 2 * (2 ^ k + 1) := by
    have : (1 : Real) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    linarith
  unfold globalBudgetW
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_le_one (by positivity)]; linarith
  · rw [inv_div, div_eq_mul_inv]
    have hc : 2 * ((2 : Real) ^ k + 1) ≤ (2 / alpha) ^ (2 ^ ((5 * k + 14) + 6)) := by
      have h1 : 2 * ((2 : Real) ^ k + 1) ≤ 2 ^ (k + 2) := by
        have : (1 : Real) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
        rw [pow_add]; norm_num; linarith
      refine h1.trans ((pow_le_pow_left₀ (by norm_num) hX _).trans (pw_natpow hX ?_))
      calc k + 2 ≤ 2 ^ (k + 2) := Nat.lt_two_pow_self.le
        _ ≤ 2 ^ ((5 * k + 14) + 6) := Nat.pow_le_pow_right (by norm_num) (by
            have : k + 2 ≤ (5 * k + 14) := by
              have := Nat.lt_two_pow_self (n := k + 5); omega
            omega)
    have := pw_mul hX (by positivity) (inv_pos.mpr h0).le hc hi
    exact this

theorem T2_fejer_bounds5 (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < globalTheta2W (fejerThetaOne alpha (alpha / 2) k) ∧ globalTheta2W (fejerThetaOne alpha (alpha / 2) k) ≤ 1 ∧
      (globalTheta2W (fejerThetaOne alpha (alpha / 2) k))⁻¹ ≤ (2 / alpha) ^ (2 ^ (5 * k + 21)) := by
  obtain ⟨h0, h1, hi⟩ := thetaTwo_fejer_bounds k ha ha2
  have hX := two_div_ge_two ha ha2
  unfold globalTheta2W
  refine ⟨by positivity, by linarith, ?_⟩
  rw [inv_div, div_eq_mul_inv]
  have h2 : (2 : Real) ≤ (2 / alpha) ^ (2 ^ ((5 * k + 14) + 6)) :=
    hX.trans (pw_X hX _)
  have := pw_mul hX (by norm_num) (inv_pos.mpr h0).le h2 hi
  exact pw_mono hX this (by omega)

theorem delta_fejer_bounds5 (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < section16Delta (fejerThetaOne alpha (alpha / 2) k) ∧
      section16Delta (fejerThetaOne alpha (alpha / 2) k) ≤ 1 ∧
      (section16Delta (fejerThetaOne alpha (alpha / 2) k))⁻¹ ≤ (2 / alpha) ^ (2 ^ (5 * k + 21)) := by
  have ha1 : alpha ≤ 1 := by linarith
  obtain ⟨-, -, d0, d1⟩ := section16_theta_delta_bounds_with (fejer_alpha_bounds k ha ha2).1 (fejer_alpha_bounds k ha ha2).2
  obtain ⟨t0, t1, ti⟩ := thetaOne_fejer_bounds k ha ha2
  have hX := two_div_ge_two ha ha2
  refine ⟨d0, d1, ?_⟩
  set t := fejerThetaOne alpha (alpha / 2) k with htdef
  have hq0 : 0 < t / 4 := by positivity
  have hq1 : t / 4 ≤ 1 := by linarith
  -- `(t/4)^(11/2) ≥ (t/4)^6`
  have h6 : (t / 4) ^ (6 : Nat) ≤ (t / 4) ^ ((11 : Real) / 2) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hq0 hq1 (by norm_num)
  unfold section16Delta
  have h37 : ((2 : Real) ^ (-(37 : Real)))⁻¹ = 2 ^ (37 : Nat) := by
    rw [Real.rpow_neg (by norm_num), inv_inv,
      show (37 : Real) = ((37 : Nat) : Real) by norm_num, Real.rpow_natCast]
  rw [mul_inv, h37]
  have hinv6 : ((t / 4) ^ ((11 : Real) / 2))⁻¹ ≤ ((t / 4) ^ (6 : Nat))⁻¹ :=
    inv_anti₀ (pow_pos hq0 _) h6
  have hq : ((t / 4) ^ (6 : Nat))⁻¹ ≤ (2 / alpha) ^ (2 ^ ((5 * k + 14) + 2 + 1 + 3)) := by
    rw [← inv_pow, inv_div]
    have h4t : 4 / t ≤ (2 / alpha) ^ (2 ^ ((5 * k + 14) + 2 + 1)) := by
      rw [div_eq_mul_inv]
      have h4 : (4 : Real) ≤ (2 / alpha) ^ (2 ^ ((5 * k + 14) + 2)) :=
        (show (4 : Real) ≤ 2 ^ 2 by norm_num).trans
          ((pow_le_pow_left₀ (by norm_num) hX 2).trans (pw_natpow hX (by
            calc 2 = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ ((5 * k + 14) + 2) := Nat.pow_le_pow_right (by norm_num) (by
                  have := Nat.one_le_two_pow (n := k + 5); omega))))
      exact pw_mul hX (by norm_num) (inv_pos.mpr t0).le h4 ti
    exact pw_pow hX (by positivity) h4t (by norm_num)
  have h2 : (2 : Real) ^ (37 : Nat) ≤ (2 / alpha) ^ (2 ^ ((5 * k + 14) + 2 + 1 + 3)) :=
    (pow_le_pow_left₀ (by norm_num) hX 37).trans (pw_natpow hX (by
      calc 37 ≤ 2 ^ 6 := by norm_num
        _ ≤ 2 ^ ((5 * k + 14) + 2 + 1 + 3) := Nat.pow_le_pow_right (by norm_num) (by
            have := Nat.one_le_two_pow (n := k + 5); omega)))
  have := pw_mul hX (by positivity) (by positivity) h2 (hinv6.trans hq)
  exact pw_mono hX this (by omega)


theorem budget_gen_bounds_fejerQ (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k ∧
      globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k ≤ 1 ∧
      (globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k)⁻¹ ≤ (2 / alpha) ^ (2 ^ fixDegQ k) := by
  obtain ⟨h0, h1, hi⟩ := budget_fejer_bounds5 k ha ha2
  exact ⟨h0, h1, pw_mono (two_div_ge_two ha ha2) hi (five_k_le_fixDegQ k)⟩

theorem T2_gen_bounds_fejerQ (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < globalTheta2W (fejerThetaOne alpha (alpha / 2) k) ∧
      globalTheta2W (fejerThetaOne alpha (alpha / 2) k) ≤ 1 ∧
      (globalTheta2W (fejerThetaOne alpha (alpha / 2) k))⁻¹ ≤ (2 / alpha) ^ (2 ^ fixDegQ k) := by
  obtain ⟨h0, h1, hi⟩ := T2_fejer_bounds5 k ha ha2
  exact ⟨h0, h1, pw_mono (two_div_ge_two ha ha2) hi (five_k_le_fixDegQ k)⟩

theorem delta_gen_bounds_fejerQ (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < section16Delta (fejerThetaOne alpha (alpha / 2) k) ∧
      section16Delta (fejerThetaOne alpha (alpha / 2) k) ≤ 1 ∧
      (section16Delta (fejerThetaOne alpha (alpha / 2) k))⁻¹ ≤ (2 / alpha) ^ (2 ^ fixDegQ k) := by
  obtain ⟨h0, h1, hi⟩ := delta_fejer_bounds5 k ha ha2
  exact ⟨h0, h1, pw_mono (two_div_ge_two ha ha2) hi (five_k_le_fixDegQ k)⟩

/-- **The Fejér base density is a reciprocal power, at `fixDegQ`.** -/
theorem baseCFQ_recipPowerLB {V : Real} {D k μV μ0 : Nat} (ha : 0 < alpha)
    (ha2 : alpha ≤ 1 / 2) (hV : 1 ≤ V) (hVμ : V ≤ 2 ^ (2 ^ μV))
    (hμ0 : max μV (fixDegQ k) + 2 ≤ μ0) :
    RecipPowerLB (2 / alpha) (baseCF V D k alpha) (D * 2 ^ μ0 + 1) (D + 1) := by
  have hX := two_div_ge_two ha ha2
  obtain ⟨hB0, hB1, hBi⟩ := budget_gen_bounds_fejerQ k ha ha2
  have hc := GenParams.slice_const_le (V := V) (B := globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k)
    (μV := μV) (k := k - 1) (μ0 := μ0) ha ha2 hV hVμ hB0 hBi hμ0
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
