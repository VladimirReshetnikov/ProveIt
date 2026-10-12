import GowersSzemeredi.Proofs18CoverFejerHeadlineT

/-! **Theorem 18.2 and Corollary 18.7 at `L + 2` for every `L ≥ 13`, from the
recurrence profiles** (Notes L.16l).

The Theorem 18.2 envelope of `Proofs18CoverFejerHeadlineT` carries the
threshold branch `2^(k+6) + 8`, which keeps it at `64·2^k` and blocks
`L + 2`. That branch comes from `zeta_gen_bounds_fejer`, which bounds the
inverse tight Bohr radius by `exp(X^(2^(2^(k+6)+1)))` through the printed
`θ₁`. Under the Fejér `θ₁` the radius is polynomial in `θ₁′⁻¹`:
* `zeta_gen_bounds_fejer5`: `ζ⁻¹ ≤ exp(X^(2^(5k+21)))`, from
  `tightZeta_fejer_inv_le_gen` and `fejerProductExponent k ≤ 2^(5k+14)`;
* `GenParamsT.MReq_le_expU`, `GenParamsT.Tloc_le_expU`: the requirement on
  `m` and the modulus threshold at `threshDegU`, which is
  `max(expDeg + 4, 16·2^k + 5k + 25)` instead of `max(expDeg + 4, 64·2^k + 5)`
  (generated from the T versions);
* `envBound_stepUx`, `genMuXU`, `envBound_allXU`: the Theorem 18.2 envelope
  with that threshold (generated). Each step is now at most
  `max(μ + 28·2^k + O(k²), 32·2^k + 9)` (`envStepUTx_le_tight`), and at least
  `32·2^k + 9`;
* `genMuXU_small64` (`decide +kernel`, `k = 9, …, 12`) and `genMuXU_le64`
  (`μ_k + 4k + 128 ≤ 64·2^k` for `k ≥ 12`);
* `theorem_18_2_L2_thirteen_le_of_profiles_cover`,
  `corollary_18_7_L2_thirteen_le_of_profiles_cover`: `L + 2` at every length
  `L ≥ 13`. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- **The tight Bohr radius under the Fejér `θ₁` is polynomial**:
`ζ⁻¹ ≤ exp(X^(2^(5k+21)))`. -/
theorem zeta_gen_bounds_fejer5 (k : Nat) {alpha : Real} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < tightZeta (fejerThetaOne alpha (alpha / 2) k / 4) ∧
      (tightZeta (fejerThetaOne alpha (alpha / 2) k / 4))⁻¹ ≤
        Real.exp ((2 / alpha) ^ (2 ^ (5 * k + 21))) := by
  have hX := two_div_ge_two ha ha2
  obtain ⟨h0, -, hi⟩ := tightZeta_fejer_inv_le_gen (gamma := alpha / 2) (theta := alpha) k
    (half_pos ha) (by linarith) ha (by linarith)
  refine ⟨h0, hi.trans (Real.exp_le_exp.mpr ?_)⟩
  have hval : 2 / (alpha / 2 * alpha) = (2 / alpha) ^ 2 := by field_simp <;> ring
  rw [hval, ← pow_mul]
  refine pow_le_pow_right₀ (by linarith) ?_
  have hF := fejerProductExponent_le k
  have h14 : 2 ^ 14 ≤ 2 ^ (5 * k + 14) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h21 : 2 ^ (5 * k + 21) = 128 * 2 ^ (5 * k + 14) := by
    rw [show 5 * k + 21 = (5 * k + 14) + 7 by ring, pow_add]; ring
  unfold fejerStepT
  omega

namespace GenParamsT

variable (P : GenParamsT) {alpha : Real}

/-- The modulus-threshold degree with the polynomial Bohr radius. -/
def threshDegU (k μ0 μK : Nat) : Nat := max (expDegT k μ0 μK + 4) (2 ^ (k + 4) + 5 * k + 25)

/-- **The requirement on `m`**. -/
theorem MReq_le_expU {μV μK : Nat} (H : CHyp P μV μK) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    1 ≤ P.MReq alpha ∧
      P.MReq alpha ≤ Real.exp ((2 / alpha) ^ (2 ^ max (expDegT P.k P.μ0 μK + 3) (5 * P.k + 24))) := by
  have hX := two_div_ge_two ha ha2
  have hX1 : (1 : Real) ≤ 2 / alpha := by linarith
  obtain ⟨-, hQM, hBx⟩ := P.spectrum_exps_inv_leT H ha ha2
  have hri := P.rho1_inv_leT ha ha2 H.hV H.hVμ H.hμ0
  set k := P.k with hkdef
  set E := expDegT k P.μ0 μK with hEdef
  set Z := 5 * k + 21 with hZdef
  have hZ2 : 2 ≤ Z := by rw [hZdef]; omega
  have hρE : rhoDegT k P.μ0 + tDeg k + k + 7 ≤ E := by
    rw [hEdef]; unfold expDegT; exact (le_max_left _ _).trans (le_max_right _ _)
  have hKE : μK + 2 ≤ E := by
    rw [hEdef]; unfold expDegT; exact (le_max_right _ _).trans (le_max_right _ _)
  -- the recurrence threshold
  have hthr := familyRecThr_le_exp (k := k) hX (by have := H.hK; omega) H.hKμ H.hpμ hQM
  have hthr' : (familyRecThr k P.K P.p (P.QM alpha) : Real) ≤
      Real.exp ((2 / alpha) ^ (2 ^ (E + 3))) := ex_mono hX hthr (by omega)
  have hthr1 : (1 : Real) ≤ (familyRecThr k P.K P.p (P.QM alpha) : Real) :=
    Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr
      (familyRecThr_pos (k := k) (p := P.p) (by have := H.hK; omega) _).ne')
  -- the Bohr radius and `ρ`
  obtain ⟨hz0, hzi⟩ := zeta_gen_bounds_fejer5 k ha ha2
  have hz1 : tightZeta (fejerThetaOne alpha (alpha / 2) k / 4) ≤ 1 / 2 :=
    (tightZeta_pos_le_half (fejerThetaOne_bounds k ha (by linarith) (half_pos ha) (by linarith)).1 (by linarith [(fejerThetaOne_bounds k ha (by linarith) (half_pos ha) (by linarith)).2])).2
  have hzeq : P.Zeta alpha = tightZeta (fejerThetaOne alpha (alpha / 2) k / 4) := rfl
  obtain ⟨ht0, ht1, -⟩ := T2_gen_bounds_fejerQ k ha ha2
  obtain ⟨hr0, hr1⟩ : 0 < P.Rho1 alpha ∧ P.Rho1 alpha ≤ 1 := P.rho1_pos_le ha ha2
  have hρ1 : 1 ≤ rhoDegT k P.μ0 := by have := (rhoDegT_ge k P.μ0).1; omega
  obtain ⟨hR0, hR1, hRi⟩ := GenParams.rho_step hX hr0 hr1 hri hρ1
  have hReq : P.Rho alpha = P.Rho1 alpha / 2 * (P.Rho1 alpha / 2 / 2) := rfl
  rw [← hReq] at hR0 hR1 hRi
  have hBpos : 0 < P.Bexp alpha := by
    have := familyRecExp_pos k P.p (P.QM alpha) H.hp
    show 0 < familyRecExp k P.p _ / 2; exact half_pos this
  set z := P.Zeta alpha with hzdef
  set R := P.Rho alpha with hRdef
  set B := P.Bexp alpha with hBdef
  rw [← hzeq] at hz0 hzi hz1
  have h8 : (8 : Real) ≤ Real.exp ((2 / alpha) ^ (2 ^ 2)) := ex_of_pw (pw_const hX (by norm_num))
  have hzi' : z⁻¹ ≤ Real.exp ((2 / alpha) ^ (2 ^ Z)) := hzi
  have h8z : 8 / z ≤ Real.exp ((2 / alpha) ^ (2 ^ (Z + 1))) := by
    rw [div_eq_mul_inv]
    exact ex_mono hX (ex_mul' hX (inv_pos.mpr hz0).le h8 hzi') (by omega)
  have h16 : (16 : Real) ≤ Real.exp ((2 / alpha) ^ (2 ^ 2)) := ex_of_pw (pw_const hX (by norm_num))
  have h16z : 16 / z ≤ Real.exp ((2 / alpha) ^ (2 ^ (Z + 1))) := by
    rw [div_eq_mul_inv]
    exact ex_mono hX (ex_mul' hX (inv_pos.mpr hz0).le h16 hzi') (by omega)
  have hR3 : (R ^ 3)⁻¹ ≤ (2 / alpha) ^ (2 ^ (rhoDegT k P.μ0 + 2 + 2)) := by
    rw [← inv_pow]; exact pw_pow hX (inv_pos.mpr hR0).le hRi (by norm_num)
  have h4zr : 4 / (z * R ^ 3) ≤
      Real.exp ((2 / alpha) ^ (2 ^ (max (Z + 1) (rhoDegT k P.μ0 + 4) + 1))) := by
    rw [div_eq_mul_inv, mul_inv, ← mul_assoc]
    have h4z : 4 * z⁻¹ ≤ Real.exp ((2 / alpha) ^ (2 ^ (Z + 1))) := by
      have h4 : (4 : Real) ≤ Real.exp ((2 / alpha) ^ (2 ^ 2)) := ex_of_pw (pw_const hX (by norm_num))
      exact ex_mono hX (ex_mul' hX (inv_pos.mpr hz0).le h4 hzi') (by omega)
    exact ex_mul' hX (inv_pos.mpr (pow_pos hR0 3)).le h4z (ex_of_pw hR3)
  have h8z1 : 1 ≤ 8 / z := by rw [le_div_iff₀ hz0]; linarith
  have h16z1 : 1 ≤ 16 / z := by rw [le_div_iff₀ hz0]; linarith
  have h4zr1 : 1 ≤ 4 / (z * R ^ 3) := by
    rw [le_div_iff₀ (mul_pos hz0 (pow_pos hR0 3))]
    have : R ^ 3 ≤ 1 := pow_le_one₀ hR0.le hR1
    have : z * R ^ 3 ≤ 1 / 2 * 1 := mul_le_mul hz1 this (pow_pos hR0 3).le (by norm_num)
    linarith
  have hBe : 1 / B ≤ (2 / alpha) ^ (2 ^ E) := by rw [one_div]; exact hBx
  have hBe2 : 2 / B ≤ (2 / alpha) ^ (2 ^ (E + 1)) := by
    rw [div_eq_mul_inv]
    exact pw_mul hX (by norm_num) (inv_pos.mpr hBpos).le (hX.trans (pw_X hX _)) hBx
  have e1 := ex_rpow hX h8z1 h8z (div_nonneg zero_le_one hBpos.le) hBe
  have e2 := ex_rpow hX h4zr1 h4zr (div_nonneg zero_le_one hBpos.le) hBe
  have e3 := ex_rpow hX h16z1 h16z (div_nonneg zero_le_two hBpos.le) hBe2
  refine ⟨hthr1.trans (le_max_left _ _), ?_⟩
  show max (familyRecThr k P.K P.p (P.QM alpha) : Real)
    (max ((8 / z) ^ (1 / B)) (max ((4 / (z * R ^ 3)) ^ (1 / B)) ((16 / z) ^ (2 / B)))) ≤ _
  refine max_le (ex_mono hX hthr' (le_max_left _ _)) (max_le ?_ (max_le ?_ ?_))
  · exact ex_mono hX e1 (by rw [hZdef]; omega)
  · exact ex_mono hX e2 (by rw [hZdef]; omega)
  · exact ex_mono hX e3 (by rw [hZdef]; omega)

/-- **The modulus threshold of the step is single exponential.** -/
theorem Tloc_le_expU {μV μK : Nat} (H : CHyp P μV μK) (hk : 1 ≤ P.k) (ha : 0 < alpha)
    (ha2 : alpha ≤ 1 / 2) :
    P.Tloc alpha ≤ Real.exp ((2 / alpha) ^ (2 ^ threshDegU P.k P.μ0 μK)) := by
  have hX := two_div_ge_two ha ha2
  have hX1 : (1 : Real) ≤ 2 / alpha := by linarith
  obtain ⟨hEl0, hEli⟩ := P.Eloc_inv_leT H ha ha2
  obtain ⟨hEm, -, -⟩ := P.spectrum_exps_inv_leT H ha ha2
  have hNE := P.nestExp_inv_leT ha ha2 H.hV H.hVμ H.hμ0
  obtain ⟨-, -, -, -, -, -, -, ⟨hEm0, -⟩, -, -, ⟨hN0, -, -⟩, -, -, -⟩ :=
    P.ranges H.hV H.hp ha ha2
  obtain ⟨hR1, hR⟩ := P.MReq_le_expU H ha ha2
  have hL := lemma156_gen_le_fejer hk ha ha2
  set k := P.k with hkdef
  set E := expDegT k P.μ0 μK with hEdef
  set T := threshDegU k P.μ0 μK with hTdef
  set μD := tDeg k with hμDdef
  have hET : E + 4 ≤ T := by rw [hTdef]; unfold threshDegU; exact le_max_left _ _
  have hZT : 2 ^ (k + 4) + 5 * k + 25 ≤ T := by rw [hTdef]; unfold threshDegU; exact le_max_right _ _
  have hρE : rhoDegT k P.μ0 + μD + k + 7 ≤ E := by
    rw [hEdef]; unfold expDegT; exact (le_max_left _ _).trans (le_max_right _ _)
  obtain ⟨hρ0, hρ2⟩ := rhoDegT_ge k P.μ0
  have hNE' : (P.NestExp alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ E) := pw_mono hX hNE (by omega)
  have hEm' : (P.Em alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ E) := pw_mono hX hEm (by omega)
  have hMx : (P.MExp alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ (E + 2)) := by
    show (P.NestExp alpha * (P.Em alpha / 2))⁻¹ ≤ _
    rw [show (P.NestExp alpha * (P.Em alpha / 2))⁻¹ =
      2 * ((P.NestExp alpha)⁻¹ * (P.Em alpha)⁻¹) by field_simp]
    have p1 := pw_mul hX (inv_pos.mpr hN0).le (inv_pos.mpr hEm0).le hNE' hEm'
    exact pw_mul hX (by norm_num) (mul_nonneg (inv_pos.mpr hN0).le (inv_pos.mpr hEm0).le)
      (hX.trans (pw_X hX _)) p1
  have hMx0 : 0 < P.MExp alpha := by
    show 0 < P.NestExp alpha * (P.Em alpha / 2)
    exact mul_pos hN0 (half_pos hEm0)
  -- the roots
  have h64 : (64 : Real) ^ (1 / P.NestExp alpha) ≤ Real.exp ((2 / alpha) ^ (2 ^ T)) :=
    ex_mono hX (ex_root (j := 3) hX (by norm_num) (by norm_num) hN0 hNE') (by omega)
  have h4 : (4 : Real) ^ (1 / P.NestExp alpha) ≤ Real.exp ((2 / alpha) ^ (2 ^ T)) :=
    ex_mono hX (ex_root (j := 2) hX (by norm_num) (by norm_num) hN0 hNE') (by omega)
  have h6 : (6 : Real) ^ (1 / P.Eloc alpha) ≤ Real.exp ((2 / alpha) ^ (2 ^ T)) :=
    ex_mono hX (ex_root (j := 2) hX (by norm_num) (by norm_num) hEl0 hEli) (by omega)
  have hF : P.F alpha = 8 * P.Eloc alpha := by show P.F alpha = 8 * (P.F alpha / 8); ring
  have h8 : (8 : Real) ^ (2 / P.F alpha) ≤ Real.exp ((2 / alpha) ^ (2 ^ T)) := by
    have hle : 2 / P.F alpha ≤ 1 / P.Eloc alpha := by
      rw [hF, div_le_div_iff₀ (mul_pos (by norm_num) hEl0) hEl0]; nlinarith
    refine (Real.rpow_le_rpow_of_exponent_le (by norm_num) hle).trans ?_
    exact ex_mono hX (ex_root (j := 2) hX (by norm_num) (by norm_num) hEl0 hEli) (by omega)
  -- the requirement on `m`
  have hMR : P.MReq alpha ^ (1 / P.MExp alpha) ≤ Real.exp ((2 / alpha) ^ (2 ^ T)) := by
    rw [one_div]
    refine ex_mono hX (ex_rpow hX hR1 hR (inv_pos.mpr hMx0).le hMx) ?_
    have := hET; have := hZT; have := Nat.two_pow_pos (k + 4)
    simp only [max_def]; split_ifs <;> omega
  have hMT : P.MThr alpha ≤ Real.exp ((2 / alpha) ^ (2 ^ T)) :=
    max_le (Real.one_le_exp (pow_nonneg (by linarith) _)) h64
  -- Lemma 15.6
  have hL' : fejerProductThreshold k (alpha / 2) (alpha / 2) ≤
      Real.exp ((2 / alpha) ^ (2 ^ T)) := by
    refine ex_of_pw (pw_mono hX hL ?_)
    have : 2 ^ (k + 4) + 4 * k + 13 ≤ 2 ^ (k + 4) + 5 * k + 25 := by omega
    omega
  have h3 : (3 : Real) ≤ Real.exp ((2 / alpha) ^ (2 ^ T)) :=
    ex_of_pw (pw_const hX (by
      calc (3 : Real) ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 ^ T) := pow_le_pow_right₀ (by norm_num) (by
            have := Nat.lt_two_pow_self (n := T); omega)))
  show max (max 3 (fejerProductThreshold k (alpha / 2) (alpha / 2)))
    (max (P.MThr alpha)
      (max (4 ^ (1 / P.NestExp alpha))
        (max (P.MReq alpha ^ (1 / P.MExp alpha))
          (max (6 ^ (1 / P.Eloc alpha)) (8 ^ (2 / P.F alpha)))))) ≤ _
  exact max_le (max_le h3 hL') (max_le hMT (max_le h4 (max_le hMR (max_le h6 h8))))

end GenParamsT

/-- The envelope after one step, with the threshold, without the cubic branch. -/
def envStepUTx (k μ0 μK μ : Nat) : Nat :=
  max (GenParamsT.densDegT k μ0 + μ + 4 * (k + 3) ^ 2 + 14)
    (max (GenParamsT.threshDegU k μ0 μK + 3) (k + 20))

/-- **The single-piece step, with envelopes and the sharper phase-refinement
threshold.** -/
theorem envBound_stepUx (P : GenParamsT) {μV μK μ : Nat} (H : P.CHyp μV μK) (hk : 1 ≤ P.k)
    (hcov : ∀ l, 1 ≤ l → l ≤ P.k → PolyCoverAt l (uCount P.V (uDegT l)) (uExp P.V (uDegT l)))
    (hrec : Section16RecurrenceProfileWith P.k (familyRecThr P.k P.K P.p) (familyRecExp P.k P.p))
    (hlow : EnvBound (P.k + 1) μ) : EnvBound (P.k + 2) (envStepUTx P.k P.μ0 μK μ) := by
  intro alpha ha ha2
  have hX := two_div_ge_two ha ha2
  -- everything that mentions `P.k`, before naming it
  obtain ⟨he0, he8, hei, hy0, hyle, hyi⟩ := P.yIn_boundsT ha ha2 H.hV H.hVμ H.hμ0
  have hy2 : P.yIn alpha ≤ 1 / 2 := hyle.trans ha2
  obtain ⟨β, σ, T, hB, b0, b1, s0, s16, bi, si, Ti⟩ := hlow _ hy0 hy2
  have hstep := P.inverse_step H.hV H.hK H.hp hk hcov hrec ha ha2 hB b0 s0 s16
  obtain ⟨hEl0, hEli⟩ := P.Eloc_inv_leT H ha ha2
  obtain ⟨-, hEl2, -⟩ := P.Eloc_pos_le H.hV H.hp ha ha2
  have hTl := P.Tloc_le_expU H hk ha ha2
  set k := P.k with hkdef
  set E := GenParamsT.expDegT k P.μ0 μK with hEdef
  set Th := GenParamsT.threshDegU k P.μ0 μK with hThdef
  set dd := GenParamsT.densDegT k P.μ0 with hdddef
  set M1 := dd + 1 + μ with hM1def
  have hETh : E + 4 ≤ Th := by rw [hThdef]; unfold GenParamsT.threshDegU; exact le_max_left _ _
  have hk3 : k + 2 ≤ (k + 2) ^ 3 := Nat.le_self_pow (by norm_num) _
  obtain ⟨-, hYμ⟩ := input_scale_le (μ := μ) ha ha2 hy0 hyi
  have bi' : β⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) := bi.trans hYμ
  have si' : σ⁻¹ ≤ Real.exp ((2 / alpha) ^ (2 ^ M1)) := si.trans (Real.exp_le_exp.mpr hYμ)
  have Ti' : T ≤ Real.exp (Real.exp ((2 / alpha) ^ (2 ^ M1))) :=
    Ti.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hYμ))
  have hei' : (P.eta alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) :=
    pw_mono hX hei (by rw [hM1def, hdddef]; unfold GenParamsT.densDegT; omega)
  have heta1 : P.eta alpha ≤ 1 := by linarith
  -- the localization exponent and `σ′`
  obtain ⟨σ0', σ16', σeq⟩ := sigma_step (d := k + 1) hEl0 hEl2 s0 s16
  have h32P : 32 * (polynomialPartitionConstant (k + 1 + 1) : Real) ≤
      (2 / alpha) ^ (2 ^ (4 * (k + 3) ^ 2 + 4)) := by
    refine pw_const hX ?_
    have hP := polyPartConst_le (k + 1 + 1)
    rw [show k + 1 + 1 + 1 = k + 3 by ring] at hP
    have hn : 4 * (k + 3) ^ 2 + 5 ≤ 2 ^ (4 * (k + 3) ^ 2 + 4) :=
      Nat.lt_two_pow_self (n := 4 * (k + 3) ^ 2 + 4)
    have hnat : 32 * polynomialPartitionConstant (k + 1 + 1) ≤ 2 ^ (2 ^ (4 * (k + 3) ^ 2 + 4)) := by
      calc 32 * polynomialPartitionConstant (k + 1 + 1) ≤ 2 ^ 5 * 2 ^ (4 * (k + 3) ^ 2) :=
            Nat.mul_le_mul (by norm_num) hP
        _ = 2 ^ (4 * (k + 3) ^ 2 + 5) := by rw [← pow_add]; ring_nf
        _ ≤ 2 ^ (2 ^ (4 * (k + 3) ^ 2 + 4)) := Nat.pow_le_pow_right (by norm_num) hn
    exact_mod_cast hnat
  set S := max (max (4 * (k + 3) ^ 2 + 4) (E + 3) + 1) M1 + 1 with hSdef
  have hσ' : (inverseStepExponent (k + 1) (P.Eloc alpha) σ)⁻¹ ≤
      Real.exp ((2 / alpha) ^ (2 ^ S)) := by
    rw [σeq]
    have h1 := pw_mul' hX (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (inv_pos.mpr hEl0).le
      h32P hEli
    exact ex_mul' hX (inv_pos.mpr s0).le (ex_of_pw h1) si'
  -- the thresholds
  have hc : 6 * ((k + 1 : Nat) : Real) ≤ 2 ^ (2 ^ (k + 3)) := by
    have := small_nat_le_pw (le_refl (2 : Real)) (k := k) (c := 6 * (k + 1)) (by omega)
    push_cast at this ⊢; linarith
  have hd : (((k + 1 + 2 : Nat) : Real) ^ (2 : Nat)) ≤ 2 ^ (2 ^ (k + 3)) := by
    have h1 : k + 1 + 2 ≤ 2 ^ (k + 3) := by
      have := Nat.lt_two_pow_self (n := k + 3); omega
    have h2 : 2 * (k + 3) ≤ 2 ^ (k + 3) := by
      have := Nat.lt_two_pow_self (n := k + 2); rw [pow_succ]; omega
    have hnat : (k + 1 + 2) ^ 2 ≤ 2 ^ (2 ^ (k + 3)) :=
      calc (k + 1 + 2) ^ 2 ≤ (2 ^ (k + 3)) ^ 2 := Nat.pow_le_pow_left h1 2
        _ = 2 ^ (2 * (k + 3)) := by rw [← pow_mul]; ring_nf
        _ ≤ 2 ^ (2 ^ (k + 3)) := Nat.pow_le_pow_right (by norm_num) h2
    exact_mod_cast hnat
  have hshort := short_thr_le hX (d := k + 1) (j := k + 3) hEl0 hEli (by positivity) hc Ti' hTl hd
  have hinv := inv_thr_le_ex hX (k := k) he0 heta1 b0 b1 hei' bi' s0 s16 σ0' hσ'
  -- assemble
  refine ⟨P.eta alpha * β / 4, _, _, hstep, div_pos (mul_pos he0 b0) (by norm_num), ?_, σ0', σ16',
    ?_, ex_mono hX hσ' ?_, ?_⟩
  · have : P.eta alpha * β ≤ 1 := mul_le_one₀ heta1 b0.le b1
    linarith
  · rw [show (P.eta alpha * β / 4)⁻¹ = 4 * ((P.eta alpha)⁻¹ * β⁻¹) by field_simp]
    have h1 := pw_mul hX (inv_pos.mpr he0).le (inv_pos.mpr b0).le hei' bi'
    have h4 : (4 : Real) ≤ (2 / alpha) ^ (2 ^ (M1 + 1)) :=
      (four_le_pw_one hX).trans (pw_mono hX le_rfl (by omega))
    refine (pw_mul hX (by norm_num) (mul_nonneg (inv_pos.mpr he0).le (inv_pos.mpr b0).le) h4 h1).trans
      (pw_mono hX le_rfl ?_)
    unfold envStepUTx; rw [← hdddef]; omega
  · unfold envStepUTx; rw [← hdddef, ← hThdef]; omega
  · refine max_le (dex_mono hX hshort ?_) (dex_mono hX hinv ?_)
    · unfold envStepUTx; rw [← hdddef, ← hThdef]; omega
    · unfold envStepUTx; rw [← hdddef, ← hThdef]; omega



/-- The Theorem 18.2 envelope at the tight base budget, without the cubic branch. -/
def genMuXU : Nat → Nat
  | 0 => 62
  | 1 => 62
  | k + 2 => envStepUTx (k + 2) (tightMu0T (k + 2)) (genMuK (k + 2)) (genMuXU (k + 1))

theorem genMuXU_succ {k : Nat} (hk : 1 ≤ k) :
    genMuXU (k + 1) = envStepUTx (k + 1) (tightMu0T (k + 1)) (genMuK (k + 1)) (genMuXU k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rfl

theorem envBound_allXU (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5)))) :
    ∀ k, 2 ≤ k → EnvBound (k + 2) (genMuXU k) := by
  have hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))) :=
    fun k hk => abstractFamilyLemma166At_of k (hK k) (hp k) (hrec k hk)
  have hK1 : ∀ k, 1 ≤ Kc k := fun k => le_trans (by norm_num) (hK k)
  have hstep : ∀ k, 2 ≤ k → ∀ μ, EnvBound (k + 1) μ →
      EnvBound (k + 2) (envStepUTx k (tightMu0T k) (genMuK k) μ) := by
    intro k hk μ hlow
    let P : GenParamsT := ⟨classV Kc pc k, k, Kc k, pc k, tightMu0T k⟩
    have H : P.CHyp (tightMuV k) (genMuK k) := tightHyp_of_profiles_fejerT Kc pc hK hp hconst hk
    have hcov : ∀ l, 1 ≤ l → l ≤ P.k →
        PolyCoverAt l (uCount P.V (uDegT l)) (uExp P.V (uDegT l)) := by
      intro l hl1 hlk
      have hcl := polyCoverAt_classT Kc pc hK1 hp hlem hl1
      exact hcl.uniform_mono (one_le_classV Kc pc l) (classV_mono Kc pc hlk) le_rfl
    exact envBound_stepUx P H (by show 1 ≤ k; omega) hcov (hrec k (by omega)) hlow
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact hstep 2 le_rfl 62 envBound_three
  | succ k hk ih =>
    rw [genMuXU_succ (by omega)]
    exact hstep (k + 1) (by omega) (genMuXU k) ih





/-! ### Closed forms -/

/-- Beyond the table one Theorem 18.2 step costs `28·2^k` plus a polynomial,
or at most `32·2^k + 9`. -/
theorem envStepUTx_le_tight {k : Nat} (hk : 13 ≤ k) (μ : Nat) :
    envStepUTx k (tightMu0T k) (genMuK k) μ ≤
      max (μ + 28 * 2 ^ k + 9 * (k + 4) ^ 2 + 4 * (k + 3) ^ 2 + k + 135) (32 * 2 ^ k + 9) := by
  unfold envStepUTx GenParamsT.densDegT GenParamsT.threshDegU GenParamsT.expDegT
    GenParamsT.rhoDegT tightMu0T tightMuV genMuK
  rw [tDeg_eq_of_ge hk, fixDegQ_eq (by omega), two_pow_five_mul, two_pow_four_mul]
  have := Nat.lt_two_pow_self (n := k)
  generalize 4 * (k + 3) ^ 2 = q
  generalize (k + 4) ^ 2 = s
  generalize 2 ^ k = x at *
  omega

/-- Every Theorem 18.2 step is at least `32·2^k + 9`. -/
theorem envStepUTx_ge (k μ0 μ : Nat) : 32 * 2 ^ k + 9 ≤ envStepUTx k μ0 (genMuK k) μ := by
  unfold envStepUTx GenParamsT.threshDegU GenParamsT.expDegT genMuK
  rw [two_pow_five_mul]
  omega

/-- The kernel-evaluated envelope in dimensions `9, …, 12`. -/
theorem genMuXU_small64 {k : Nat} (h9 : 9 ≤ k) (h12 : k ≤ 12) :
    genMuXU k + 2 * (k + 4) + 14 ≤ 64 * 2 ^ k := by
  interval_cases k <;> decide +kernel

theorem genMuXU_twelve : genMuXU 12 + 4 * 12 + 128 ≤ 64 * 2 ^ 12 := by decide +kernel

/-- **The Theorem 18.2 envelope beyond the table**: `μ_k + 4k + 128 ≤ 64·2^k`
for `k ≥ 12`. -/
theorem genMuXU_le64 : ∀ k, 12 ≤ k → genMuXU k + 4 * k + 128 ≤ 64 * 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact genMuXU_twelve
  | succ k hk ih =>
    rw [genMuXU_succ (by omega)]
    have h1 := envStepUTx_le_tight (k := k + 1) (by omega) (genMuXU k)
    have h2 := four_sq_le_two_pow_ten k (by omega)
    have h3 : (k + 4) ^ 2 ≤ (k + 5) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h4 : k + 140 ≤ 2 ^ k := le_trans (by nlinarith) h2
    rw [show k + 1 + 4 = k + 5 by ring, show k + 1 + 3 = k + 4 by ring] at h1
    rw [pow_succ] at h1 ⊢
    generalize (k + 5) ^ 2 = s5 at *
    generalize (k + 4) ^ 2 = s4 at *
    generalize 2 ^ k = x at *
    omega

/-- **The Theorem 18.2 envelope fits `64·2^k` in every dimension `k ≥ 9`.** -/
theorem genMuXU_fit64 {k : Nat} (hk : 9 ≤ k) : genMuXU k + 2 * (k + 4) + 14 ≤ 64 * 2 ^ k := by
  rcases Nat.lt_or_ge k 13 with h | h
  · exact genMuXU_small64 hk (by omega)
  · have := genMuXU_le64 k (by omega); omega

theorem genMuXU_ge {k : Nat} (hk : 2 ≤ k) : 32 * 2 ^ k + 9 ≤ genMuXU k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [genMuXU_succ (by omega)]
  exact envStepUTx_ge _ _ _

/-! ### The headline statements -/

/-- **Theorem 18.2 at every length `L ≥ 13` with `L + 2` in the threshold**,
from the recurrence profiles. -/
theorem theorem_18_2_L2_thirteen_le_of_profiles_cover (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {L : Nat} (hL : 13 ≤ L) : Theorem182AtSharp 2 L := by
  have henv := envBound_allXU Kc pc hK hp hrec hconst (L - 4) (by omega)
  rw [show L - 4 + 2 = L - 2 by omega] at henv
  have hge := genMuXU_ge (k := L - 4) (by omega)
  have hfit := genMuXU_fit64 (k := L - 4) (by omega)
  have hk := Nat.lt_two_pow_self (n := L - 4)
  have h42 : 42 ≤ genMuXU (L - 4) := by omega
  have hLμ : 4 * L + 20 ≤ 2 ^ genMuXU (L - 4) := by
    have := Nat.lt_two_pow_self (n := genMuXU (L - 4))
    omega
  refine theorem182AtSharp_of_envBound (by omega) henv h42 hLμ ?_
  have h2 : 2 ^ (L + 2) = 64 * 2 ^ (L - 4) := by
    rw [show L + 2 = (L - 4) + 6 by omega, pow_add]; ring
  rw [h2]
  omega

/-- **Corollary 18.7 at every length `L ≥ 13` with `L + 2`**, from the profiles. -/
theorem corollary_18_7_L2_thirteen_le_of_profiles_cover (Kc pc : Nat → Nat)
    (hK : ∀ k, 2 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {L : Nat} (hL : 13 ≤ L) : Corollary187AtSharp 2 L :=
  (theorem_18_2_L2_thirteen_le_of_profiles_cover Kc pc hK hp hrec hconst hL).corollary_18_7

end LeanProofs.GowersSzemeredi
