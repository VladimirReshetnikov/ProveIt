import GowersSzemeredi.Proofs18CoverBudget
import GowersSzemeredi.Proofs18ThresholdAt
import GowersSzemeredi.Proofs18EnvelopeInduction

/-! The uniform `L+5` threshold for lengths at least six.

Charge the phase-refinement constants at the exponential level, bound the
resulting envelope by `500 * 2^k`, and feed it to the density iteration.
The short-length threshold comparisons are in `Proofs18CoverThresholdsSharp`.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- `2^n ≤ e^n`. -/
theorem two_pow_le_exp_nat (n : Nat) : (2 : Real) ^ n ≤ Real.exp n := by
  have h2 : (2 : Real) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : Real); linarith
  calc (2 : Real) ^ n ≤ (Real.exp 1) ^ n := pow_le_pow_left₀ (by norm_num) h2 n
    _ = Real.exp n := by rw [← Real.exp_nat_mul, mul_one]

/-- **A constant tower at the exponential level**: `2^(2^m) ≤ exp(X^(2^j))`
once `m ≤ 2^j`. -/
theorem two_tower_le_ex {X : Real} (hX : 2 ≤ X) {m j : Nat} (hmj : m ≤ 2 ^ j) :
    (2 : Real) ^ (2 ^ m) ≤ Real.exp (X ^ (2 ^ j)) := by
  refine (two_pow_le_exp_nat (2 ^ m)).trans (Real.exp_le_exp.mpr ?_)
  push_cast
  exact (pow_le_pow_left₀ (by norm_num) hX m).trans (pw_natpow hX hmj)

theorem forty_cube_le (k : Nat) : 40 * (k + 1 + 1) ^ 3 + 2 ≤ 2 ^ (k + 11) := by
  have h1 := cube_le_two_pow_sharp k
  have h2 : (k + 1 + 1) ^ 3 ≤ (k + 3) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have h3 : 2 ^ (k + 11) = 2048 * 2 ^ k := by rw [pow_add]; ring
  have h4 := Nat.one_le_two_pow (n := k)
  omega

/-- **The phase-refinement threshold, with the constants at the exponential
level.** -/
theorem inv_thr_le_ex_of_partition_bound {X : Real} (hX : 2 ≤ X) {k q : Nat} {η β e σ : Real} {M s : Nat}
    (hpart : polynomialPartitionConstant (k + 1 + 1) ≤ 2 ^ q)
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hηi : η⁻¹ ≤ X ^ (2 ^ M)) (hβi : β⁻¹ ≤ X ^ (2 ^ M)) (hs0 : 0 < σ) (hs16 : σ ≤ 16)
    (hσ'0 : 0 < inverseStepExponent (k + 1) e σ)
    (hσ' : (inverseStepExponent (k + 1) e σ)⁻¹ ≤ Real.exp (X ^ (2 ^ s))) :
    inverseStepThreshold (k + 1) η β e (6 * ((k + 1 : Nat) : Real)) σ ≤
      Real.exp (Real.exp (X ^ (2 ^ (max (max (M + q + 4) (k + 16)) s + 1)))) := by
  -- the refinement constant at `b = ηβ/2`
  have hb : 0 < η * β / 2 := by positivity
  have hbi : (η * β / 2)⁻¹ ≤ X ^ (2 ^ (M + 2)) := by
    rw [show (η * β / 2)⁻¹ = 2 * (η⁻¹ * β⁻¹) by field_simp]
    have h1 := pw_mul hX (inv_pos.mpr hη0).le (inv_pos.mpr hβ0).le hηi hβi
    exact pw_mul' hX (by norm_num) (by positivity) (hX.trans (pw_X hX M)) h1 |>.trans
      (pw_mono hX le_rfl (by omega))
  have hb1 : 1 ≤ (η * β / 2)⁻¹ := by
    rw [one_le_inv₀ hb]
    have : η * β ≤ 1 := mul_le_one₀ hη1 hβ0.le hβ1
    linarith
  have hscaled := section5LocalRefinementConstant_le_scaled (k + 1 + 1) (η * β / 2)
    (η * β / 2)⁻¹ hb hb1 le_rfl
  have hs5 : section5LocalRefinementConstant (k + 1 + 1) 1 ≤ Real.exp (X ^ (2 ^ (k + 11))) :=
    (s5_one_le (d := k + 1 + 1) (by omega)).trans (two_tower_le_ex hX (forty_cube_le k))
  have hpow : ((η * β / 2)⁻¹) ^ polynomialPartitionConstant (k + 1 + 1) ≤
      X ^ (2 ^ (M + 2 + q)) :=
    pw_pow hX (inv_pos.mpr hb).le hbi hpart
  have hR : section5LocalRefinementConstant (k + 1 + 1) (η * β / 2) ≤
      Real.exp (X ^ (2 ^ (max (k + 11) (M + 2 + q) + 1))) :=
    hscaled.trans (ex_mul' hX (pow_nonneg (inv_pos.mpr hb).le _) hs5 (ex_of_pw hpow))
  -- the count constant
  have hσ16 : σ / 16 ≤ 1 := by linarith
  have hσ16' : 0 ≤ σ / 16 := by positivity
  have hr1 : (1 : Real) ≤ 2 * ((k + 1 + 2 : Nat) : Real) := by push_cast; linarith
  have hc1 : (1 : Real) ≤ 6 * ((k + 1 : Nat) : Real) := by push_cast; linarith
  have hrpow : (2 * ((k + 1 + 2 : Nat) : Real)) ^ (1 - σ / 16) ≤
      2 * ((k + 1 + 2 : Nat) : Real) :=
    Real.rpow_le_self_of_one_le hr1 (by linarith)
  have hcpow : (6 * ((k + 1 : Nat) : Real)) ^ (σ / 16) ≤
      6 * ((k + 1 : Nat) : Real) := Real.rpow_le_self_of_one_le hc1 hσ16
  have hB0 : 0 ≤ boundaryRefinementConstant (1 / 16) := (section5LocalRefinementConstant_pos _ _).le
  have hr : 2 * ((k + 1 + 2 : Nat) : Real) ≤ X ^ (2 ^ (k + 3)) := by
    have := small_nat_le_pw hX (k := k) (c := 2 * (k + 1 + 2)) (by omega)
    push_cast at this ⊢; linarith
  have hc : 6 * ((k + 1 : Nat) : Real) ≤ X ^ (2 ^ (k + 3)) := by
    have := small_nat_le_pw hX (k := k) (c := 6 * (k + 1)) (by omega)
    push_cast at this ⊢; linarith
  have hBe : boundaryRefinementConstant (1 / 16) ≤ Real.exp (X ^ (2 ^ 11)) :=
    cubic_boundary_refinement_constant_upper.trans (two_tower_le_ex hX (by norm_num))
  have h2e : (2 : Real) ≤ Real.exp (X ^ (2 ^ 0)) :=
    ex_of_pw (hX.trans (pw_X hX 0))
  have h2B : 2 * boundaryRefinementConstant (1 / 16) ≤ Real.exp (X ^ (2 ^ (max 0 11 + 1))) :=
    ex_mul' hX hB0 h2e hBe
  have hD : inverseStepCountConstant (k + 1) (6 * ((k + 1 : Nat) : Real)) σ ≤
      Real.exp (X ^ (2 ^ (k + 14))) := by
    unfold inverseStepCountConstant localInverseAssemblyConstant
    have hmax : max 1 (2 * boundaryRefinementConstant (1 / 16) *
        (2 * ((k + 1 + 2 : Nat) : Real)) ^ (1 - σ / 16)) ≤
        Real.exp (X ^ (2 ^ (max (max 0 11 + 1) (k + 3) + 1))) :=
      max_le (Real.one_le_exp (by positivity)) (ex_mul' hX (Real.rpow_nonneg (by linarith) _) h2B
        (ex_of_pw (hrpow.trans hr)))
    have := ex_mul' hX (Real.rpow_nonneg (by linarith) _) hmax (ex_of_pw (hcpow.trans hc))
    exact ex_mono hX this (by omega)
  have hD1 : 1 ≤ inverseStepCountConstant (k + 1) (6 * ((k + 1 : Nat) : Real)) σ := by
    unfold inverseStepCountConstant localInverseAssemblyConstant
    exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) (Real.one_le_rpow hc1 hσ16')
  have hP1 : (1 : Real) ≤ polynomialPartitionConstant (k + 1 + 1) := by
    exact_mod_cast polyPartConst_pos (k + 1 + 1)
  have hDp : (inverseStepCountConstant (k + 1) (6 * ((k + 1 : Nat) : Real)) σ) ^
      ((polynomialPartitionConstant (k + 1 + 1) : Real))⁻¹ ≤
      inverseStepCountConstant (k + 1) (6 * ((k + 1 : Nat) : Real)) σ :=
    Real.rpow_le_self_of_one_le hD1 (inv_le_one_of_one_le₀ hP1)
  have hPIC : phaseInverseConstant (k + 1 + 1) (η * β / 2)
      (inverseStepCountConstant (k + 1) (6 * ((k + 1 : Nat) : Real)) σ) ≤
      Real.exp (X ^ (2 ^ (max (max (M + q + 4) (k + 16)) s))) := by
    unfold phaseInverseConstant
    have := ex_mul' hX (Real.rpow_nonneg (le_trans zero_le_one hD1) _) hR (hDp.trans hD)
    exact ex_mono hX this (by omega)
  unfold inverseStepThreshold
  have hppt := positivePowerThreshold_one_le_double_exp hσ'0.le (le_exp_exp_of_le_exp hPIC) hσ'
  refine hppt.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr ?_))
  exact pw_add hX (pw_mono hX le_rfl le_rfl) (pw_mono hX le_rfl (le_max_right _ s))

/-- The phase-refinement estimate with the original polynomial partition budget. -/
theorem inv_thr_le_ex {X : Real} (hX : 2 ≤ X) {k : Nat} {η β e σ : Real} {M s : Nat}
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hηi : η⁻¹ ≤ X ^ (2 ^ M)) (hβi : β⁻¹ ≤ X ^ (2 ^ M)) (hs0 : 0 < σ) (hs16 : σ ≤ 16)
    (hσ'0 : 0 < inverseStepExponent (k + 1) e σ)
    (hσ' : (inverseStepExponent (k + 1) e σ)⁻¹ ≤ Real.exp (X ^ (2 ^ s))) :
    inverseStepThreshold (k + 1) η β e (6 * ((k + 1 : Nat) : Real)) σ ≤
      Real.exp (Real.exp (X ^ (2 ^ (max (max (M + 4 * (k + 3) ^ 2 + 4) (k + 16)) s + 1)))) := by
  exact inv_thr_le_ex_of_partition_bound hX
    (by simpa only [show k + 1 + 1 + 1 = k + 3 by omega] using polyPartConst_le (k + 1 + 1))
    hη0 hη1 hβ0 hβ1 hηi hβi hs0 hs16 hσ'0 hσ'

/-- The envelope after one step, with the threshold, without the cubic branch. -/
def envStepCTx (k μ0 μK μ : Nat) : Nat :=
  max (GenParamsC.densDegC k μ0 + μ + 4 * (k + 3) ^ 2 + 14)
    (max (GenParamsC.threshDegC k μ0 μK + 3) (k + 20))

/-- **The single-piece step, with envelopes and the sharper phase-refinement
threshold.** -/
theorem envBound_stepCx (P : GenParamsC) {μV μK μ : Nat} (H : P.CHyp μV μK) (hk : 1 ≤ P.k)
    (hcov : ∀ l, 1 ≤ l → l ≤ P.k → PolyCoverAt l (uCount P.V (uDeg68 l)) (uExp P.V (uDeg68 l)))
    (hrec : Section16RecurrenceProfileWith P.k (familyRecThr P.k P.K P.p) (familyRecExp P.k P.p))
    (hlow : EnvBound (P.k + 1) μ) : EnvBound (P.k + 2) (envStepCTx P.k P.μ0 μK μ) := by
  intro alpha ha ha2
  have hX := two_div_ge_two ha ha2
  -- everything that mentions `P.k`, before naming it
  obtain ⟨he0, he8, hei, hy0, hyle, hyi⟩ := P.yIn_boundsC ha ha2 H.hV H.hVμ H.hμ0
  have hy2 : P.yIn alpha ≤ 1 / 2 := hyle.trans ha2
  obtain ⟨β, σ, T, hB, b0, b1, s0, s16, bi, si, Ti⟩ := hlow _ hy0 hy2
  have hstep := P.inverse_step H.hV H.hK H.hp hk hcov hrec ha ha2 hB b0 s0 s16
  obtain ⟨hEl0, hEli⟩ := P.Eloc_inv_leC H ha ha2
  obtain ⟨-, hEl2, -⟩ := P.Eloc_pos_le H.hV H.hp ha ha2
  have hTl := P.Tloc_le_expC H hk ha ha2
  set k := P.k with hkdef
  set E := GenParamsC.expDegC k P.μ0 μK with hEdef
  set Th := GenParamsC.threshDegC k P.μ0 μK with hThdef
  set dd := GenParamsC.densDegC k P.μ0 with hdddef
  set M1 := dd + 1 + μ with hM1def
  have hETh : E + 4 ≤ Th := by rw [hThdef]; unfold GenParamsC.threshDegC; exact le_max_left _ _
  have hk3 : k + 2 ≤ (k + 2) ^ 3 := Nat.le_self_pow (by norm_num) _
  obtain ⟨-, hYμ⟩ := input_scale_le (μ := μ) ha ha2 hy0 hyi
  have bi' : β⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) := bi.trans hYμ
  have si' : σ⁻¹ ≤ Real.exp ((2 / alpha) ^ (2 ^ M1)) := si.trans (Real.exp_le_exp.mpr hYμ)
  have Ti' : T ≤ Real.exp (Real.exp ((2 / alpha) ^ (2 ^ M1))) :=
    Ti.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hYμ))
  have hei' : (P.eta alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) :=
    pw_mono hX hei (by rw [hM1def, hdddef]; unfold GenParamsC.densDegC; omega)
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
    unfold envStepCTx; rw [← hdddef]; omega
  · unfold envStepCTx; rw [← hdddef, ← hThdef]; omega
  · refine max_le (dex_mono hX hshort ?_) (dex_mono hX hinv ?_)
    · unfold envStepCTx; rw [← hdddef, ← hThdef]; omega
    · unfold envStepCTx; rw [← hdddef, ← hThdef]; omega


/-- The Theorem 18.2 envelope at the tight base budget, without the cubic branch. -/
def genMuX : Nat → Nat
  | 0 => 62
  | 1 => 62
  | k + 2 => envStepCTx (k + 2) (tightMu0 (k + 2)) (genMuK (k + 2)) (genMuX (k + 1))

theorem genMuX_succ {k : Nat} (hk : 1 ≤ k) :
    genMuX (k + 1) = envStepCTx (k + 1) (tightMu0 (k + 1)) (genMuK (k + 1)) (genMuX k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rfl

theorem envBound_allX (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5)))) :
    ∀ k, 2 ≤ k → EnvBound (k + 2) (genMuX k) := by
  have hstep : ∀ k, 2 ≤ k → ∀ μ, EnvBound (k + 1) μ →
      EnvBound (k + 2) (envStepCTx k (tightMu0 k) (genMuK k) μ) := by
    intro k hk μ hlow
    let P : GenParamsC := ⟨classV Kc pc k, k, Kc k, pc k, tightMu0 k⟩
    have H : P.CHyp (tightMuV k) (genMuK k) := tightHyp_of_profiles Kc pc hK hp hconst hk
    have hcov := classCovers_of_profiles Kc pc hK hp hrec (degree := uDeg68) (k := k)
      (fun hK1 => polyCoverAt_class68 Kc pc hK1 hp)
    exact envBound_stepCx P H (by show 1 ≤ k; omega) hcov (hrec k (by omega)) hlow
  intro k hk
  exact envelope_induction (P := EnvBound) (budget := genMuX) hstep
    envBound_three (fun _ h => genMuX_succ h) k (by omega)


theorem envStepCTx_le_tight (k μ : Nat) :
    envStepCTx k (tightMu0 k) (genMuK k) μ ≤ μ + 236 * 2 ^ k + 4 * (k + 3) ^ 2 + k + 39 := by
  unfold envStepCTx GenParamsC.densDegC GenParamsC.threshDegC GenParamsC.expDegC
    GenParamsC.rhoDegC tightMu0 tightMuV genMuK fixDeg
  rw [two_pow_six_mul, two_pow_five_mul, two_pow_four_mul]
  have := Nat.lt_two_pow_self (n := k)
  generalize 4 * (k + 3) ^ 2 = q
  generalize 2 ^ k = x at *
  omega

theorem envStepCTx_ge_tight (k μ : Nat) :
    μ + 236 * 2 ^ k ≤ envStepCTx k (tightMu0 k) (genMuK k) μ := by
  unfold envStepCTx GenParamsC.densDegC GenParamsC.rhoDegC tightMu0 tightMuV fixDeg
  rw [two_pow_five_mul, two_pow_four_mul]
  generalize 4 * (k + 3) ^ 2 = q
  generalize 2 ^ k = x at *
  omega

theorem genMuX_small : genMuX 2 + 2 * 6 + 14 ≤ 2 ^ (6 + 5) ∧
    genMuX 3 + 2 * 7 + 14 ≤ 2 ^ (7 + 5) ∧ genMuX 4 ≤ 500 * 2 ^ 4 := by
  decide

/-- **The Theorem 18.2 envelope without the cubic branch is `≤ 500·2^k`**, `k ≥ 2`. -/
theorem genMuX_le : ∀ k, 2 ≤ k → genMuX k ≤ 500 * 2 ^ k := by
  intro k hk
  rcases Nat.lt_or_ge k 4 with hsmall | hk4
  · interval_cases k <;> decide
  · clear hk
    induction k, hk4 using Nat.le_induction with
    | base => exact genMuX_small.2.2
    | succ k hk ih =>
      rw [genMuX_succ (by omega)]
      have h1 := envStepCTx_le_tight (k + 1) (genMuX k)
      have h2 := sq_le_two_pow_four k hk
      have h3 : 16 ≤ 2 ^ k := le_trans (by norm_num : 16 ≤ 2 ^ 4) (Nat.pow_le_pow_right (by norm_num) hk)
      have h4 := Nat.lt_two_pow_self (n := k)
      rw [show k + 1 + 3 = k + 4 by ring] at h1
      rw [pow_succ] at h1 ⊢
      generalize (k + 4) ^ 2 = s at *
      generalize 2 ^ k = x at *
      omega

theorem genMuX_ge : ∀ k, 2 ≤ k → 236 * 2 ^ k ≤ genMuX k := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [genMuX_succ (by omega)]
  have := envStepCTx_ge_tight (j + 1) (genMuX j)
  omega

/-- **Theorem 18.2 at every length `L ≥ 6` with `L + 5` in the threshold**,
from the recurrence profiles. -/
theorem theorem_18_2_L5_all_of_profiles_cover (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {L : Nat} (hL6 : 6 ≤ L) : Theorem182AtSharp 5 L := by
  have henv := envBound_allX Kc pc hK hp hrec hconst (L - 4) (by omega)
  rw [show L - 4 + 2 = L - 2 by omega] at henv
  have hge := genMuX_ge (L - 4) (by omega)
  have hk := Nat.lt_two_pow_self (n := L - 4)
  have hpow := Nat.lt_two_pow_self (n := genMuX (L - 4))
  have hle := genMuX_le (L - 4) (by omega)
  refine theorem182AtSharp_of_envBound (by omega) henv (by omega) (by omega) ?_
  have h2 : 2 ^ (L + 5) = 512 * 2 ^ (L - 4) := by
    rw [show L + 5 = (L - 4) + 9 by omega, pow_add]; ring
  rw [h2]
  omega

end LeanProofs.GowersSzemeredi
