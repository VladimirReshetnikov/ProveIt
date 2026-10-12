import GowersSzemeredi.Proofs18CoverExponentsFejerQ
import GowersSzemeredi.Proofs18CoverFejerHeadline

/-! **Theorem 18.1 at `d + 5` for every `d ≥ 12` and Theorem 18.2 /
Corollary 18.7 at `L + 3` for every `L ≥ 14`, from the recurrence profiles**
(Notes L.16i).

The Section 18 envelope at `GenParamsQ`. The class covers sit at degree
`uDegQ l = 2^qDeg l`, `qDeg l = 14·2^l + 3(l+4)² + 2`
(`polyCoverAt_classQ`, from the split invariant with additive slack). The
base budget is `tightMu0Q k = max(tightMuV k, fixDegQ k) + 2 = 2^(k+4) + 9`,
the class-base term, since the Fejér θ₁ no longer forces the printed
`2^(k+5) + 9`. The step lemmas and recursions are generated from
`Proofs18CoverFejerHeadline`; the closed forms are new.

One step now costs exactly `58·2^k + 9(k+4)² + 4(k+3)² + k + 45`
(`envStepQ_le_tight`), so the envelope tends to `116·2^k < 128·2^k`. The
polynomial terms are absorbed from `k = 10` (`polyGenMuQ_le`,
`genMuXQ_le`: `μ_k + 4k + 128 ≤ 128·2^k`). This yields:
* `theorem_18_1_d5_of_profiles_cover`: Theorem 18.1 with exponent
  `α^(2^(2^(d+5)))` at every degree `d ≥ 12`;
* `theorem_18_2_L3_of_profiles_cover`, `corollary_18_7_L3_of_profiles_cover`:
  `L + 3` at every length `L ≥ 14`.
Smaller degrees and lengths keep `d + 6` / `L + 4`
(`Proofs18CoverFejerHeadline`). -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The base budget at the class-base term. -/
def tightMu0Q (k : Nat) : Nat := max (tightMuV k) (fixDegQ k) + 2

/-- The envelope after one step (no threshold). -/
def envStepQ (k μ0 μK μ : Nat) : Nat :=
  max (GenParamsQ.densDegQ k μ0 + μ + 4 * (k + 3) ^ 2 + 14) (GenParamsQ.expDegQ k μ0 μK + 6)

/-- **The single-piece step with polynomial envelopes.** -/
theorem polyEnvBound_stepQ (P : GenParamsQ) {μV μK μ : Nat} (H : P.CHyp μV μK) (hk : 1 ≤ P.k)
    (hcov : ∀ l, 1 ≤ l → l ≤ P.k → PolyCoverAt l (uCount P.V (uDegQ l)) (uExp P.V (uDegQ l)))
    (hrec : Section16RecurrenceProfileWith P.k (familyRecThr P.k P.K P.p) (familyRecExp P.k P.p))
    (hlow : PolyEnvBound (P.k + 1) μ) : PolyEnvBound (P.k + 2) (envStepQ P.k P.μ0 μK μ) := by
  intro alpha ha ha2
  have hX := two_div_ge_two ha ha2
  -- the input parameter, the lower-degree bound, the step and `Eloc`
  obtain ⟨he0, he8, hei, hy0, hyle, hyi⟩ := P.yIn_boundsQ ha ha2 H.hV H.hVμ H.hμ0
  have hy2 : P.yIn alpha ≤ 1 / 2 := hyle.trans ha2
  obtain ⟨β, σ, T, hB, b0, b1, s0, s16, bi, si⟩ := hlow _ hy0 hy2
  have hstep := P.inverse_step H.hV H.hK H.hp hk hcov hrec ha ha2 hB b0 s0 s16
  obtain ⟨hEl0, hEli⟩ := P.Eloc_inv_leQ H ha ha2
  obtain ⟨-, hEl2, -⟩ := P.Eloc_pos_le H.hV H.hp ha ha2
  set k := P.k with hkdef
  set E := GenParamsQ.expDegQ k P.μ0 μK with hEdef
  set dd := GenParamsQ.densDegQ k P.μ0 with hdddef
  set M1 := dd + 1 + μ with hM1def
  obtain ⟨-, hYμ⟩ := input_scale_le (μ := μ) ha ha2 hy0 hyi
  have bi' : β⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) := bi.trans hYμ
  have si' : σ⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) := si.trans hYμ
  have hei' : (P.eta alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) :=
    pw_mono hX hei (by rw [hM1def, hdddef]; unfold GenParamsQ.densDegQ; omega)
  have heta1 : P.eta alpha ≤ 1 := by linarith
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
  have hσ' : (inverseStepExponent (k + 1) (P.Eloc alpha) σ)⁻¹ ≤ (2 / alpha) ^ (2 ^ S) := by
    rw [σeq]
    have hx0 : 0 ≤ 32 * (polynomialPartitionConstant (k + 1 + 1) : Real) * (P.Eloc alpha)⁻¹ :=
      mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (inv_pos.mpr hEl0).le
    have h1 := pw_mul' hX (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (inv_pos.mpr hEl0).le
      h32P hEli
    exact pw_mul' hX hx0 (inv_pos.mpr s0).le h1 si'
  -- assemble
  refine ⟨P.eta alpha * β / 4, _, _, hstep, div_pos (mul_pos he0 b0) (by norm_num), ?_, σ0', σ16',
    ?_, pw_mono hX hσ' ?_⟩
  · have : P.eta alpha * β ≤ 1 := mul_le_one₀ heta1 b0.le b1
    linarith
  · rw [show (P.eta alpha * β / 4)⁻¹ = 4 * ((P.eta alpha)⁻¹ * β⁻¹) by field_simp]
    have h1 := pw_mul hX (inv_pos.mpr he0).le (inv_pos.mpr b0).le hei' bi'
    have h4 : (4 : Real) ≤ (2 / alpha) ^ (2 ^ (M1 + 1)) :=
      (four_le_pw_one hX).trans (pw_mono hX le_rfl (by omega))
    refine (pw_mul hX (by norm_num) (mul_nonneg (inv_pos.mpr he0).le (inv_pos.mpr b0).le) h4 h1).trans
      (pw_mono hX le_rfl ?_)
    unfold envStepQ; rw [← hdddef]; omega
  · unfold envStepQ; rw [← hdddef, ← hEdef]; omega


/-- The envelope after one step, with the threshold, without the cubic branch. -/
def envStepQTx (k μ0 μK μ : Nat) : Nat :=
  max (GenParamsQ.densDegQ k μ0 + μ + 4 * (k + 3) ^ 2 + 14)
    (max (GenParamsQ.threshDegQ k μ0 μK + 3) (k + 20))

/-- **The single-piece step, with envelopes and the sharper phase-refinement
threshold.** -/
theorem envBound_stepQx (P : GenParamsQ) {μV μK μ : Nat} (H : P.CHyp μV μK) (hk : 1 ≤ P.k)
    (hcov : ∀ l, 1 ≤ l → l ≤ P.k → PolyCoverAt l (uCount P.V (uDegQ l)) (uExp P.V (uDegQ l)))
    (hrec : Section16RecurrenceProfileWith P.k (familyRecThr P.k P.K P.p) (familyRecExp P.k P.p))
    (hlow : EnvBound (P.k + 1) μ) : EnvBound (P.k + 2) (envStepQTx P.k P.μ0 μK μ) := by
  intro alpha ha ha2
  have hX := two_div_ge_two ha ha2
  -- everything that mentions `P.k`, before naming it
  obtain ⟨he0, he8, hei, hy0, hyle, hyi⟩ := P.yIn_boundsQ ha ha2 H.hV H.hVμ H.hμ0
  have hy2 : P.yIn alpha ≤ 1 / 2 := hyle.trans ha2
  obtain ⟨β, σ, T, hB, b0, b1, s0, s16, bi, si, Ti⟩ := hlow _ hy0 hy2
  have hstep := P.inverse_step H.hV H.hK H.hp hk hcov hrec ha ha2 hB b0 s0 s16
  obtain ⟨hEl0, hEli⟩ := P.Eloc_inv_leQ H ha ha2
  obtain ⟨-, hEl2, -⟩ := P.Eloc_pos_le H.hV H.hp ha ha2
  have hTl := P.Tloc_le_expQ H hk ha ha2
  set k := P.k with hkdef
  set E := GenParamsQ.expDegQ k P.μ0 μK with hEdef
  set Th := GenParamsQ.threshDegQ k P.μ0 μK with hThdef
  set dd := GenParamsQ.densDegQ k P.μ0 with hdddef
  set M1 := dd + 1 + μ with hM1def
  have hETh : E + 4 ≤ Th := by rw [hThdef]; unfold GenParamsQ.threshDegQ; exact le_max_left _ _
  have hk3 : k + 2 ≤ (k + 2) ^ 3 := Nat.le_self_pow (by norm_num) _
  obtain ⟨-, hYμ⟩ := input_scale_le (μ := μ) ha ha2 hy0 hyi
  have bi' : β⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) := bi.trans hYμ
  have si' : σ⁻¹ ≤ Real.exp ((2 / alpha) ^ (2 ^ M1)) := si.trans (Real.exp_le_exp.mpr hYμ)
  have Ti' : T ≤ Real.exp (Real.exp ((2 / alpha) ^ (2 ^ M1))) :=
    Ti.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hYμ))
  have hei' : (P.eta alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) :=
    pw_mono hX hei (by rw [hM1def, hdddef]; unfold GenParamsQ.densDegQ; omega)
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
    unfold envStepQTx; rw [← hdddef]; omega
  · unfold envStepQTx; rw [← hdddef, ← hThdef]; omega
  · refine max_le (dex_mono hX hshort ?_) (dex_mono hX hinv ?_)
    · unfold envStepQTx; rw [← hdddef, ← hThdef]; omega
    · unfold envStepQTx; rw [← hdddef, ← hThdef]; omega



/-- The standing hypotheses at the tight base budget. -/
theorem tightHyp_of_profiles_fejerQ (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5)))) {k : Nat}
    (hk : 2 ≤ k) :
    (⟨classV Kc pc k, k, Kc k, pc k, tightMu0Q k⟩ : GenParamsQ).CHyp (tightMuV k) (genMuK k) := by
  obtain ⟨hV, -, -, -, -, -, hKk, hKμ, hpk, hpμ⟩ := stdHyp_of_profiles Kc pc hK hp hconst hk
  refine ⟨hV, classV_le_tight Kc pc hconst k, le_rfl, ?_, hKk, hKμ, hpk, hpμ⟩
  show k ≤ 2 ^ tightMu0Q k
  calc k ≤ 2 ^ k := Nat.lt_two_pow_self.le
    _ ≤ 2 ^ tightMu0Q k := Nat.pow_le_pow_right (by norm_num) (by
        unfold tightMu0Q; have := five_k_le_fixDegQ k
        have := le_max_right (tightMuV k) (fixDegQ k); omega)


/-- The Theorem 18.1 envelope at the tight base budget. -/
def polyGenMuQ : Nat → Nat
  | 0 => 74
  | 1 => 74
  | k + 2 => envStepQ (k + 2) (tightMu0Q (k + 2)) (genMuK (k + 2)) (polyGenMuQ (k + 1))

theorem polyGenMuQ_succ {k : Nat} (hk : 1 ≤ k) :
    polyGenMuQ (k + 1) = envStepQ (k + 1) (tightMu0Q (k + 1)) (genMuK (k + 1)) (polyGenMuQ k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rfl


theorem polyEnvBound_allQ (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {Kφ : Real} {pφ : Nat} (hpp : ProgressionPhasePartition Kφ pφ) (hpφ : 0 < pφ)
    (hKφ : Kφ ≤ 2 ^ pφ) (hpφB : (pφ : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64)) :
    ∀ k, 2 ≤ k → PolyEnvBound (k + 2) (polyGenMuQ k) := by
  have hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))) :=
    fun k hk => abstractFamilyLemma166At_of k (hK k) (hp k) (hrec k hk)
  have hK1 : ∀ k, 1 ≤ Kc k := fun k => le_trans (by norm_num) (hK k)
  have hstep : ∀ k, 2 ≤ k → ∀ μ, PolyEnvBound (k + 1) μ →
      PolyEnvBound (k + 2) (envStepQ k (tightMu0Q k) (genMuK k) μ) := by
    intro k hk μ hlow
    let P : GenParamsQ := ⟨classV Kc pc k, k, Kc k, pc k, tightMu0Q k⟩
    have H : P.CHyp (tightMuV k) (genMuK k) := tightHyp_of_profiles_fejerQ Kc pc hK hp hconst hk
    have hcov : ∀ l, 1 ≤ l → l ≤ P.k →
        PolyCoverAt l (uCount P.V (uDegQ l)) (uExp P.V (uDegQ l)) := by
      intro l hl1 hlk
      have hcl := polyCoverAt_classQ Kc pc hK1 hp hlem hl1
      exact hcl.uniform_mono (one_le_classV Kc pc l) (classV_mono Kc pc hlk) le_rfl
    exact polyEnvBound_stepQ P H (by show 1 ≤ k; omega) hcov (hrec k (by omega)) hlow
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    exact hstep 2 le_rfl 74 (polyEnvBound_three_of_phase_partition hpp hpφ hKφ hpφB)
  | succ k hk ih =>
    rw [polyGenMuQ_succ (by omega)]
    exact hstep (k + 1) (by omega) (polyGenMuQ k) ih


/-- The Theorem 18.2 envelope at the tight base budget, without the cubic branch. -/
def genMuXQ : Nat → Nat
  | 0 => 62
  | 1 => 62
  | k + 2 => envStepQTx (k + 2) (tightMu0Q (k + 2)) (genMuK (k + 2)) (genMuXQ (k + 1))

theorem genMuXQ_succ {k : Nat} (hk : 1 ≤ k) :
    genMuXQ (k + 1) = envStepQTx (k + 1) (tightMu0Q (k + 1)) (genMuK (k + 1)) (genMuXQ k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rfl

theorem envBound_allXQ (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5)))) :
    ∀ k, 2 ≤ k → EnvBound (k + 2) (genMuXQ k) := by
  have hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))) :=
    fun k hk => abstractFamilyLemma166At_of k (hK k) (hp k) (hrec k hk)
  have hK1 : ∀ k, 1 ≤ Kc k := fun k => le_trans (by norm_num) (hK k)
  have hstep : ∀ k, 2 ≤ k → ∀ μ, EnvBound (k + 1) μ →
      EnvBound (k + 2) (envStepQTx k (tightMu0Q k) (genMuK k) μ) := by
    intro k hk μ hlow
    let P : GenParamsQ := ⟨classV Kc pc k, k, Kc k, pc k, tightMu0Q k⟩
    have H : P.CHyp (tightMuV k) (genMuK k) := tightHyp_of_profiles_fejerQ Kc pc hK hp hconst hk
    have hcov : ∀ l, 1 ≤ l → l ≤ P.k →
        PolyCoverAt l (uCount P.V (uDegQ l)) (uExp P.V (uDegQ l)) := by
      intro l hl1 hlk
      have hcl := polyCoverAt_classQ Kc pc hK1 hp hlem hl1
      exact hcl.uniform_mono (one_le_classV Kc pc l) (classV_mono Kc pc hlk) le_rfl
    exact envBound_stepQx P H (by show 1 ≤ k; omega) hcov (hrec k (by omega)) hlow
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact hstep 2 le_rfl 62 envBound_three
  | succ k hk ih =>
    rw [genMuXQ_succ (by omega)]
    exact hstep (k + 1) (by omega) (genMuXQ k) ih




/-! ### Closed forms -/

/-- One step at `(qDeg, tightMu0Q)` costs `58·2^k` plus a polynomial. -/
theorem envStepQ_le_tight {k : Nat} (hk : 1 ≤ k) (μ : Nat) :
    envStepQ k (tightMu0Q k) (genMuK k) μ ≤
      μ + 58 * 2 ^ k + 9 * (k + 4) ^ 2 + 4 * (k + 3) ^ 2 + k + 45 := by
  unfold envStepQ GenParamsQ.densDegQ GenParamsQ.expDegQ GenParamsQ.rhoDegQ tightMu0Q tightMuV
    genMuK qDeg
  rw [fixDegQ_eq hk, two_pow_five_mul, two_pow_four_mul]
  have := Nat.lt_two_pow_self (n := k)
  generalize 4 * (k + 3) ^ 2 = q
  generalize (k + 4) ^ 2 = s
  generalize 2 ^ k = x at *
  omega

theorem envStepQTx_le_tight {k : Nat} (hk : 1 ≤ k) (μ : Nat) :
    envStepQTx k (tightMu0Q k) (genMuK k) μ ≤
      max (μ + 58 * 2 ^ k + 9 * (k + 4) ^ 2 + 4 * (k + 3) ^ 2 + k + 45) (64 * 2 ^ k + 8) := by
  unfold envStepQTx GenParamsQ.densDegQ GenParamsQ.threshDegQ GenParamsQ.expDegQ
    GenParamsQ.rhoDegQ tightMu0Q tightMuV genMuK qDeg
  rw [fixDegQ_eq hk, two_pow_six_mul, two_pow_five_mul, two_pow_four_mul]
  have := Nat.lt_two_pow_self (n := k)
  generalize 4 * (k + 3) ^ 2 = q
  generalize (k + 4) ^ 2 = s
  generalize 2 ^ k = x at *
  omega

theorem envStepQTx_ge_tight {k : Nat} (hk : 1 ≤ k) (μ : Nat) :
    μ + 58 * 2 ^ k ≤ envStepQTx k (tightMu0Q k) (genMuK k) μ := by
  unfold envStepQTx GenParamsQ.densDegQ GenParamsQ.rhoDegQ tightMu0Q tightMuV qDeg
  rw [fixDegQ_eq hk, two_pow_four_mul]
  have := Nat.lt_two_pow_self (n := k)
  generalize 4 * (k + 3) ^ 2 = q
  generalize (k + 4) ^ 2 = s
  generalize 2 ^ k = x at *
  omega

/-- `4(k+5)² ≤ 2^k` for `k ≥ 10`. -/
theorem four_sq_le_two_pow_ten : ∀ k, 10 ≤ k → 4 * (k + 5) ^ 2 ≤ 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hstep : (k + 1 + 5) ^ 2 ≤ 2 * (k + 5) ^ 2 := by nlinarith
    calc 4 * (k + 1 + 5) ^ 2 ≤ 2 * (4 * (k + 5) ^ 2) := by omega
      _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left _ ih
      _ = 2 ^ (k + 1) := by rw [pow_succ]; ring

theorem polyGenMuQ_ten : polyGenMuQ 10 + 4 * 10 + 128 ≤ 128 * 2 ^ 10 := by decide

/-- **The Theorem 18.1 envelope at `(qDeg, tightMu0Q)`**: `μ_k + 4k + 128 ≤ 128·2^k`
for `k ≥ 10`. -/
theorem polyGenMuQ_le : ∀ k, 10 ≤ k → polyGenMuQ k + 4 * k + 128 ≤ 128 * 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact polyGenMuQ_ten
  | succ k hk ih =>
    rw [polyGenMuQ_succ (by omega)]
    have h1 := envStepQ_le_tight (k := k + 1) (by omega) (polyGenMuQ k)
    have h2 := four_sq_le_two_pow_ten k hk
    have h3 : (k + 4) ^ 2 ≤ (k + 5) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h4 : k + 50 ≤ 2 ^ k := le_trans (by nlinarith) h2
    rw [show k + 1 + 4 = k + 5 by ring, show k + 1 + 3 = k + 4 by ring] at h1
    rw [pow_succ] at h1 ⊢
    generalize (k + 5) ^ 2 = s5 at *
    generalize (k + 4) ^ 2 = s4 at *
    generalize 2 ^ k = x at *
    omega

theorem genMuXQ_ten : genMuXQ 10 + 4 * 10 + 128 ≤ 128 * 2 ^ 10 := by decide

theorem genMuXQ_le : ∀ k, 10 ≤ k → genMuXQ k + 4 * k + 128 ≤ 128 * 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact genMuXQ_ten
  | succ k hk ih =>
    rw [genMuXQ_succ (by omega)]
    have h1 := envStepQTx_le_tight (k := k + 1) (by omega) (genMuXQ k)
    have h2 := four_sq_le_two_pow_ten k hk
    have h3 : (k + 4) ^ 2 ≤ (k + 5) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h4 : k + 50 ≤ 2 ^ k := le_trans (by nlinarith) h2
    rw [show k + 1 + 4 = k + 5 by ring, show k + 1 + 3 = k + 4 by ring] at h1
    rw [pow_succ] at h1 ⊢
    generalize (k + 5) ^ 2 = s5 at *
    generalize (k + 4) ^ 2 = s4 at *
    generalize 2 ^ k = x at *
    omega

theorem genMuXQ_ge : ∀ k, 2 ≤ k → 58 * 2 ^ k ≤ genMuXQ k := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [genMuXQ_succ (by omega)]
  have := envStepQTx_ge_tight (k := j + 1) (by omega) (genMuXQ j)
  omega

/-! ### The headline statements -/

/-- **Theorem 18.1 at every degree `d ≥ 12` with exponent `α^(2^(2^(d+5)))`**,
from the recurrence profiles and a phase partition. -/
theorem theorem_18_1_d5_of_profiles_cover (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {Kφ : Real} {pφ : Nat} (hpp : ProgressionPhasePartition Kφ pφ) (hpφ : 0 < pφ)
    (hKφ : Kφ ≤ 2 ^ pφ) (hpφB : (pφ : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64))
    {d : Nat} (hd : 12 ≤ d) : Theorem181AtSharp 5 d := by
  have henv := polyEnvBound_allQ Kc pc hK hp hrec hconst hpp hpφ hKφ hpφB (d - 2) (by omega)
  rw [show d - 2 + 2 = d by omega] at henv
  refine theorem181AtSharp_of_polyEnvBound henv ?_
  have hle := polyGenMuQ_le (d - 2) (by omega)
  have h2 : 2 ^ (d + 5) = 128 * 2 ^ (d - 2) := by
    rw [show d + 5 = (d - 2) + 7 by omega, pow_add]; ring
  rw [h2]
  omega

/-- **Theorem 18.2 at every length `L ≥ 14` with `L + 3` in the threshold**,
from the recurrence profiles. -/
theorem theorem_18_2_L3_of_profiles_cover (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {L : Nat} (hL : 14 ≤ L) : Theorem182AtSharp 3 L := by
  have henv := envBound_allXQ Kc pc hK hp hrec hconst (L - 4) (by omega)
  rw [show L - 4 + 2 = L - 2 by omega] at henv
  have hge := genMuXQ_ge (L - 4) (by omega)
  have hle := genMuXQ_le (L - 4) (by omega)
  have hk := Nat.lt_two_pow_self (n := L - 4)
  have h4 : 4 ≤ 2 ^ (L - 4) :=
    le_trans (by norm_num : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h42 : 42 ≤ genMuXQ (L - 4) := by omega
  have hLμ : 4 * L + 20 ≤ 2 ^ genMuXQ (L - 4) := by
    have := Nat.lt_two_pow_self (n := genMuXQ (L - 4))
    omega
  refine theorem182AtSharp_of_envBound (by omega) henv h42 hLμ ?_
  have h2 : 2 ^ (L + 3) = 128 * 2 ^ (L - 4) := by
    rw [show L + 3 = (L - 4) + 7 by omega, pow_add]; ring
  rw [h2]
  omega

/-- **Corollary 18.7 at every length `L ≥ 14` with `L + 3`**, from the profiles. -/
theorem corollary_18_7_L3_of_profiles_cover (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {L : Nat} (hL : 14 ≤ L) : Corollary187AtSharp 3 L :=
  (theorem_18_2_L3_of_profiles_cover Kc pc hK hp hrec hconst hL).corollary_18_7

end LeanProofs.GowersSzemeredi
