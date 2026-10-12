import GowersSzemeredi.Proofs18CoverExponentsFejerW
import GowersSzemeredi.Proofs18CoverFejerHeadlineT

/-! **Theorem 18.1 at `d + 3` for every `d ≥ 11` and at `d + 4` for every
`d ≥ 8`; Theorem 18.2 / Corollary 18.7 at `L + 1` for every `L ≥ 13` and at
`L + 2` for every `L ≥ 10`, from the recurrence profiles with polynomial
family constants** (Notes L.16m).

The Section 18 envelope at `GenParamsW`. Its base budget is
`tightMu0W k = max(4k + 13, 5k + 21) + 2 = 5k + 23` instead of `16·2^k + 9`
(`Proofs18FejerEnvelopeBaseW`). That needs the family constants at
`Kc k + pc k ≤ 2^(2^(4k+16))`, the hypothesis `hconst` here, which the
explicit constants satisfy. The class covers sit at the exact table `uDegT`,
and the requirement on `m` uses the polynomial Bohr radius. The step lemmas
and recursions are generated from `Proofs18CoverFejerHeadlineT`.

Beyond the table one step costs `12·2^k + O(k²)` (`envStepW_le_tight`). The
Theorem 18.2 threshold branch is `16·2^k + 5k + 28`. Both envelopes tend to
`24·2^k < 32·2^k`. `decide +kernel` certifies them in dimensions `2, …, 12`,
and the invariants `μ_k + 4k + 128 ≤ 32·2^k` (`polyGenMuW_le32`,
`genMuXW_le32`) carry them from `k = 12` on. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The polynomial base budget. -/
def tightMu0W (k : Nat) : Nat := max (tightMuW k) (pDeg k) + 2

/-- The envelope after one step (no threshold). -/
def envStepW (k μ0 μK μ : Nat) : Nat :=
  max (GenParamsW.densDegW k μ0 + μ + 4 * (k + 3) ^ 2 + 14) (GenParamsW.expDegW k μ0 μK + 6)

/-- **The single-piece step with polynomial envelopes.** -/
theorem polyEnvBound_stepW (P : GenParamsW) {μV μK μ : Nat} (H : P.CHyp μV μK) (hk : 1 ≤ P.k)
    (hcov : ∀ l, 1 ≤ l → l ≤ P.k → PolyCoverAt l (uCount P.V (uDegT l)) (uExp P.V (uDegT l)))
    (hrec : Section16RecurrenceProfileWith P.k (familyRecThr P.k P.K P.p) (familyRecExp P.k P.p))
    (hlow : PolyEnvBound (P.k + 1) μ) : PolyEnvBound (P.k + 2) (envStepW P.k P.μ0 μK μ) := by
  intro alpha ha ha2
  have hX := two_div_ge_two ha ha2
  -- the input parameter, the lower-degree bound, the step and `Eloc`
  obtain ⟨he0, he8, hei, hy0, hyle, hyi⟩ := P.yIn_boundsW ha ha2 H.hV H.hVμ H.hμ0
  have hy2 : P.yIn alpha ≤ 1 / 2 := hyle.trans ha2
  obtain ⟨β, σ, T, hB, b0, b1, s0, s16, bi, si⟩ := hlow _ hy0 hy2
  have hstep := P.inverse_step H.hV H.hK H.hp hk hcov hrec ha ha2 hB b0 s0 s16
  obtain ⟨hEl0, hEli⟩ := P.Eloc_inv_leW H ha ha2
  obtain ⟨-, hEl2, -⟩ := P.Eloc_pos_le H.hV H.hp ha ha2
  set k := P.k with hkdef
  set E := GenParamsW.expDegW k P.μ0 μK with hEdef
  set dd := GenParamsW.densDegW k P.μ0 with hdddef
  set M1 := dd + 1 + μ with hM1def
  obtain ⟨-, hYμ⟩ := input_scale_le (μ := μ) ha ha2 hy0 hyi
  have bi' : β⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) := bi.trans hYμ
  have si' : σ⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) := si.trans hYμ
  have hei' : (P.eta alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) :=
    pw_mono hX hei (by rw [hM1def, hdddef]; unfold GenParamsW.densDegW; omega)
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
    unfold envStepW; rw [← hdddef]; omega
  · unfold envStepW; rw [← hdddef, ← hEdef]; omega


/-- The envelope after one step, with the threshold, without the cubic branch. -/
def envStepWTx (k μ0 μK μ : Nat) : Nat :=
  max (GenParamsW.densDegW k μ0 + μ + 4 * (k + 3) ^ 2 + 14)
    (max (GenParamsW.threshDegW k μ0 μK + 3) (k + 20))

/-- **The single-piece step, with envelopes and the sharper phase-refinement
threshold.** -/
theorem envBound_stepWx (P : GenParamsW) {μV μK μ : Nat} (H : P.CHyp μV μK) (hk : 1 ≤ P.k)
    (hcov : ∀ l, 1 ≤ l → l ≤ P.k → PolyCoverAt l (uCount P.V (uDegT l)) (uExp P.V (uDegT l)))
    (hrec : Section16RecurrenceProfileWith P.k (familyRecThr P.k P.K P.p) (familyRecExp P.k P.p))
    (hlow : EnvBound (P.k + 1) μ) : EnvBound (P.k + 2) (envStepWTx P.k P.μ0 μK μ) := by
  intro alpha ha ha2
  have hX := two_div_ge_two ha ha2
  -- everything that mentions `P.k`, before naming it
  obtain ⟨he0, he8, hei, hy0, hyle, hyi⟩ := P.yIn_boundsW ha ha2 H.hV H.hVμ H.hμ0
  have hy2 : P.yIn alpha ≤ 1 / 2 := hyle.trans ha2
  obtain ⟨β, σ, T, hB, b0, b1, s0, s16, bi, si, Ti⟩ := hlow _ hy0 hy2
  have hstep := P.inverse_step H.hV H.hK H.hp hk hcov hrec ha ha2 hB b0 s0 s16
  obtain ⟨hEl0, hEli⟩ := P.Eloc_inv_leW H ha ha2
  obtain ⟨-, hEl2, -⟩ := P.Eloc_pos_le H.hV H.hp ha ha2
  have hTl := P.Tloc_le_expW H hk ha ha2
  set k := P.k with hkdef
  set E := GenParamsW.expDegW k P.μ0 μK with hEdef
  set Th := GenParamsW.threshDegW k P.μ0 μK with hThdef
  set dd := GenParamsW.densDegW k P.μ0 with hdddef
  set M1 := dd + 1 + μ with hM1def
  have hETh : E + 4 ≤ Th := by rw [hThdef]; unfold GenParamsW.threshDegW; exact le_max_left _ _
  have hk3 : k + 2 ≤ (k + 2) ^ 3 := Nat.le_self_pow (by norm_num) _
  obtain ⟨-, hYμ⟩ := input_scale_le (μ := μ) ha ha2 hy0 hyi
  have bi' : β⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) := bi.trans hYμ
  have si' : σ⁻¹ ≤ Real.exp ((2 / alpha) ^ (2 ^ M1)) := si.trans (Real.exp_le_exp.mpr hYμ)
  have Ti' : T ≤ Real.exp (Real.exp ((2 / alpha) ^ (2 ^ M1))) :=
    Ti.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hYμ))
  have hei' : (P.eta alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) :=
    pw_mono hX hei (by rw [hM1def, hdddef]; unfold GenParamsW.densDegW; omega)
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
    unfold envStepWTx; rw [← hdddef]; omega
  · unfold envStepWTx; rw [← hdddef, ← hThdef]; omega
  · refine max_le (dex_mono hX hshort ?_) (dex_mono hX hinv ?_)
    · unfold envStepWTx; rw [← hdddef, ← hThdef]; omega
    · unfold envStepWTx; rw [← hdddef, ← hThdef]; omega



/-- The polynomial bound on the family constants: `K, p ≤ 2^(2^(4k+16))`. -/
def genMuKW (k : Nat) : Nat := 4 * k + 16

/-- The standing hypotheses at the polynomial base budget. -/
theorem tightHyp_of_profiles_fejerW (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ (4 * k + 16))) {k : Nat}
    (hk : 2 ≤ k) :
    (⟨classV Kc pc k, k, Kc k, pc k, tightMu0W k⟩ : GenParamsW).CHyp (tightMuW k) (genMuKW k) := by
  have hKr : (Kc k : Real) ≤ 2 ^ ((2 : Nat) ^ genMuKW k) := by
    have := hconst k; unfold genMuKW; linarith [Nat.cast_nonneg (α := Real) (pc k)]
  have hpr : (pc k : Real) ≤ 2 ^ ((2 : Nat) ^ genMuKW k) := by
    have := hconst k; unfold genMuKW; linarith [Nat.cast_nonneg (α := Real) (Kc k)]
  refine ⟨one_le_classV Kc pc k, classV_le_poly Kc pc hconst k, le_rfl, ?_, hK k, ?_, hp k, ?_⟩
  · show k ≤ 2 ^ tightMu0W k
    calc k ≤ 2 ^ k := Nat.lt_two_pow_self.le
      _ ≤ 2 ^ tightMu0W k := Nat.pow_le_pow_right (by norm_num) (by
          unfold tightMu0W; have := five_k_le_pDeg k
          have := le_max_right (tightMuW k) (pDeg k); omega)
  · have : ((Kc k : Nat) : Real) ≤ ((2 ^ 2 ^ genMuKW k : Nat) : Real) := by push_cast; exact hKr
    exact_mod_cast this
  · have : ((pc k : Nat) : Real) ≤ ((2 ^ 2 ^ genMuKW k : Nat) : Real) := by push_cast; exact hpr
    exact_mod_cast this


/-- The Theorem 18.1 envelope at the tight base budget. -/
def polyGenMuW : Nat → Nat
  | 0 => 74
  | 1 => 74
  | k + 2 => envStepW (k + 2) (tightMu0W (k + 2)) (genMuKW (k + 2)) (polyGenMuW (k + 1))

theorem polyGenMuW_succ {k : Nat} (hk : 1 ≤ k) :
    polyGenMuW (k + 1) = envStepW (k + 1) (tightMu0W (k + 1)) (genMuKW (k + 1)) (polyGenMuW k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rfl


theorem polyEnvBound_allW (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ (4 * k + 16)))
    {Kφ : Real} {pφ : Nat} (hpp : ProgressionPhasePartition Kφ pφ) (hpφ : 0 < pφ)
    (hKφ : Kφ ≤ 2 ^ pφ) (hpφB : (pφ : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64)) :
    ∀ k, 2 ≤ k → PolyEnvBound (k + 2) (polyGenMuW k) := by
  have hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))) :=
    fun k hk => abstractFamilyLemma166At_of k (hK k) (hp k) (hrec k hk)
  have hK1 : ∀ k, 1 ≤ Kc k := fun k => le_trans (by norm_num) (hK k)
  have hstep : ∀ k, 2 ≤ k → ∀ μ, PolyEnvBound (k + 1) μ →
      PolyEnvBound (k + 2) (envStepW k (tightMu0W k) (genMuKW k) μ) := by
    intro k hk μ hlow
    let P : GenParamsW := ⟨classV Kc pc k, k, Kc k, pc k, tightMu0W k⟩
    have H : P.CHyp (tightMuW k) (genMuKW k) := tightHyp_of_profiles_fejerW Kc pc hK hp hconst hk
    have hcov : ∀ l, 1 ≤ l → l ≤ P.k →
        PolyCoverAt l (uCount P.V (uDegT l)) (uExp P.V (uDegT l)) := by
      intro l hl1 hlk
      have hcl := polyCoverAt_classT Kc pc hK1 hp hlem hl1
      exact hcl.uniform_mono (one_le_classV Kc pc l) (classV_mono Kc pc hlk) le_rfl
    exact polyEnvBound_stepW P H (by show 1 ≤ k; omega) hcov (hrec k (by omega)) hlow
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    exact hstep 2 le_rfl 74 (polyEnvBound_three_of_phase_partition hpp hpφ hKφ hpφB)
  | succ k hk ih =>
    rw [polyGenMuW_succ (by omega)]
    exact hstep (k + 1) (by omega) (polyGenMuW k) ih


/-- The Theorem 18.2 envelope at the tight base budget, without the cubic branch. -/
def genMuXW : Nat → Nat
  | 0 => 62
  | 1 => 62
  | k + 2 => envStepWTx (k + 2) (tightMu0W (k + 2)) (genMuKW (k + 2)) (genMuXW (k + 1))

theorem genMuXW_succ {k : Nat} (hk : 1 ≤ k) :
    genMuXW (k + 1) = envStepWTx (k + 1) (tightMu0W (k + 1)) (genMuKW (k + 1)) (genMuXW k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rfl

theorem envBound_allXW (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ (4 * k + 16))) :
    ∀ k, 2 ≤ k → EnvBound (k + 2) (genMuXW k) := by
  have hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))) :=
    fun k hk => abstractFamilyLemma166At_of k (hK k) (hp k) (hrec k hk)
  have hK1 : ∀ k, 1 ≤ Kc k := fun k => le_trans (by norm_num) (hK k)
  have hstep : ∀ k, 2 ≤ k → ∀ μ, EnvBound (k + 1) μ →
      EnvBound (k + 2) (envStepWTx k (tightMu0W k) (genMuKW k) μ) := by
    intro k hk μ hlow
    let P : GenParamsW := ⟨classV Kc pc k, k, Kc k, pc k, tightMu0W k⟩
    have H : P.CHyp (tightMuW k) (genMuKW k) := tightHyp_of_profiles_fejerW Kc pc hK hp hconst hk
    have hcov : ∀ l, 1 ≤ l → l ≤ P.k →
        PolyCoverAt l (uCount P.V (uDegT l)) (uExp P.V (uDegT l)) := by
      intro l hl1 hlk
      have hcl := polyCoverAt_classT Kc pc hK1 hp hlem hl1
      exact hcl.uniform_mono (one_le_classV Kc pc l) (classV_mono Kc pc hlk) le_rfl
    exact envBound_stepWx P H (by show 1 ≤ k; omega) hcov (hrec k (by omega)) hlow
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact hstep 2 le_rfl 62 envBound_three
  | succ k hk ih =>
    rw [genMuXW_succ (by omega)]
    exact hstep (k + 1) (by omega) (genMuXW k) ih




/-! ### Closed forms -/

/-- Beyond the table one step costs `12·2^k` plus a polynomial. -/
theorem envStepW_le_tight {k : Nat} (hk : 13 ≤ k) (μ : Nat) :
    envStepW k (tightMu0W k) (genMuKW k) μ ≤
      μ + 12 * 2 ^ k + 9 * (k + 4) ^ 2 + 4 * (k + 3) ^ 2 + 6 * k + 149 := by
  unfold envStepW GenParamsW.densDegW GenParamsW.expDegW GenParamsW.rhoDegW tightMu0W tightMuW
    genMuKW pDeg
  rw [tDeg_eq_of_ge hk]
  have := Nat.lt_two_pow_self (n := k)
  generalize 4 * (k + 3) ^ 2 = q
  generalize (k + 4) ^ 2 = s
  generalize 2 ^ k = x at *
  omega

theorem envStepWTx_le_tight {k : Nat} (hk : 13 ≤ k) (μ : Nat) :
    envStepWTx k (tightMu0W k) (genMuKW k) μ ≤
      max (μ + 12 * 2 ^ k + 9 * (k + 4) ^ 2 + 4 * (k + 3) ^ 2 + 6 * k + 149)
        (16 * 2 ^ k + 5 * k + 28) := by
  unfold envStepWTx GenParamsW.densDegW GenParamsW.threshDegW GenParamsW.expDegW
    GenParamsW.rhoDegW tightMu0W tightMuW genMuKW pDeg
  rw [tDeg_eq_of_ge hk, two_pow_four_mul]
  have := Nat.lt_two_pow_self (n := k)
  generalize 4 * (k + 3) ^ 2 = q
  generalize (k + 4) ^ 2 = s
  generalize 2 ^ k = x at *
  omega

/-- The threshold branch: every Theorem 18.2 step is at least `16·2^k + 5k + 28`. -/
theorem envStepWTx_ge (k μ0 μK μ : Nat) : 16 * 2 ^ k + 5 * k + 28 ≤ envStepWTx k μ0 μK μ := by
  unfold envStepWTx GenParamsW.threshDegW
  rw [two_pow_four_mul]
  omega

/-! The envelopes in dimensions `2, …, 12`, kernel-evaluated. -/

theorem polyGenMuW_small128 {k : Nat} (h2 : 2 ≤ k) (h12 : k ≤ 12) :
    polyGenMuW k + 1 ≤ 128 * 2 ^ k := by
  interval_cases k <;> decide +kernel

theorem polyGenMuW_small64 {k : Nat} (h6 : 6 ≤ k) (h12 : k ≤ 12) :
    polyGenMuW k + 1 ≤ 64 * 2 ^ k := by
  interval_cases k <;> decide +kernel

theorem polyGenMuW_small32 {k : Nat} (h9 : 9 ≤ k) (h12 : k ≤ 12) :
    polyGenMuW k + 1 ≤ 32 * 2 ^ k := by
  interval_cases k <;> decide +kernel

theorem genMuXW_small128 {k : Nat} (h2 : 2 ≤ k) (h12 : k ≤ 12) :
    genMuXW k + 2 * (k + 4) + 14 ≤ 128 * 2 ^ k := by
  interval_cases k <;> decide +kernel

theorem genMuXW_small64 {k : Nat} (h6 : 6 ≤ k) (h12 : k ≤ 12) :
    genMuXW k + 2 * (k + 4) + 14 ≤ 64 * 2 ^ k := by
  interval_cases k <;> decide +kernel

theorem genMuXW_small32 {k : Nat} (h9 : 9 ≤ k) (h12 : k ≤ 12) :
    genMuXW k + 2 * (k + 4) + 14 ≤ 32 * 2 ^ k := by
  interval_cases k <;> decide +kernel

theorem polyGenMuW_twelve : polyGenMuW 12 + 4 * 12 + 128 ≤ 32 * 2 ^ 12 := by decide +kernel

theorem genMuXW_twelve : genMuXW 12 + 4 * 12 + 128 ≤ 32 * 2 ^ 12 := by decide +kernel

/-- **The Theorem 18.1 envelope beyond the table**: `μ_k + 4k + 128 ≤ 32·2^k`
for `k ≥ 12`. -/
theorem polyGenMuW_le32 : ∀ k, 12 ≤ k → polyGenMuW k + 4 * k + 128 ≤ 32 * 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact polyGenMuW_twelve
  | succ k hk ih =>
    rw [polyGenMuW_succ (by omega)]
    have h1 := envStepW_le_tight (k := k + 1) (by omega) (polyGenMuW k)
    have h2 := four_sq_le_two_pow_ten k (by omega)
    have h3 : (k + 4) ^ 2 ≤ (k + 5) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h4 : 6 * k + 160 ≤ 2 ^ k := le_trans (by nlinarith) h2
    rw [show k + 1 + 4 = k + 5 by ring, show k + 1 + 3 = k + 4 by ring] at h1
    rw [pow_succ] at h1 ⊢
    generalize (k + 5) ^ 2 = s5 at *
    generalize (k + 4) ^ 2 = s4 at *
    generalize 2 ^ k = x at *
    omega

/-- **The Theorem 18.2 envelope beyond the table**: `μ_k + 4k + 128 ≤ 32·2^k`
for `k ≥ 12`. -/
theorem genMuXW_le32 : ∀ k, 12 ≤ k → genMuXW k + 4 * k + 128 ≤ 32 * 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact genMuXW_twelve
  | succ k hk ih =>
    rw [genMuXW_succ (by omega)]
    have h1 := envStepWTx_le_tight (k := k + 1) (by omega) (genMuXW k)
    have h2 := four_sq_le_two_pow_ten k (by omega)
    have h3 : (k + 4) ^ 2 ≤ (k + 5) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h4 : 6 * k + 160 ≤ 2 ^ k := le_trans (by nlinarith) h2
    rw [show k + 1 + 4 = k + 5 by ring, show k + 1 + 3 = k + 4 by ring] at h1
    rw [pow_succ] at h1 ⊢
    generalize (k + 5) ^ 2 = s5 at *
    generalize (k + 4) ^ 2 = s4 at *
    generalize 2 ^ k = x at *
    omega

theorem polyGenMuW_fit32 {k : Nat} (hk : 9 ≤ k) : polyGenMuW k + 1 ≤ 32 * 2 ^ k := by
  rcases Nat.lt_or_ge k 13 with h | h
  · exact polyGenMuW_small32 hk (by omega)
  · have := polyGenMuW_le32 k (by omega); omega

theorem polyGenMuW_fit64 {k : Nat} (hk : 6 ≤ k) : polyGenMuW k + 1 ≤ 64 * 2 ^ k := by
  rcases Nat.lt_or_ge k 13 with h | h
  · exact polyGenMuW_small64 hk (by omega)
  · have := polyGenMuW_le32 k (by omega); omega

theorem genMuXW_fit32 {k : Nat} (hk : 9 ≤ k) : genMuXW k + 2 * (k + 4) + 14 ≤ 32 * 2 ^ k := by
  rcases Nat.lt_or_ge k 13 with h | h
  · exact genMuXW_small32 hk (by omega)
  · have := genMuXW_le32 k (by omega); omega

theorem genMuXW_fit64 {k : Nat} (hk : 6 ≤ k) : genMuXW k + 2 * (k + 4) + 14 ≤ 64 * 2 ^ k := by
  rcases Nat.lt_or_ge k 13 with h | h
  · exact genMuXW_small64 hk (by omega)
  · have := genMuXW_le32 k (by omega); omega

theorem genMuXW_ge {k : Nat} (hk : 2 ≤ k) : 16 * 2 ^ k + 28 ≤ genMuXW k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [genMuXW_succ (by omega)]
  have := envStepWTx_ge (j + 1) (tightMu0W (j + 1)) (genMuKW (j + 1)) (genMuXW j)
  omega

/-! ### The headline statements -/

/-- **Theorem 18.1 at every degree `d ≥ 11` with exponent `α^(2^(2^(d+3)))`**,
from the recurrence profiles with polynomial family constants. -/
theorem theorem_18_1_d3_eleven_le_of_profiles_poly (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ (4 * k + 16)))
    {Kφ : Real} {pφ : Nat} (hpp : ProgressionPhasePartition Kφ pφ) (hpφ : 0 < pφ)
    (hKφ : Kφ ≤ 2 ^ pφ) (hpφB : (pφ : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64))
    {d : Nat} (hd : 11 ≤ d) : Theorem181AtSharp 3 d := by
  have henv := polyEnvBound_allW Kc pc hK hp hrec hconst hpp hpφ hKφ hpφB (d - 2) (by omega)
  rw [show d - 2 + 2 = d by omega] at henv
  refine theorem181AtSharp_of_polyEnvBound henv ?_
  have hle := polyGenMuW_fit32 (k := d - 2) (by omega)
  have h2 : 2 ^ (d + 3) = 32 * 2 ^ (d - 2) := by
    rw [show d + 3 = (d - 2) + 5 by omega, pow_add]; ring
  rw [h2]
  exact hle

/-- **Theorem 18.1 at every degree `d ≥ 8` with exponent `α^(2^(2^(d+4)))`**. -/
theorem theorem_18_1_d4_eight_le_of_profiles_poly (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ (4 * k + 16)))
    {Kφ : Real} {pφ : Nat} (hpp : ProgressionPhasePartition Kφ pφ) (hpφ : 0 < pφ)
    (hKφ : Kφ ≤ 2 ^ pφ) (hpφB : (pφ : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64))
    {d : Nat} (hd : 8 ≤ d) : Theorem181AtSharp 4 d := by
  have henv := polyEnvBound_allW Kc pc hK hp hrec hconst hpp hpφ hKφ hpφB (d - 2) (by omega)
  rw [show d - 2 + 2 = d by omega] at henv
  refine theorem181AtSharp_of_polyEnvBound henv ?_
  have hle := polyGenMuW_fit64 (k := d - 2) (by omega)
  have h2 : 2 ^ (d + 4) = 64 * 2 ^ (d - 2) := by
    rw [show d + 4 = (d - 2) + 6 by omega, pow_add]; ring
  rw [h2]
  exact hle

/-- **Theorem 18.2 at every length `L ≥ 13` with `L + 1` in the threshold**,
from the recurrence profiles with polynomial family constants. -/
theorem theorem_18_2_L1_thirteen_le_of_profiles_poly (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ (4 * k + 16)))
    {L : Nat} (hL : 13 ≤ L) : Theorem182AtSharp 1 L := by
  have henv := envBound_allXW Kc pc hK hp hrec hconst (L - 4) (by omega)
  rw [show L - 4 + 2 = L - 2 by omega] at henv
  have hge := genMuXW_ge (k := L - 4) (by omega)
  have hfit := genMuXW_fit32 (k := L - 4) (by omega)
  have hk := Nat.lt_two_pow_self (n := L - 4)
  have h42 : 42 ≤ genMuXW (L - 4) := by omega
  have hLμ : 4 * L + 20 ≤ 2 ^ genMuXW (L - 4) := by
    have := Nat.lt_two_pow_self (n := genMuXW (L - 4))
    omega
  refine theorem182AtSharp_of_envBound (by omega) henv h42 hLμ ?_
  have h2 : 2 ^ (L + 1) = 32 * 2 ^ (L - 4) := by
    rw [show L + 1 = (L - 4) + 5 by omega, pow_add]; ring
  rw [h2]
  omega

/-- **Theorem 18.2 at every length `L ≥ 10` with `L + 2` in the threshold**. -/
theorem theorem_18_2_L2_ten_le_of_profiles_poly (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ (4 * k + 16)))
    {L : Nat} (hL : 10 ≤ L) : Theorem182AtSharp 2 L := by
  have henv := envBound_allXW Kc pc hK hp hrec hconst (L - 4) (by omega)
  rw [show L - 4 + 2 = L - 2 by omega] at henv
  have hge := genMuXW_ge (k := L - 4) (by omega)
  have hfit := genMuXW_fit64 (k := L - 4) (by omega)
  have hk := Nat.lt_two_pow_self (n := L - 4)
  have h42 : 42 ≤ genMuXW (L - 4) := by omega
  have hLμ : 4 * L + 20 ≤ 2 ^ genMuXW (L - 4) := by
    have := Nat.lt_two_pow_self (n := genMuXW (L - 4))
    omega
  refine theorem182AtSharp_of_envBound (by omega) henv h42 hLμ ?_
  have h2 : 2 ^ (L + 2) = 64 * 2 ^ (L - 4) := by
    rw [show L + 2 = (L - 4) + 6 by omega, pow_add]; ring
  rw [h2]
  omega

theorem corollary_18_7_L1_thirteen_le_of_profiles_poly (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ (4 * k + 16)))
    {L : Nat} (hL : 13 ≤ L) : Corollary187AtSharp 1 L :=
  (theorem_18_2_L1_thirteen_le_of_profiles_poly Kc pc hK hp hrec hconst hL).corollary_18_7

theorem corollary_18_7_L2_ten_le_of_profiles_poly (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ (4 * k + 16)))
    {L : Nat} (hL : 10 ≤ L) : Corollary187AtSharp 2 L :=
  (theorem_18_2_L2_ten_le_of_profiles_poly Kc pc hK hp hrec hconst hL).corollary_18_7

end LeanProofs.GowersSzemeredi
