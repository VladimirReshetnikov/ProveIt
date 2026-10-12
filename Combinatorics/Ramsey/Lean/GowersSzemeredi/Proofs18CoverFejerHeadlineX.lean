import GowersSzemeredi.Proofs18CoverExponentsFejerX
import GowersSzemeredi.Proofs18CoverFejerHeadlineW

/-! **Theorem 18.1 at `d + 2` for every `d ≥ 17`, and Theorem 18.2 /
Corollary 18.7 with no offset (`L + 0`) for every `L ≥ 19`, from the
recurrence profiles with polynomial family constants** (Notes L.16n).

The Section 18 envelope at `GenParamsX`: the polynomial base budget of
`Proofs18CoverFejerHeadlineW`, with the class covers at `uDegX`. The class
table is exact up to dimension `12`, and beyond it is
`5·2^(l−1) + 3(l+4)² + 2` (`Proofs18TightClassesFejerX`). One step then costs
`15·2^(k−1) + O(k²) = 7.5·2^k + O(k²)` (`envStepX_le_tight`), and the
Theorem 18.1 envelope tends to `15·2^k < 16·2^k`. `decide +kernel` certifies
the base `k = 15`, and the invariant `μ_k + 4k + 128 ≤ 16·2^k`
(`polyGenMuX_le16`) carries it on. The step lemmas and recursions are
generated from `Proofs18CoverFejerHeadlineW`. The Theorem 18.2 threshold
branch is the polynomial `5k + 33` (Lemma 15.6 at `X^(2^(5k+21))`), so the
same invariant gives `genMuXX_le16` and Theorem 18.2 without offset. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The polynomial base budget. -/
def tightMu0X (k : Nat) : Nat := max (tightMuW k) (pDeg k) + 2

/-- The envelope after one step (no threshold). -/
def envStepX (k μ0 μK μ : Nat) : Nat :=
  max (GenParamsX.densDegX k μ0 + μ + 4 * (k + 3) ^ 2 + 14) (GenParamsX.expDegX k μ0 μK + 6)

/-- **The single-piece step with polynomial envelopes.** -/
theorem polyEnvBound_stepX (P : GenParamsX) {μV μK μ : Nat} (H : P.CHyp μV μK) (hk : 1 ≤ P.k)
    (hcov : ∀ l, 1 ≤ l → l ≤ P.k → PolyCoverAt l (uCount P.V (uDegX l)) (uExp P.V (uDegX l)))
    (hrec : Section16RecurrenceProfileWith P.k (familyRecThr P.k P.K P.p) (familyRecExp P.k P.p))
    (hlow : PolyEnvBound (P.k + 1) μ) : PolyEnvBound (P.k + 2) (envStepX P.k P.μ0 μK μ) := by
  intro alpha ha ha2
  have hX := two_div_ge_two ha ha2
  -- the input parameter, the lower-degree bound, the step and `Eloc`
  obtain ⟨he0, he8, hei, hy0, hyle, hyi⟩ := P.yIn_boundsX ha ha2 H.hV H.hVμ H.hμ0
  have hy2 : P.yIn alpha ≤ 1 / 2 := hyle.trans ha2
  obtain ⟨β, σ, T, hB, b0, b1, s0, s16, bi, si⟩ := hlow _ hy0 hy2
  have hstep := P.inverse_step H.hV H.hK H.hp hk hcov hrec ha ha2 hB b0 s0 s16
  obtain ⟨hEl0, hEli⟩ := P.Eloc_inv_leX H ha ha2
  obtain ⟨-, hEl2, -⟩ := P.Eloc_pos_le H.hV H.hp ha ha2
  set k := P.k with hkdef
  set E := GenParamsX.expDegX k P.μ0 μK with hEdef
  set dd := GenParamsX.densDegX k P.μ0 with hdddef
  set M1 := dd + 1 + μ with hM1def
  obtain ⟨-, hYμ⟩ := input_scale_le (μ := μ) ha ha2 hy0 hyi
  have bi' : β⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) := bi.trans hYμ
  have si' : σ⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) := si.trans hYμ
  have hei' : (P.eta alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) :=
    pw_mono hX hei (by rw [hM1def, hdddef]; unfold GenParamsX.densDegX; omega)
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
    unfold envStepX; rw [← hdddef]; omega
  · unfold envStepX; rw [← hdddef, ← hEdef]; omega


/-- The envelope after one step, with the threshold, without the cubic branch. -/
def envStepXTx (k μ0 μK μ : Nat) : Nat :=
  max (GenParamsX.densDegX k μ0 + μ + 4 * (k + 3) ^ 2 + 14)
    (max (GenParamsX.threshDegX k μ0 μK + 3) (k + 20))

/-- **The single-piece step, with envelopes and the sharper phase-refinement
threshold.** -/
theorem envBound_stepXx (P : GenParamsX) {μV μK μ : Nat} (H : P.CHyp μV μK) (hk : 1 ≤ P.k)
    (hcov : ∀ l, 1 ≤ l → l ≤ P.k → PolyCoverAt l (uCount P.V (uDegX l)) (uExp P.V (uDegX l)))
    (hrec : Section16RecurrenceProfileWith P.k (familyRecThr P.k P.K P.p) (familyRecExp P.k P.p))
    (hlow : EnvBound (P.k + 1) μ) : EnvBound (P.k + 2) (envStepXTx P.k P.μ0 μK μ) := by
  intro alpha ha ha2
  have hX := two_div_ge_two ha ha2
  -- everything that mentions `P.k`, before naming it
  obtain ⟨he0, he8, hei, hy0, hyle, hyi⟩ := P.yIn_boundsX ha ha2 H.hV H.hVμ H.hμ0
  have hy2 : P.yIn alpha ≤ 1 / 2 := hyle.trans ha2
  obtain ⟨β, σ, T, hB, b0, b1, s0, s16, bi, si, Ti⟩ := hlow _ hy0 hy2
  have hstep := P.inverse_step H.hV H.hK H.hp hk hcov hrec ha ha2 hB b0 s0 s16
  obtain ⟨hEl0, hEli⟩ := P.Eloc_inv_leX H ha ha2
  obtain ⟨-, hEl2, -⟩ := P.Eloc_pos_le H.hV H.hp ha ha2
  have hTl := P.Tloc_le_expX H hk ha ha2
  set k := P.k with hkdef
  set E := GenParamsX.expDegX k P.μ0 μK with hEdef
  set Th := GenParamsX.threshDegX k P.μ0 μK with hThdef
  set dd := GenParamsX.densDegX k P.μ0 with hdddef
  set M1 := dd + 1 + μ with hM1def
  have hETh : E + 4 ≤ Th := by rw [hThdef]; unfold GenParamsX.threshDegX; exact le_max_left _ _
  have hk3 : k + 2 ≤ (k + 2) ^ 3 := Nat.le_self_pow (by norm_num) _
  obtain ⟨-, hYμ⟩ := input_scale_le (μ := μ) ha ha2 hy0 hyi
  have bi' : β⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) := bi.trans hYμ
  have si' : σ⁻¹ ≤ Real.exp ((2 / alpha) ^ (2 ^ M1)) := si.trans (Real.exp_le_exp.mpr hYμ)
  have Ti' : T ≤ Real.exp (Real.exp ((2 / alpha) ^ (2 ^ M1))) :=
    Ti.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hYμ))
  have hei' : (P.eta alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) :=
    pw_mono hX hei (by rw [hM1def, hdddef]; unfold GenParamsX.densDegX; omega)
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
    unfold envStepXTx; rw [← hdddef]; omega
  · unfold envStepXTx; rw [← hdddef, ← hThdef]; omega
  · refine max_le (dex_mono hX hshort ?_) (dex_mono hX hinv ?_)
    · unfold envStepXTx; rw [← hdddef, ← hThdef]; omega
    · unfold envStepXTx; rw [← hdddef, ← hThdef]; omega



/-- The polynomial bound on the family constants: `K, p ≤ 2^(2^(4k+16))`. -/
def genMuKX (k : Nat) : Nat := 4 * k + 16

/-- The standing hypotheses at the polynomial base budget. -/
theorem tightHyp_of_profiles_fejerX (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ (4 * k + 16))) {k : Nat}
    (hk : 2 ≤ k) :
    (⟨classV Kc pc k, k, Kc k, pc k, tightMu0X k⟩ : GenParamsX).CHyp (tightMuW k) (genMuKX k) := by
  have hKr : (Kc k : Real) ≤ 2 ^ ((2 : Nat) ^ genMuKX k) := by
    have := hconst k; unfold genMuKX; linarith [Nat.cast_nonneg (α := Real) (pc k)]
  have hpr : (pc k : Real) ≤ 2 ^ ((2 : Nat) ^ genMuKX k) := by
    have := hconst k; unfold genMuKX; linarith [Nat.cast_nonneg (α := Real) (Kc k)]
  refine ⟨one_le_classV Kc pc k, classV_le_poly Kc pc hconst k, le_rfl, ?_, hK k, ?_, hp k, ?_⟩
  · show k ≤ 2 ^ tightMu0X k
    calc k ≤ 2 ^ k := Nat.lt_two_pow_self.le
      _ ≤ 2 ^ tightMu0X k := Nat.pow_le_pow_right (by norm_num) (by
          unfold tightMu0X; have := five_k_le_pDeg k
          have := le_max_right (tightMuW k) (pDeg k); omega)
  · have : ((Kc k : Nat) : Real) ≤ ((2 ^ 2 ^ genMuKX k : Nat) : Real) := by push_cast; exact hKr
    exact_mod_cast this
  · have : ((pc k : Nat) : Real) ≤ ((2 ^ 2 ^ genMuKX k : Nat) : Real) := by push_cast; exact hpr
    exact_mod_cast this


/-- The Theorem 18.1 envelope at the tight base budget. -/
def polyGenMuX : Nat → Nat
  | 0 => 74
  | 1 => 74
  | k + 2 => envStepX (k + 2) (tightMu0X (k + 2)) (genMuKX (k + 2)) (polyGenMuX (k + 1))

theorem polyGenMuX_succ {k : Nat} (hk : 1 ≤ k) :
    polyGenMuX (k + 1) = envStepX (k + 1) (tightMu0X (k + 1)) (genMuKX (k + 1)) (polyGenMuX k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rfl


theorem polyEnvBound_allX (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ (4 * k + 16)))
    {Kφ : Real} {pφ : Nat} (hpp : ProgressionPhasePartition Kφ pφ) (hpφ : 0 < pφ)
    (hKφ : Kφ ≤ 2 ^ pφ) (hpφB : (pφ : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64)) :
    ∀ k, 2 ≤ k → PolyEnvBound (k + 2) (polyGenMuX k) := by
  have hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))) :=
    fun k hk => abstractFamilyLemma166At_of k (hK k) (hp k) (hrec k hk)
  have hK1 : ∀ k, 1 ≤ Kc k := fun k => le_trans (by norm_num) (hK k)
  have hstep : ∀ k, 2 ≤ k → ∀ μ, PolyEnvBound (k + 1) μ →
      PolyEnvBound (k + 2) (envStepX k (tightMu0X k) (genMuKX k) μ) := by
    intro k hk μ hlow
    let P : GenParamsX := ⟨classV Kc pc k, k, Kc k, pc k, tightMu0X k⟩
    have H : P.CHyp (tightMuW k) (genMuKX k) := tightHyp_of_profiles_fejerX Kc pc hK hp hconst hk
    have hcov : ∀ l, 1 ≤ l → l ≤ P.k →
        PolyCoverAt l (uCount P.V (uDegX l)) (uExp P.V (uDegX l)) := by
      intro l hl1 hlk
      have hcl := polyCoverAt_classX Kc pc hK1 hp hlem hl1
      exact hcl.uniform_mono (one_le_classV Kc pc l) (classV_mono Kc pc hlk) le_rfl
    exact polyEnvBound_stepX P H (by show 1 ≤ k; omega) hcov (hrec k (by omega)) hlow
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    exact hstep 2 le_rfl 74 (polyEnvBound_three_of_phase_partition hpp hpφ hKφ hpφB)
  | succ k hk ih =>
    rw [polyGenMuX_succ (by omega)]
    exact hstep (k + 1) (by omega) (polyGenMuX k) ih


/-- The Theorem 18.2 envelope at the tight base budget, without the cubic branch. -/
def genMuXX : Nat → Nat
  | 0 => 62
  | 1 => 62
  | k + 2 => envStepXTx (k + 2) (tightMu0X (k + 2)) (genMuKX (k + 2)) (genMuXX (k + 1))

theorem genMuXX_succ {k : Nat} (hk : 1 ≤ k) :
    genMuXX (k + 1) = envStepXTx (k + 1) (tightMu0X (k + 1)) (genMuKX (k + 1)) (genMuXX k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rfl

theorem envBound_allXX (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ (4 * k + 16))) :
    ∀ k, 2 ≤ k → EnvBound (k + 2) (genMuXX k) := by
  have hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))) :=
    fun k hk => abstractFamilyLemma166At_of k (hK k) (hp k) (hrec k hk)
  have hK1 : ∀ k, 1 ≤ Kc k := fun k => le_trans (by norm_num) (hK k)
  have hstep : ∀ k, 2 ≤ k → ∀ μ, EnvBound (k + 1) μ →
      EnvBound (k + 2) (envStepXTx k (tightMu0X k) (genMuKX k) μ) := by
    intro k hk μ hlow
    let P : GenParamsX := ⟨classV Kc pc k, k, Kc k, pc k, tightMu0X k⟩
    have H : P.CHyp (tightMuW k) (genMuKX k) := tightHyp_of_profiles_fejerX Kc pc hK hp hconst hk
    have hcov : ∀ l, 1 ≤ l → l ≤ P.k →
        PolyCoverAt l (uCount P.V (uDegX l)) (uExp P.V (uDegX l)) := by
      intro l hl1 hlk
      have hcl := polyCoverAt_classX Kc pc hK1 hp hlem hl1
      exact hcl.uniform_mono (one_le_classV Kc pc l) (classV_mono Kc pc hlk) le_rfl
    exact envBound_stepXx P H (by show 1 ≤ k; omega) hcov (hrec k (by omega)) hlow
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact hstep 2 le_rfl 62 envBound_three
  | succ k hk ih =>
    rw [genMuXX_succ (by omega)]
    exact hstep (k + 1) (by omega) (genMuXX k) ih




/-! ### Closed forms -/

/-- Beyond the table one step costs `15·2^(k−1)` plus a polynomial. -/
theorem envStepX_le_tight {k : Nat} (hk : 13 ≤ k) (μ : Nat) :
    envStepX k (tightMu0X k) (genMuKX k) μ ≤
      μ + 15 * 2 ^ (k - 1) + 9 * (k + 4) ^ 2 + 4 * (k + 3) ^ 2 + 6 * k + 59 := by
  unfold envStepX GenParamsX.densDegX GenParamsX.expDegX GenParamsX.rhoDegX tightMu0X tightMuW
    genMuKX pDeg
  rw [tDegX_eq_of_ge hk]
  have := Nat.lt_two_pow_self (n := k - 1)
  generalize 4 * (k + 3) ^ 2 = q
  generalize (k + 4) ^ 2 = s
  generalize 2 ^ (k - 1) = y at *
  omega

/-- `32(k+5)² ≤ 2^k` for `k ≥ 15`. -/
theorem thirtytwo_sq_le_two_pow : ∀ k, 15 ≤ k → 32 * (k + 5) ^ 2 ≤ 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hstep : (k + 1 + 5) ^ 2 ≤ 2 * (k + 5) ^ 2 := by nlinarith
    calc 32 * (k + 1 + 5) ^ 2 ≤ 2 * (32 * (k + 5) ^ 2) := by omega
      _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left _ ih
      _ = 2 ^ (k + 1) := by rw [pow_succ]; ring

theorem polyGenMuX_fifteen : polyGenMuX 15 + 4 * 15 + 128 ≤ 16 * 2 ^ 15 := by decide +kernel

/-- **The Theorem 18.1 envelope at class constant `5/2`**: `μ_k + 4k + 128 ≤ 16·2^k`
for `k ≥ 15`. -/
theorem polyGenMuX_le16 : ∀ k, 15 ≤ k → polyGenMuX k + 4 * k + 128 ≤ 16 * 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact polyGenMuX_fifteen
  | succ k hk ih =>
    rw [polyGenMuX_succ (by omega)]
    have h1 := envStepX_le_tight (k := k + 1) (by omega) (polyGenMuX k)
    have h2 := thirtytwo_sq_le_two_pow k hk
    have h3 : (k + 4) ^ 2 ≤ (k + 5) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h4 : 6 * k + 70 ≤ (k + 5) ^ 2 := by nlinarith
    rw [show k + 1 + 4 = k + 5 by ring, show k + 1 + 3 = k + 4 by ring,
      show k + 1 - 1 = k by omega] at h1
    rw [pow_succ]
    generalize (k + 5) ^ 2 = s5 at *
    generalize (k + 4) ^ 2 = s4 at *
    generalize 2 ^ k = x at *
    omega

/-! ### The headline statement -/

/-- **Theorem 18.1 at every degree `d ≥ 17` with exponent `α^(2^(2^(d+2)))`**,
from the recurrence profiles with polynomial family constants. -/
theorem theorem_18_1_d2_seventeen_le_of_profiles_poly (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ (4 * k + 16)))
    {Kφ : Real} {pφ : Nat} (hpp : ProgressionPhasePartition Kφ pφ) (hpφ : 0 < pφ)
    (hKφ : Kφ ≤ 2 ^ pφ) (hpφB : (pφ : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64))
    {d : Nat} (hd : 17 ≤ d) : Theorem181AtSharp 2 d := by
  have henv := polyEnvBound_allX Kc pc hK hp hrec hconst hpp hpφ hKφ hpφB (d - 2) (by omega)
  rw [show d - 2 + 2 = d by omega] at henv
  refine theorem181AtSharp_of_polyEnvBound henv ?_
  have hle := polyGenMuX_le16 (d - 2) (by omega)
  have h2 : 2 ^ (d + 2) = 16 * 2 ^ (d - 2) := by
    rw [show d + 2 = (d - 2) + 4 by omega, pow_add]; ring
  rw [h2]
  omega


/-! ### Theorem 18.2 without offset -/

theorem envStepXTx_le_tight {k : Nat} (hk : 13 ≤ k) (μ : Nat) :
    envStepXTx k (tightMu0X k) (genMuKX k) μ ≤
      μ + 15 * 2 ^ (k - 1) + 9 * (k + 4) ^ 2 + 4 * (k + 3) ^ 2 + 6 * k + 59 := by
  unfold envStepXTx GenParamsX.densDegX GenParamsX.threshDegX GenParamsX.expDegX
    GenParamsX.rhoDegX tightMu0X tightMuW genMuKX pDeg
  rw [tDegX_eq_of_ge hk]
  have := Nat.lt_two_pow_self (n := k - 1)
  generalize 4 * (k + 3) ^ 2 = q
  generalize (k + 4) ^ 2 = s
  generalize 2 ^ (k - 1) = y at *
  omega

theorem envStepXTx_ge (k μ0 μK μ : Nat) : 5 * k + 33 ≤ envStepXTx k μ0 μK μ := by
  unfold envStepXTx GenParamsX.threshDegX
  omega

theorem genMuXX_fifteen : genMuXX 15 + 4 * 15 + 128 ≤ 16 * 2 ^ 15 := by decide +kernel

/-- **The Theorem 18.2 envelope at class constant `5/2`**: `μ_k + 4k + 128 ≤ 16·2^k`
for `k ≥ 15`. -/
theorem genMuXX_le16 : ∀ k, 15 ≤ k → genMuXX k + 4 * k + 128 ≤ 16 * 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact genMuXX_fifteen
  | succ k hk ih =>
    rw [genMuXX_succ (by omega)]
    have h1 := envStepXTx_le_tight (k := k + 1) (by omega) (genMuXX k)
    have h2 := thirtytwo_sq_le_two_pow k hk
    have h3 : (k + 4) ^ 2 ≤ (k + 5) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h4 : 6 * k + 70 ≤ (k + 5) ^ 2 := by nlinarith
    rw [show k + 1 + 4 = k + 5 by ring, show k + 1 + 3 = k + 4 by ring,
      show k + 1 - 1 = k by omega] at h1
    rw [pow_succ]
    generalize (k + 5) ^ 2 = s5 at *
    generalize (k + 4) ^ 2 = s4 at *
    generalize 2 ^ k = x at *
    omega

theorem genMuXX_ge {k : Nat} (hk : 2 ≤ k) : 5 * k + 33 ≤ genMuXX k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [genMuXX_succ (by omega)]
  exact envStepXTx_ge _ _ _ _

/-- **Theorem 18.2 at every length `L ≥ 19` with no offset**: threshold
`2^2^δ^-1^(2^2^L)` (printed: `L + 9`), from the recurrence profiles with
polynomial family constants. -/
theorem theorem_18_2_L0_nineteen_le_of_profiles_poly (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ (4 * k + 16)))
    {L : Nat} (hL : 19 ≤ L) : Theorem182AtSharp 0 L := by
  have henv := envBound_allXX Kc pc hK hp hrec hconst (L - 4) (by omega)
  rw [show L - 4 + 2 = L - 2 by omega] at henv
  have hge := genMuXX_ge (k := L - 4) (by omega)
  have hle := genMuXX_le16 (L - 4) (by omega)
  have h42 : 42 ≤ genMuXX (L - 4) := by omega
  have hLμ : 4 * L + 20 ≤ 2 ^ genMuXX (L - 4) := by
    have := Nat.lt_two_pow_self (n := genMuXX (L - 4))
    omega
  refine theorem182AtSharp_of_envBound (by omega) henv h42 hLμ ?_
  have h2 : 2 ^ (L + 0) = 16 * 2 ^ (L - 4) := by
    rw [show L + 0 = (L - 4) + 4 by omega, pow_add]; ring
  rw [h2]
  omega

/-- **Corollary 18.7 at every length `L ≥ 19` with no offset.** -/
theorem corollary_18_7_L0_nineteen_le_of_profiles_poly (Kc pc : Nat → Nat)
    (hK : ∀ k, 2 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ (4 * k + 16)))
    {L : Nat} (hL : 19 ≤ L) : Corollary187AtSharp 0 L :=
  (theorem_18_2_L0_nineteen_le_of_profiles_poly Kc pc hK hp hrec hconst hL).corollary_18_7

end LeanProofs.GowersSzemeredi
