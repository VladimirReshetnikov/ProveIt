import GowersSzemeredi.Proofs18CoverExponentsFejer
import GowersSzemeredi.Proofs18CoverThresholdsSharp
import GowersSzemeredi.Proofs18EnvelopeInduction
import GowersSzemeredi.Proofs18TightClassesFejerSide

/-! **Theorem 18.1 at `d + 6` and Theorem 18.2 / Corollary 18.7 at `L + 4`,
from the recurrence profiles, under the Fejér θ₁** (Notes L.16d).

The Section 18 envelope of `Proofs18CoverTightBase` and
`Proofs18CoverThresholdsSharp` at the parameters `GenParamsF`: class covers
at degree `uDeg23 l` (`polyCoverAt_class23`), the Fejér θ₁ and the tight
radius in the single-piece step, and the tight base budget `tightMu0`. The
step lemmas and the recursions are generated from the corpus by a script;
the closed forms are new.

One step now costs `101·2^k + 4(k+3)² + k + 39`
(`envStepF_le_tight`, `envStepFTx_le_tight`): the vertex covers `23·2^k`,
the base budget `32·2^k` and the two slice controls `2·23·2^k`, against the
printed `68 + 32 + 136 = 236`. So the envelopes grow like `202·2^k`, below
the `256·2^k` that `d + 6` and `L + 4` allow
(`models/model_fejer_envelope_exact.py`: at most `219·2^k`):
* `polyGenMuF_le`, `genMuXF_le`: at most `230·2^k` for `k ≥ 4`;
* `theorem_18_1_d6_of_profiles_cover`: **Theorem 18.1 at every degree
  `d ≥ 4` with exponent `α^(2^(2^(d+6)))`** (printed `d + 10`, corpus best
  `d + 7`);
* `theorem_18_2_L4_all_of_profiles_cover`,
  `corollary_18_7_L4_all_of_profiles_cover`: **Theorem 18.2 and
  Corollary 18.7 at every length `L ≥ 6` with `L + 4`** (printed `L + 9`,
  corpus best `L + 5`). -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The envelope after one step (no threshold). -/
def envStepF (k μ0 μK μ : Nat) : Nat :=
  max (GenParamsF.densDegF k μ0 + μ + 4 * (k + 3) ^ 2 + 14) (GenParamsF.expDegF k μ0 μK + 6)

/-- **The single-piece step with polynomial envelopes.** -/
theorem polyEnvBound_stepF (P : GenParamsF) {μV μK μ : Nat} (H : P.CHyp μV μK) (hk : 1 ≤ P.k)
    (hcov : ∀ l, 1 ≤ l → l ≤ P.k → PolyCoverAt l (uCount P.V (uDeg23 l)) (uExp P.V (uDeg23 l)))
    (hrec : Section16RecurrenceProfileWith P.k (familyRecThr P.k P.K P.p) (familyRecExp P.k P.p))
    (hlow : PolyEnvBound (P.k + 1) μ) : PolyEnvBound (P.k + 2) (envStepF P.k P.μ0 μK μ) := by
  intro alpha ha ha2
  have hX := two_div_ge_two ha ha2
  -- the input parameter, the lower-degree bound, the step and `Eloc`
  obtain ⟨he0, he8, hei, hy0, hyle, hyi⟩ := P.yIn_boundsF ha ha2 H.hV H.hVμ H.hμ0
  have hy2 : P.yIn alpha ≤ 1 / 2 := hyle.trans ha2
  obtain ⟨β, σ, T, hB, b0, b1, s0, s16, bi, si⟩ := hlow _ hy0 hy2
  have hstep := P.inverse_step H.hV H.hK H.hp hk hcov hrec ha ha2 hB b0 s0 s16
  obtain ⟨hEl0, hEli⟩ := P.Eloc_inv_leF H ha ha2
  obtain ⟨-, hEl2, -⟩ := P.Eloc_pos_le H.hV H.hp ha ha2
  set k := P.k with hkdef
  set E := GenParamsF.expDegF k P.μ0 μK with hEdef
  set dd := GenParamsF.densDegF k P.μ0 with hdddef
  set M1 := dd + 1 + μ with hM1def
  obtain ⟨-, hYμ⟩ := input_scale_le (μ := μ) ha ha2 hy0 hyi
  have bi' : β⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) := bi.trans hYμ
  have si' : σ⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) := si.trans hYμ
  have hei' : (P.eta alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) :=
    pw_mono hX hei (by rw [hM1def, hdddef]; unfold GenParamsF.densDegF; omega)
  have heta1 : P.eta alpha ≤ 1 := by linarith
  obtain ⟨σ0', σ16', σeq⟩ := sigma_step (d := k + 1) hEl0 hEl2 s0 s16
  have h32P := polyPartConst_mul32_le_pw hX k
  set S := max (max (4 * (k + 3) ^ 2 + 4) (E + 3) + 1) M1 + 1 with hSdef
  have hσ' : (inverseStepExponent (k + 1) (P.Eloc alpha) σ)⁻¹ ≤ (2 / alpha) ^ (2 ^ S) := by
    rw [σeq]
    have hx0 : 0 ≤ 32 * (polynomialPartitionConstant (k + 1 + 1) : Real) * (P.Eloc alpha)⁻¹ :=
      mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (inv_pos.mpr hEl0).le
    have h1 := pw_mul' hX (inv_pos.mpr hEl0).le
      h32P hEli
    exact pw_mul' hX (inv_pos.mpr s0).le h1 si'
  -- assemble
  refine ⟨P.eta alpha * β / 4, _, _, hstep, div_pos (mul_pos he0 b0) (by norm_num), ?_, σ0', σ16',
    ?_, pw_mono hX hσ' ?_⟩
  · have : P.eta alpha * β ≤ 1 := mul_le_one₀ heta1 b0.le b1
    linarith
  · refine pw_mono hX (inv_mul_div_four_le_pw hX he0 b0 hei' bi') ?_
    unfold envStepF; rw [← hdddef]; omega
  · unfold envStepF; rw [← hdddef, ← hEdef]; omega


/-- The envelope after one step, with the threshold, without the cubic branch. -/
def envStepFTx (k μ0 μK μ : Nat) : Nat :=
  max (GenParamsF.densDegF k μ0 + μ + 4 * (k + 3) ^ 2 + 14)
    (max (GenParamsF.threshDegF k μ0 μK + 3) (k + 20))

/-- **The single-piece step, with envelopes and the sharper phase-refinement
threshold.** -/
theorem envBound_stepFx (P : GenParamsF) {μV μK μ : Nat} (H : P.CHyp μV μK) (hk : 1 ≤ P.k)
    (hcov : ∀ l, 1 ≤ l → l ≤ P.k → PolyCoverAt l (uCount P.V (uDeg23 l)) (uExp P.V (uDeg23 l)))
    (hrec : Section16RecurrenceProfileWith P.k (familyRecThr P.k P.K P.p) (familyRecExp P.k P.p))
    (hlow : EnvBound (P.k + 1) μ) : EnvBound (P.k + 2) (envStepFTx P.k P.μ0 μK μ) := by
  intro alpha ha ha2
  have hX := two_div_ge_two ha ha2
  -- everything that mentions `P.k`, before naming it
  obtain ⟨he0, he8, hei, hy0, hyle, hyi⟩ := P.yIn_boundsF ha ha2 H.hV H.hVμ H.hμ0
  have hy2 : P.yIn alpha ≤ 1 / 2 := hyle.trans ha2
  obtain ⟨β, σ, T, hB, b0, b1, s0, s16, bi, si, Ti⟩ := hlow _ hy0 hy2
  have hstep := P.inverse_step H.hV H.hK H.hp hk hcov hrec ha ha2 hB b0 s0 s16
  obtain ⟨hEl0, hEli⟩ := P.Eloc_inv_leF H ha ha2
  obtain ⟨-, hEl2, -⟩ := P.Eloc_pos_le H.hV H.hp ha ha2
  have hTl := P.Tloc_le_expF H hk ha ha2
  set k := P.k with hkdef
  set E := GenParamsF.expDegF k P.μ0 μK with hEdef
  set Th := GenParamsF.threshDegF k P.μ0 μK with hThdef
  set dd := GenParamsF.densDegF k P.μ0 with hdddef
  set M1 := dd + 1 + μ with hM1def
  have hETh : E + 4 ≤ Th := by rw [hThdef]; unfold GenParamsF.threshDegF; exact le_max_left _ _
  have hk3 : k + 2 ≤ (k + 2) ^ 3 := Nat.le_self_pow (by norm_num) _
  obtain ⟨-, hYμ⟩ := input_scale_le (μ := μ) ha ha2 hy0 hyi
  have bi' : β⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) := bi.trans hYμ
  have si' : σ⁻¹ ≤ Real.exp ((2 / alpha) ^ (2 ^ M1)) := si.trans (Real.exp_le_exp.mpr hYμ)
  have Ti' : T ≤ Real.exp (Real.exp ((2 / alpha) ^ (2 ^ M1))) :=
    Ti.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hYμ))
  have hei' : (P.eta alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) :=
    pw_mono hX hei (by rw [hM1def, hdddef]; unfold GenParamsF.densDegF; omega)
  have heta1 : P.eta alpha ≤ 1 := by linarith
  -- the localization exponent and `σ′`
  obtain ⟨σ0', σ16', σeq⟩ := sigma_step (d := k + 1) hEl0 hEl2 s0 s16
  have h32P := polyPartConst_mul32_le_pw hX k
  set S := max (max (4 * (k + 3) ^ 2 + 4) (E + 3) + 1) M1 + 1 with hSdef
  have hσ' : (inverseStepExponent (k + 1) (P.Eloc alpha) σ)⁻¹ ≤
      Real.exp ((2 / alpha) ^ (2 ^ S)) := by
    rw [σeq]
    have h1 := pw_mul' hX (inv_pos.mpr hEl0).le
      h32P hEli
    exact ex_mul' hX (inv_pos.mpr s0).le (ex_of_pw h1) si'
  -- the thresholds
  have hshort := short_thr_step_le hX (k := k) hEl0 hEli Ti' hTl
  have hinv := inv_thr_le_ex hX (k := k) he0 heta1 b0 b1 hei' bi' s0 s16 σ0' hσ'
  -- assemble
  refine ⟨P.eta alpha * β / 4, _, _, hstep, div_pos (mul_pos he0 b0) (by norm_num), ?_, σ0', σ16',
    ?_, ex_mono hX hσ' ?_, ?_⟩
  · have : P.eta alpha * β ≤ 1 := mul_le_one₀ heta1 b0.le b1
    linarith
  · refine pw_mono hX (inv_mul_div_four_le_pw hX he0 b0 hei' bi') ?_
    unfold envStepFTx; rw [← hdddef]; omega
  · unfold envStepFTx; rw [← hdddef, ← hThdef]; omega
  · refine max_le (dex_mono hX hshort ?_) (dex_mono hX hinv ?_)
    · unfold envStepFTx; rw [← hdddef, ← hThdef]; omega
    · unfold envStepFTx; rw [← hdddef, ← hThdef]; omega



/-- The Theorem 18.1 envelope at the tight base budget. -/
def polyGenMuF : Nat → Nat
  | 0 => 74
  | 1 => 74
  | k + 2 => envStepF (k + 2) (tightMu0 (k + 2)) (genMuK (k + 2)) (polyGenMuF (k + 1))

theorem polyGenMuF_succ {k : Nat} (hk : 1 ≤ k) :
    polyGenMuF (k + 1) = envStepF (k + 1) (tightMu0 (k + 1)) (genMuK (k + 1)) (polyGenMuF k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rfl


theorem polyEnvBound_allF (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {Kφ : Real} {pφ : Nat} (hpp : ProgressionPhasePartition Kφ pφ) (hpφ : 0 < pφ)
    (hKφ : Kφ ≤ 2 ^ pφ) (hpφB : (pφ : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64)) :
    ∀ k, 2 ≤ k → PolyEnvBound (k + 2) (polyGenMuF k) := by
  have hstep : ∀ k, 2 ≤ k → ∀ μ, PolyEnvBound (k + 1) μ →
      PolyEnvBound (k + 2) (envStepF k (tightMu0 k) (genMuK k) μ) := by
    intro k hk μ hlow
    let P : GenParamsF := ⟨classV Kc pc k, k, Kc k, pc k, tightMu0 k⟩
    have H : P.CHyp (tightMuV k) (genMuK k) := tightHyp_of_profiles_fejer Kc pc hK hp hconst hk
    have hcov := classCovers_of_profiles Kc pc hK hp hrec (degree := uDeg23) (k := k)
      (fun hK1 => polyCoverAt_class23 Kc pc hK1 hp)
    exact polyEnvBound_stepF P H (by show 1 ≤ k; omega) hcov (hrec k (by omega)) hlow
  intro k hk
  exact envelope_induction (P := PolyEnvBound) (budget := polyGenMuF) hstep
    (polyEnvBound_three_of_phase_partition hpp hpφ hKφ hpφB) (fun _ h => polyGenMuF_succ h) k (by omega)


/-- The Theorem 18.2 envelope at the tight base budget, without the cubic branch. -/
def genMuXF : Nat → Nat
  | 0 => 62
  | 1 => 62
  | k + 2 => envStepFTx (k + 2) (tightMu0 (k + 2)) (genMuK (k + 2)) (genMuXF (k + 1))

theorem genMuXF_succ {k : Nat} (hk : 1 ≤ k) :
    genMuXF (k + 1) = envStepFTx (k + 1) (tightMu0 (k + 1)) (genMuK (k + 1)) (genMuXF k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rfl

theorem envBound_allXF (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5)))) :
    ∀ k, 2 ≤ k → EnvBound (k + 2) (genMuXF k) := by
  have hstep : ∀ k, 2 ≤ k → ∀ μ, EnvBound (k + 1) μ →
      EnvBound (k + 2) (envStepFTx k (tightMu0 k) (genMuK k) μ) := by
    intro k hk μ hlow
    let P : GenParamsF := ⟨classV Kc pc k, k, Kc k, pc k, tightMu0 k⟩
    have H : P.CHyp (tightMuV k) (genMuK k) := tightHyp_of_profiles_fejer Kc pc hK hp hconst hk
    have hcov := classCovers_of_profiles Kc pc hK hp hrec (degree := uDeg23) (k := k)
      (fun hK1 => polyCoverAt_class23 Kc pc hK1 hp)
    exact envBound_stepFx P H (by show 1 ≤ k; omega) hcov (hrec k (by omega)) hlow
  intro k hk
  exact envelope_induction (P := EnvBound) (budget := genMuXF) hstep
    envBound_three (fun _ h => genMuXF_succ h) k (by omega)



/-! ### Closed forms -/

/-- One step at the tight base budget costs `101·2^k` plus a polynomial. -/
theorem envStepF_le_tight (k μ : Nat) :
    envStepF k (tightMu0 k) (genMuK k) μ ≤ μ + 101 * 2 ^ k + 4 * (k + 3) ^ 2 + k + 39 := by
  unfold envStepF GenParamsF.densDegF GenParamsF.expDegF GenParamsF.rhoDegF tightMu0 tightMuV
    genMuK fixDeg
  rw [two_pow_five_mul, two_pow_four_mul]
  have := Nat.lt_two_pow_self (n := k)
  generalize 4 * (k + 3) ^ 2 = q
  generalize 2 ^ k = x at *
  omega

theorem envStepFTx_le_tight (k μ : Nat) :
    envStepFTx k (tightMu0 k) (genMuK k) μ ≤ μ + 101 * 2 ^ k + 4 * (k + 3) ^ 2 + k + 39 := by
  unfold envStepFTx GenParamsF.densDegF GenParamsF.threshDegF GenParamsF.expDegF
    GenParamsF.rhoDegF tightMu0 tightMuV genMuK fixDeg
  rw [two_pow_six_mul, two_pow_five_mul, two_pow_four_mul]
  have := Nat.lt_two_pow_self (n := k)
  generalize 4 * (k + 3) ^ 2 = q
  generalize 2 ^ k = x at *
  omega

theorem envStepFTx_ge_tight (k μ : Nat) :
    μ + 101 * 2 ^ k ≤ envStepFTx k (tightMu0 k) (genMuK k) μ := by
  unfold envStepFTx GenParamsF.densDegF GenParamsF.rhoDegF tightMu0 tightMuV fixDeg
  rw [two_pow_five_mul, two_pow_four_mul]
  generalize 4 * (k + 3) ^ 2 = q
  generalize 2 ^ k = x at *
  omega

theorem polyGenMuF_small : polyGenMuF 2 + 1 ≤ 2 ^ (4 + 6) ∧ polyGenMuF 3 + 1 ≤ 2 ^ (5 + 6) ∧
    polyGenMuF 4 ≤ 230 * 2 ^ 4 := by
  decide

/-- **The Theorem 18.1 envelope under the Fejér θ₁ is `≤ 230·2^k`**, `k ≥ 4`. -/
theorem polyGenMuF_le : ∀ k, 4 ≤ k → polyGenMuF k ≤ 230 * 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact polyGenMuF_small.2.2
  | succ k hk ih =>
    rw [polyGenMuF_succ (by omega)]
    have h1 := envStepF_le_tight (k + 1) (polyGenMuF k)
    have h2 := sq_le_two_pow_four k hk
    have h3 : 16 ≤ 2 ^ k := le_trans (by norm_num : 16 ≤ 2 ^ 4) (Nat.pow_le_pow_right (by norm_num) hk)
    have h4 := Nat.lt_two_pow_self (n := k)
    rw [show k + 1 + 3 = k + 4 by ring] at h1
    rw [pow_succ] at h1 ⊢
    generalize (k + 4) ^ 2 = s at *
    generalize 2 ^ k = x at *
    omega

theorem genMuXF_small : genMuXF 2 + 2 * 6 + 14 ≤ 2 ^ (6 + 4) ∧
    genMuXF 3 + 2 * 7 + 14 ≤ 2 ^ (7 + 4) ∧ genMuXF 4 ≤ 230 * 2 ^ 4 := by
  decide

/-- **The Theorem 18.2 envelope under the Fejér θ₁ is `≤ 230·2^k`**, `k ≥ 4`. -/
theorem genMuXF_le : ∀ k, 4 ≤ k → genMuXF k ≤ 230 * 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact genMuXF_small.2.2
  | succ k hk ih =>
    rw [genMuXF_succ (by omega)]
    have h1 := envStepFTx_le_tight (k + 1) (genMuXF k)
    have h2 := sq_le_two_pow_four k hk
    have h3 : 16 ≤ 2 ^ k := le_trans (by norm_num : 16 ≤ 2 ^ 4) (Nat.pow_le_pow_right (by norm_num) hk)
    have h4 := Nat.lt_two_pow_self (n := k)
    rw [show k + 1 + 3 = k + 4 by ring] at h1
    rw [pow_succ] at h1 ⊢
    generalize (k + 4) ^ 2 = s at *
    generalize 2 ^ k = x at *
    omega

theorem genMuXF_ge : ∀ k, 2 ≤ k → 101 * 2 ^ k ≤ genMuXF k := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [genMuXF_succ (by omega)]
  have := envStepFTx_ge_tight (j + 1) (genMuXF j)
  omega

/-! ### The headline statements -/

/-- **Theorem 18.1 at every degree `d ≥ 4` with exponent `α^(2^(2^(d+6)))`**,
from the recurrence profiles and a phase partition. -/
theorem theorem_18_1_d6_of_profiles_cover (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {Kφ : Real} {pφ : Nat} (hpp : ProgressionPhasePartition Kφ pφ) (hpφ : 0 < pφ)
    (hKφ : Kφ ≤ 2 ^ pφ) (hpφB : (pφ : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64))
    {d : Nat} (hd4 : 4 ≤ d) : Theorem181AtSharp 6 d := by
  have henv := polyEnvBound_allF Kc pc hK hp hrec hconst hpp hpφ hKφ hpφB (d - 2) (by omega)
  rw [show d - 2 + 2 = d by omega] at henv
  refine theorem181AtSharp_of_polyEnvBound henv ?_
  rcases Nat.lt_or_ge d 6 with h | h
  · obtain ⟨h4, h5, -⟩ := polyGenMuF_small
    interval_cases d
    · exact h4
    · exact h5
  · have hle := polyGenMuF_le (d - 2) (by omega)
    have h2 : 2 ^ (d + 6) = 256 * 2 ^ (d - 2) := by
      rw [show d + 6 = (d - 2) + 8 by omega, pow_add]; ring
    rw [h2]
    have := Nat.one_le_two_pow (n := d - 2)
    omega

/-- **Theorem 18.2 at every length `L ≥ 6` with `L + 4` in the threshold**,
from the recurrence profiles. -/
theorem theorem_18_2_L4_all_of_profiles_cover (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {L : Nat} (hL6 : 6 ≤ L) : Theorem182AtSharp 4 L := by
  have henv := envBound_allXF Kc pc hK hp hrec hconst (L - 4) (by omega)
  rw [show L - 4 + 2 = L - 2 by omega] at henv
  have hge := genMuXF_ge (L - 4) (by omega)
  have hk := Nat.lt_two_pow_self (n := L - 4)
  have h4 : 4 ≤ 2 ^ (L - 4) :=
    le_trans (by norm_num : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h42 : 42 ≤ genMuXF (L - 4) := by omega
  have hLμ : 4 * L + 20 ≤ 2 ^ genMuXF (L - 4) := by
    have := Nat.lt_two_pow_self (n := genMuXF (L - 4))
    omega
  refine theorem182AtSharp_of_envBound (by omega) henv h42 hLμ ?_
  rcases Nat.lt_or_ge L 8 with hL | hL
  · obtain ⟨h6, h7, -⟩ := genMuXF_small
    interval_cases L
    · exact h6
    · exact h7
  · have hle := genMuXF_le (L - 4) (by omega)
    have h16 : 16 ≤ 2 ^ (L - 4) :=
      le_trans (by norm_num : 16 ≤ 2 ^ 4) (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 : 2 ^ (L + 4) = 256 * 2 ^ (L - 4) := by
      rw [show L + 4 = (L - 4) + 8 by omega, pow_add]; ring
    rw [h2]
    omega

/-- **Corollary 18.7 at every length `L ≥ 6` with `L + 4`**, from the profiles. -/
theorem corollary_18_7_L4_all_of_profiles_cover (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {L : Nat} (hL6 : 6 ≤ L) : Corollary187AtSharp 4 L :=
  (theorem_18_2_L4_all_of_profiles_cover Kc pc hK hp hrec hconst hL6).corollary_18_7

end LeanProofs.GowersSzemeredi
