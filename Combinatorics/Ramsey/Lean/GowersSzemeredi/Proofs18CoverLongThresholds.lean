import GowersSzemeredi.Proofs18RefinementThresholdBounds
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
  have h32P := polyPartConst_mul32_le_pw hX k
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
  · refine pw_mono hX (inv_mul_div_four_le_pw hX he0 b0 hei' bi') ?_
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
