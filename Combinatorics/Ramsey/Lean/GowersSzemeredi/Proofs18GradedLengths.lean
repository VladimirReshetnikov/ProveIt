import GowersSzemeredi.Proofs18GradedThresholds
import GowersSzemeredi.Proofs18GradedDegrees
import GowersSzemeredi.Proofs18GenericLengths

/-! **Theorem 18.2 and Corollary 18.7 at every length up to thirteen**, with
graded vertex providers (Notes L.10, G7).

`envBound_stepG` is `envBound_step` for the graded parameters, at the
envelope `envStepGT k μ₀ μK μ`, which is `envStep` with `densDegG` and
`threshDegG` (graded nest cost `136·3^k + 2^k − 136·2^k − 1`). `genMuG` runs the steps
in dimensions `2, …, k` from the Fejér cubic base `envBound_three`. No phase
partition is needed here: `EnvBound` allows an exponential `σ`. Evaluation
(`genMuG_fits`) shows lengths `6, …, 13` fit `2^(L+9)`; the uniform steps
stopped at ten. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The envelope after one graded step, with the threshold. -/
def envStepGT (k μ0 μK μ : Nat) : Nat :=
  max (GenParamsG.densDegG k μ0 + μ + 4 * (k + 3) ^ 2 + 14)
    (max (GenParamsG.threshDegG k μ0 μK + 3) (40 * (k + 2) ^ 3 + 1095))

/-- **The graded single-piece step, with envelopes.** -/
theorem envBound_stepG (P : GenParamsG) {μV μK μ : Nat} (H : P.GHyp μV μK) (hk : 1 ≤ P.k)
    (hcov : ∀ l, 1 ≤ l → l ≤ P.k → PolyCoverAt l (uCount P.V (uDeg68 l)) (uExp P.V (uDeg68 l)))
    (hrec : Section16RecurrenceProfileWith P.k (familyRecThr P.k P.K P.p) (familyRecExp P.k P.p))
    (hlow : EnvBound (P.k + 1) μ) : EnvBound (P.k + 2) (envStepGT P.k P.μ0 μK μ) := by
  intro alpha ha ha2
  have hX := two_div_ge_two ha ha2
  -- everything that mentions `P.k`, before naming it
  obtain ⟨he0, he8, hei, hy0, hyle, hyi⟩ := P.yIn_boundsG ha ha2 H.hV H.hVμ H.hμ0 H.hk0 H.hk68
  have hy2 : P.yIn alpha ≤ 1 / 2 := hyle.trans ha2
  obtain ⟨β, σ, T, hB, b0, b1, s0, s16, bi, si, Ti⟩ := hlow _ hy0 hy2
  have hstep := P.inverse_step H.hV H.hK H.hp hk hcov hrec ha ha2
    (P.lift_le ha ha2 H.hV H.hVμ H.hμ0) hB b0 s0 s16
  obtain ⟨hEl0, hEli⟩ := P.Eloc_inv_leG H ha ha2
  obtain ⟨-, hEl2, -⟩ := P.Eloc_pos_le H.hV H.hp ha ha2
  have hTl := P.Tloc_le_expG H hk ha ha2
  set k := P.k with hkdef
  set E := GenParamsG.expDegG k P.μ0 μK with hEdef
  set Th := GenParamsG.threshDegG k P.μ0 μK with hThdef
  set dd := GenParamsG.densDegG k P.μ0 with hdddef
  set M1 := dd + 1 + μ with hM1def
  have hETh : E + 4 ≤ Th := by rw [hThdef]; unfold GenParamsG.threshDegG; exact le_max_left _ _
  have hk3 : k + 2 ≤ (k + 2) ^ 3 := Nat.le_self_pow (by norm_num) _
  obtain ⟨-, hYμ⟩ := input_scale_le (μ := μ) ha ha2 hy0 hyi
  have bi' : β⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) := bi.trans hYμ
  have si' : σ⁻¹ ≤ Real.exp ((2 / alpha) ^ (2 ^ M1)) := si.trans (Real.exp_le_exp.mpr hYμ)
  have Ti' : T ≤ Real.exp (Real.exp ((2 / alpha) ^ (2 ^ M1))) :=
    Ti.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hYμ))
  have hei' : (P.eta alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) :=
    pw_mono hX hei (by rw [hM1def, hdddef]; unfold GenParamsG.densDegG; omega)
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
  have hinv := inv_thr_le hX (k := k) he0 heta1 b0 b1 hei' bi' s0 s16 σ0' hσ'
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
    unfold envStepGT; rw [← hdddef]; omega
  · unfold envStepGT; rw [← hdddef, ← hThdef]; omega
  · refine max_le (dex_mono hX hshort ?_) (dex_mono hX hinv ?_)
    · unfold envStepGT; rw [← hdddef, ← hThdef]; omega
    · unfold envStepGT; rw [← hdddef, ← hThdef]; omega

/-- The graded envelope of the degree-`(k+2)` bound after the steps in
dimensions `2, …, k`. -/
def genMuG : Nat → Nat
  | 0 => 62
  | 1 => 62
  | k + 2 => envStepGT (k + 2) (genMu0 (k + 2)) (genMuK (k + 2)) (genMuG (k + 1))

theorem genMuG_succ {k : Nat} (hk : 1 ≤ k) :
    genMuG (k + 1) = envStepGT (k + 1) (genMu0 (k + 1)) (genMuK (k + 1)) (genMuG k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rfl

/-- **Graded discrepancy bounds in every degree `k + 2 ≥ 4`**, from the
recurrence profiles. -/
theorem envBound_allG (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5)))) :
    ∀ k, 2 ≤ k → k + 1 ≤ 2 ^ 68 → EnvBound (k + 2) (genMuG k) := by
  have hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))) :=
    fun k hk => abstractFamilyLemma166At_of k (hK k) (hp k) (hrec k hk)
  have hK1 : ∀ k, 1 ≤ Kc k := fun k => le_trans (by norm_num) (hK k)
  have hstep : ∀ k, 2 ≤ k → k + 1 ≤ 2 ^ 68 → ∀ μ, EnvBound (k + 1) μ →
      EnvBound (k + 2) (envStepGT k (genMu0 k) (genMuK k) μ) := by
    intro k hk hk68 μ hlow
    obtain ⟨hV, hVμ, hμ0, -, -, hk0, hKk, hKμ, hpk, hpμ⟩ := stdHyp_of_profiles Kc pc hK hp hconst hk
    let P : GenParamsG := ⟨classV Kc pc k, k, Kc k, pc k, genMu0 k⟩
    have H : P.GHyp (genMuV k) (genMuK k) := ⟨hV, hVμ, hμ0, hk0, hk68, hKk, hKμ, hpk, hpμ⟩
    have hcov : ∀ l, 1 ≤ l → l ≤ P.k →
        PolyCoverAt l (uCount P.V (uDeg68 l)) (uExp P.V (uDeg68 l)) := by
      intro l hl1 hlk
      have hcl := polyCoverAt_class68 Kc pc hK1 hp hlem hl1
      exact hcl.uniform_mono (one_le_classV Kc pc l) (classV_mono Kc pc hlk) le_rfl
    exact envBound_stepG P H (by show 1 ≤ k; omega) hcov (hrec k (by omega)) hlow
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => intro hk68; exact hstep 2 le_rfl hk68 62 envBound_three
  | succ k hk ih =>
    intro hk68
    rw [genMuG_succ (by omega)]
    exact hstep (k + 1) (by omega) hk68 (genMuG k) (ih (by omega))

/-- The graded envelopes at `L = 6, …, 13` fit the printed threshold. -/
theorem genMuG_fits :
    (42 ≤ genMuG 2 ∧ genMuG 2 + 2 * 6 + 14 ≤ 2 ^ (6 + 9)) ∧
    (42 ≤ genMuG 3 ∧ genMuG 3 + 2 * 7 + 14 ≤ 2 ^ (7 + 9)) ∧
    (42 ≤ genMuG 4 ∧ genMuG 4 + 2 * 8 + 14 ≤ 2 ^ (8 + 9)) ∧
    (42 ≤ genMuG 5 ∧ genMuG 5 + 2 * 9 + 14 ≤ 2 ^ (9 + 9)) ∧
    (42 ≤ genMuG 6 ∧ genMuG 6 + 2 * 10 + 14 ≤ 2 ^ (10 + 9)) ∧
    (42 ≤ genMuG 7 ∧ genMuG 7 + 2 * 11 + 14 ≤ 2 ^ (11 + 9)) ∧
    (42 ≤ genMuG 8 ∧ genMuG 8 + 2 * 12 + 14 ≤ 2 ^ (12 + 9)) ∧
    (42 ≤ genMuG 9 ∧ genMuG 9 + 2 * 13 + 14 ≤ 2 ^ (13 + 9)) := by
  decide

/-- **Theorem 18.2 at every length `6 ≤ L ≤ 13`**, from the recurrence profiles. -/
theorem theorem_18_2_upto_thirteen_of_profiles (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {L : Nat} (hL6 : 6 ≤ L) (hL13 : L ≤ 13) : Theorem182At L := by
  have henv := envBound_allG Kc pc hK hp hrec hconst (L - 4) (by omega) (by omega)
  rw [show L - 4 + 2 = L - 2 by omega] at henv
  have hfit := genMuG_fits
  have h42 : ∀ μ : Nat, 42 ≤ μ → 4 * L + 20 ≤ 2 ^ μ := by
    intro μ hμ
    calc 4 * L + 20 ≤ 2 ^ 42 := by omega
      _ ≤ 2 ^ μ := Nat.pow_le_pow_right (by norm_num) hμ
  interval_cases L
  · exact theorem182At_of_envBound (by norm_num) henv hfit.1.1 (h42 _ hfit.1.1) hfit.1.2
  · exact theorem182At_of_envBound (by norm_num) henv hfit.2.1.1 (h42 _ hfit.2.1.1) hfit.2.1.2
  · exact theorem182At_of_envBound (by norm_num) henv hfit.2.2.1.1 (h42 _ hfit.2.2.1.1)
      hfit.2.2.1.2
  · exact theorem182At_of_envBound (by norm_num) henv hfit.2.2.2.1.1 (h42 _ hfit.2.2.2.1.1)
      hfit.2.2.2.1.2
  · exact theorem182At_of_envBound (by norm_num) henv hfit.2.2.2.2.1.1 (h42 _ hfit.2.2.2.2.1.1)
      hfit.2.2.2.2.1.2
  · exact theorem182At_of_envBound (by norm_num) henv hfit.2.2.2.2.2.1.1
      (h42 _ hfit.2.2.2.2.2.1.1) hfit.2.2.2.2.2.1.2
  · exact theorem182At_of_envBound (by norm_num) henv hfit.2.2.2.2.2.2.1.1
      (h42 _ hfit.2.2.2.2.2.2.1.1) hfit.2.2.2.2.2.2.1.2
  · exact theorem182At_of_envBound (by norm_num) henv hfit.2.2.2.2.2.2.2.1
      (h42 _ hfit.2.2.2.2.2.2.2.1) hfit.2.2.2.2.2.2.2.2

/-- **Corollary 18.7 at every length `6 ≤ L ≤ 13`**, from the recurrence profiles. -/
theorem corollary_18_7_upto_thirteen_of_profiles (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {L : Nat} (hL6 : 6 ≤ L) (hL13 : L ≤ 13) : Corollary187At L :=
  (theorem_18_2_upto_thirteen_of_profiles Kc pc hK hp hrec hconst hL6 hL13).corollary_18_7

end LeanProofs.GowersSzemeredi
