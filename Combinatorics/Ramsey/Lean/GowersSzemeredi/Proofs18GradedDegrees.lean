import GowersSzemeredi.Proofs18GradedExponents
import GowersSzemeredi.Proofs18PolyDegrees

/-! **Theorem 18.1 at degree nine**, with graded vertex providers
(Notes L.10, G5).

`polyEnvBound_stepG` is `polyEnvBound_step` for the graded parameters.
Theorem 18.1 needs no threshold envelope, so the new envelope is
`envStepG k μ₀ μK μ = max(densDegG + μ + 4(k+3)² + 14, expDegG + 6)`.
Here `densDegG` and `expDegG` carry the graded nest cost `136·3^k + 2^k − 136·2^k − 1`
instead of `(68·2^k + 1)(2^k − 1)`.

`polyGenMuG` runs the graded steps in dimensions `2, …, k` from the
degree-three base `PolyEnvBound 3 74`. Evaluation (`polyGenMuG_fits`) shows
that degrees `4, …, 9` fit `2^(d+10)`; the uniform steps stopped at seven. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The envelope after one graded step (no threshold). -/
def envStepG (k μ0 μK μ : Nat) : Nat :=
  max (GenParamsG.densDegG k μ0 + μ + 4 * (k + 3) ^ 2 + 14) (GenParamsG.expDegG k μ0 μK + 6)

/-- **The graded single-piece step with polynomial envelopes.** -/
theorem polyEnvBound_stepG (P : GenParamsG) {μV μK μ : Nat} (H : P.GHyp μV μK) (hk : 1 ≤ P.k)
    (hcov : ∀ l, 1 ≤ l → l ≤ P.k → PolyCoverAt l (uCount P.V (uDeg68 l)) (uExp P.V (uDeg68 l)))
    (hrec : Section16RecurrenceProfileWith P.k (familyRecThr P.k P.K P.p) (familyRecExp P.k P.p))
    (hlow : PolyEnvBound (P.k + 1) μ) : PolyEnvBound (P.k + 2) (envStepG P.k P.μ0 μK μ) := by
  intro alpha ha ha2
  have hX := two_div_ge_two ha ha2
  -- the input parameter, the lower-degree bound, the step and `Eloc`
  obtain ⟨he0, he8, hei, hy0, hyle, hyi⟩ := P.yIn_boundsG ha ha2 H.hV H.hVμ H.hμ0 H.hk0 H.hk68
  have hy2 : P.yIn alpha ≤ 1 / 2 := hyle.trans ha2
  obtain ⟨β, σ, T, hB, b0, b1, s0, s16, bi, si⟩ := hlow _ hy0 hy2
  have hstep := P.inverse_step H.hV H.hK H.hp hk hcov hrec ha ha2
    (P.lift_le ha ha2 H.hV H.hVμ H.hμ0) hB b0 s0 s16
  obtain ⟨hEl0, hEli⟩ := P.Eloc_inv_leG H ha ha2
  obtain ⟨-, hEl2, -⟩ := P.Eloc_pos_le H.hV H.hp ha ha2
  set k := P.k with hkdef
  set E := GenParamsG.expDegG k P.μ0 μK with hEdef
  set dd := GenParamsG.densDegG k P.μ0 with hdddef
  set M1 := dd + 1 + μ with hM1def
  obtain ⟨-, hYμ⟩ := input_scale_le (μ := μ) ha ha2 hy0 hyi
  have bi' : β⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) := bi.trans hYμ
  have si' : σ⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) := si.trans hYμ
  have hei' : (P.eta alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) :=
    pw_mono hX hei (by rw [hM1def, hdddef]; unfold GenParamsG.densDegG; omega)
  have heta1 : P.eta alpha ≤ 1 := by linarith
  obtain ⟨σ0', σ16', σeq⟩ := sigma_step (d := k + 1) hEl0 hEl2 s0 s16
  have h32P := polyPartConst_mul32_le_pw hX k
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
  · refine pw_mono hX (inv_mul_div_four_le_pw hX he0 b0 hei' bi') ?_
    unfold envStepG; rw [← hdddef]; omega
  · unfold envStepG; rw [← hdddef, ← hEdef]; omega

/-- The graded polynomial envelope of the degree-`(k+2)` bound. -/
def polyGenMuG : Nat → Nat
  | 0 => 74
  | 1 => 74
  | k + 2 => envStepG (k + 2) (genMu0 (k + 2)) (genMuK (k + 2)) (polyGenMuG (k + 1))

theorem polyGenMuG_succ {k : Nat} (hk : 1 ≤ k) :
    polyGenMuG (k + 1) = envStepG (k + 1) (genMu0 (k + 1)) (genMuK (k + 1)) (polyGenMuG k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rfl

/-- **Graded polynomial discrepancy bounds in every degree `k + 2 ≥ 4`**, from
the recurrence profiles and a phase partition. -/
theorem polyEnvBound_allG (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {Kφ : Real} {pφ : Nat} (hpp : ProgressionPhasePartition Kφ pφ) (hpφ : 0 < pφ)
    (hKφ : Kφ ≤ 2 ^ pφ) (hpφB : (pφ : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64)) :
    ∀ k, 2 ≤ k → k + 1 ≤ 2 ^ 68 → PolyEnvBound (k + 2) (polyGenMuG k) := by
  have hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))) :=
    fun k hk => abstractFamilyLemma166At_of k (hK k) (hp k) (hrec k hk)
  have hK1 : ∀ k, 1 ≤ Kc k := fun k => le_trans (by norm_num) (hK k)
  have hstep : ∀ k, 2 ≤ k → k + 1 ≤ 2 ^ 68 → ∀ μ, PolyEnvBound (k + 1) μ →
      PolyEnvBound (k + 2) (envStepG k (genMu0 k) (genMuK k) μ) := by
    intro k hk hk68 μ hlow
    obtain ⟨hV, hVμ, hμ0, -, -, hk0, hKk, hKμ, hpk, hpμ⟩ := stdHyp_of_profiles Kc pc hK hp hconst hk
    let P : GenParamsG := ⟨classV Kc pc k, k, Kc k, pc k, genMu0 k⟩
    have H : P.GHyp (genMuV k) (genMuK k) := ⟨hV, hVμ, hμ0, hk0, hk68, hKk, hKμ, hpk, hpμ⟩
    have hcov : ∀ l, 1 ≤ l → l ≤ P.k →
        PolyCoverAt l (uCount P.V (uDeg68 l)) (uExp P.V (uDeg68 l)) := by
      intro l hl1 hlk
      have hcl := polyCoverAt_class68 Kc pc hK1 hp hlem hl1
      exact hcl.uniform_mono (one_le_classV Kc pc l) (classV_mono Kc pc hlk) le_rfl
    exact polyEnvBound_stepG P H (by show 1 ≤ k; omega) hcov (hrec k (by omega)) hlow
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro hk68
    exact hstep 2 le_rfl hk68 74 (polyEnvBound_three_of_phase_partition hpp hpφ hKφ hpφB)
  | succ k hk ih =>
    intro hk68
    rw [polyGenMuG_succ (by omega)]
    exact hstep (k + 1) (by omega) hk68 (polyGenMuG k) (ih (by omega))

/-- The graded envelopes at degrees `4, …, 9` fit `2^(d+10)`. -/
theorem polyGenMuG_fits :
    polyGenMuG 2 + 1 ≤ 2 ^ (4 + 10) ∧ polyGenMuG 3 + 1 ≤ 2 ^ (5 + 10) ∧
      polyGenMuG 4 + 1 ≤ 2 ^ (6 + 10) ∧ polyGenMuG 5 + 1 ≤ 2 ^ (7 + 10) ∧
      polyGenMuG 6 + 1 ≤ 2 ^ (8 + 10) ∧ polyGenMuG 7 + 1 ≤ 2 ^ (9 + 10) := by
  decide

/-- **Theorem 18.1 at degrees four to nine**, from the recurrence profiles
and a phase partition. -/
theorem theorem_18_1_four_to_nine_of_profiles (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {Kφ : Real} {pφ : Nat} (hpp : ProgressionPhasePartition Kφ pφ) (hpφ : 0 < pφ)
    (hKφ : Kφ ≤ 2 ^ pφ) (hpφB : (pφ : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64))
    {d : Nat} (hd4 : 4 ≤ d) (hd9 : d ≤ 9) : Theorem181At d := by
  have henv := polyEnvBound_allG Kc pc hK hp hrec hconst hpp hpφ hKφ hpφB (d - 2) (by omega)
    (by omega)
  rw [show d - 2 + 2 = d by omega] at henv
  have hfit := polyGenMuG_fits
  interval_cases d
  · exact theorem181At_of_polyEnvBound henv hfit.1
  · exact theorem181At_of_polyEnvBound henv hfit.2.1
  · exact theorem181At_of_polyEnvBound henv hfit.2.2.1
  · exact theorem181At_of_polyEnvBound henv hfit.2.2.2.1
  · exact theorem181At_of_polyEnvBound henv hfit.2.2.2.2.1
  · exact theorem181At_of_polyEnvBound henv hfit.2.2.2.2.2

end LeanProofs.GowersSzemeredi
