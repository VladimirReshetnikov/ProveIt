import GowersSzemeredi.Proofs18PolyCubicDegree
import GowersSzemeredi.Proofs18GenericLengths

/-! **Theorem 18.1 at degrees four to seven**, from the recurrence profiles
and a polynomial phase partition (Notes L.9a).

Theorem 18.1 needs `β, σ ≥ α^(2^(2^(k+10)))` with an existential threshold.
`PolyEnvBound d μ` is `EnvBound d μ` with two changes:
* `σ⁻¹ ≤ (2/α)^(2^μ)`, polynomial instead of `exp((2/α)^(2^μ))`;
* no threshold envelope.

The single-piece step keeps it polynomial. Its exponent update is
`σ′⁻¹ = 32P·E_loc⁻¹·σ⁻¹`, and `E_loc⁻¹` is already a power of `2/α`. So
`polyEnvBound_step` is `envBound_step` with the `σ` bound read in
`X`-powers. It has the same new envelope `envStep k μD μ₀ μK μ`.

The base is degree three at `μ = 74` (`polyEnvBound_three_of_phase_partition`).
`polyGenMu` runs the steps in dimensions `2, …, k`. Evaluation shows
`polyGenMu (d−2) + 1 ≤ 2^(d+10)` for `d = 4, …, 7`. Degree eight does not
fit (Notes L.7c). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- **The single-piece step with polynomial envelopes.** -/
theorem polyEnvBound_step {V : Real} {D k K p μV μD μ0 μK μ : Nat}
    (H : GenParams.StdHyp V D k K p μV μD μ0 μK) (hk : 1 ≤ k) (hcov : UniformCovers k V D)
    (hrec : Section16RecurrenceProfileWith k (familyRecThr k K p) (familyRecExp k p))
    (hlow : PolyEnvBound (k + 1) μ) : PolyEnvBound (k + 2) (envStep k μD μ0 μK μ) := by
  intro alpha ha ha2
  obtain ⟨hV, hVμ, hμ0, hD, hkD, hk0, hK, hKμ, hp, hpμ⟩ := H
  have hX := two_div_ge_two ha ha2
  set E := GenParams.expDeg k μD μ0 μK with hEdef
  set Th := GenParams.threshDeg k μD μ0 μK with hThdef
  set dd := GenParams.densDeg k μD μ0 with hdddef
  set M1 := dd + 1 + μ with hM1def
  have hETh : E + 4 ≤ Th := by rw [hThdef]; unfold GenParams.threshDeg; exact le_max_left _ _
  -- the input parameter and the lower-degree bound
  obtain ⟨he0, he8, hei, hy0, hyle, hyi⟩ :=
    GenParams.yIn_bounds (K := K) (p := p) ha ha2 hV hVμ hμ0 hD hkD hk0
  have hy2 : (GenParams.std V D k K p μ0).yIn alpha ≤ 1 / 2 := hyle.trans ha2
  obtain ⟨β, σ, T, hB, b0, b1, s0, s16, bi, si⟩ := hlow _ hy0 hy2
  obtain ⟨-, hYμ⟩ := input_scale_le (μ := μ) ha ha2 hy0 hyi
  have bi' : β⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) := bi.trans hYμ
  have si' : σ⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) := si.trans hYμ
  have hei' : ((GenParams.std V D k K p μ0).eta alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) :=
    pw_mono hX hei (by rw [hM1def, hdddef]; unfold GenParams.densDeg; omega)
  have heta1 : (GenParams.std V D k K p μ0).eta alpha ≤ 1 := by linarith
  -- the step
  have hstep := (GenParams.std V D k K p μ0).inverse_step hV hK hp hk hcov hrec ha ha2
    (GenParams.std_lift ha ha2 hV hVμ hμ0) hB b0 s0 s16
  -- the localization exponent and `σ′`
  obtain ⟨hEl0, hEli⟩ := GenParams.Eloc_inv_le (K := K) ha ha2 hV hVμ hμ0 hD hkD hk0 hp hpμ
  obtain ⟨-, hEl2, -⟩ := (GenParams.std V D k K p μ0).Eloc_pos_le hV hp ha ha2
  obtain ⟨σ0', σ16', σeq⟩ := sigma_step (d := k + 1) hEl0 hEl2 s0 s16
  have h32P := polyPartConst_mul32_le_pw hX k
  set S := max (max (4 * (k + 3) ^ 2 + 4) (E + 3) + 1) M1 + 1 with hSdef
  have hσ' : (inverseStepExponent (k + 1) ((GenParams.std V D k K p μ0).Eloc alpha) σ)⁻¹ ≤
      (2 / alpha) ^ (2 ^ S) := by
    rw [σeq]
    have hx0 : 0 ≤ 32 * (polynomialPartitionConstant (k + 1 + 1) : Real) *
        ((GenParams.std V D k K p μ0).Eloc alpha)⁻¹ :=
      mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (inv_pos.mpr hEl0).le
    have h1 := pw_mul' hX (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (inv_pos.mpr hEl0).le h32P hEli
    exact pw_mul' hX hx0 (inv_pos.mpr s0).le h1 si'
  -- assemble
  refine ⟨(GenParams.std V D k K p μ0).eta alpha * β / 4, _, _, hstep,
    div_pos (mul_pos he0 b0) (by norm_num), ?_, σ0', σ16', ?_, pw_mono hX hσ' ?_⟩
  · have : (GenParams.std V D k K p μ0).eta alpha * β ≤ 1 := mul_le_one₀ heta1 b0.le b1
    linarith
  · refine pw_mono hX (inv_mul_div_four_le_pw hX he0 b0 hei' bi') ?_
    unfold envStep; rw [← hdddef]; omega
  · unfold envStep; rw [← hdddef, ← hThdef]; omega

/-- The polynomial envelope of the degree-`(k+2)` bound after the steps in
dimensions `2, …, k`. -/
def polyGenMu : Nat → Nat
  | 0 => 74
  | 1 => 74
  | k + 2 => envStep (k + 2) (genMuD (k + 2)) (genMu0 (k + 2)) (genMuK (k + 2)) (polyGenMu (k + 1))

theorem polyGenMu_succ {k : Nat} (hk : 1 ≤ k) :
    polyGenMu (k + 1) =
      envStep (k + 1) (genMuD (k + 1)) (genMu0 (k + 1)) (genMuK (k + 1)) (polyGenMu k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rfl

/-- **Polynomial discrepancy bounds in every degree `k + 2 ≥ 4`**, from the
recurrence profiles and a phase partition. -/
theorem polyEnvBound_all (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {Kφ : Real} {pφ : Nat} (hpp : ProgressionPhasePartition Kφ pφ) (hpφ : 0 < pφ)
    (hKφ : Kφ ≤ 2 ^ pφ) (hpφB : (pφ : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64)) :
    ∀ k, 2 ≤ k → PolyEnvBound (k + 2) (polyGenMu k) := by
  have hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))) :=
    fun k hk => abstractFamilyLemma166At_of k (hK k) (hp k) (hrec k hk)
  have hK1 : ∀ k, 1 ≤ Kc k := fun k => le_trans (by norm_num) (hK k)
  have hstep : ∀ k, 2 ≤ k → ∀ μ, PolyEnvBound (k + 1) μ →
      PolyEnvBound (k + 2) (envStep k (genMuD k) (genMu0 k) (genMuK k) μ) := by
    intro k hk μ hlow
    exact polyEnvBound_step (stdHyp_of_profiles Kc pc hK hp hconst hk) (by omega)
      (uniformCovers_of_classes Kc pc hK1 hp hlem k) (hrec k (by omega)) hlow
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact hstep 2 le_rfl 74 (polyEnvBound_three_of_phase_partition hpp hpφ hKφ hpφB)
  | succ k hk ih =>
    rw [polyGenMu_succ (by omega)]
    exact hstep (k + 1) (by omega) (polyGenMu k) ih

/-- The polynomial envelopes at degrees `4, …, 7` fit `2^(d+10)`. -/
theorem polyGenMu_fits :
    polyGenMu 2 + 1 ≤ 2 ^ (4 + 10) ∧ polyGenMu 3 + 1 ≤ 2 ^ (5 + 10) ∧
      polyGenMu 4 + 1 ≤ 2 ^ (6 + 10) ∧ polyGenMu 5 + 1 ≤ 2 ^ (7 + 10) := by
  decide

/-- **Theorem 18.1 at degrees four to seven**, from the recurrence profiles
and a phase partition. -/
theorem theorem_18_1_four_to_seven_of_profiles (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {Kφ : Real} {pφ : Nat} (hpp : ProgressionPhasePartition Kφ pφ) (hpφ : 0 < pφ)
    (hKφ : Kφ ≤ 2 ^ pφ) (hpφB : (pφ : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64))
    {d : Nat} (hd4 : 4 ≤ d) (hd7 : d ≤ 7) : Theorem181At d := by
  have henv := polyEnvBound_all Kc pc hK hp hrec hconst hpp hpφ hKφ hpφB (d - 2) (by omega)
  rw [show d - 2 + 2 = d by omega] at henv
  have hfit := polyGenMu_fits
  interval_cases d
  · exact theorem181At_of_polyEnvBound henv hfit.1
  · exact theorem181At_of_polyEnvBound henv hfit.2.1
  · exact theorem181At_of_polyEnvBound henv hfit.2.2.1
  · exact theorem181At_of_polyEnvBound henv hfit.2.2.2

end LeanProofs.GowersSzemeredi
