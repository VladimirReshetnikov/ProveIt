import GowersSzemeredi.Proofs18EnvelopeBounds
import GowersSzemeredi.Proofs18GenericThresholds

/-! Discrepancy bounds in every degree, with power-of-two envelopes
(Notes L.7a, F3d).

`EnvBound d μ`: for every `α ∈ (0, 1/2]` there is a degree-`d` discrepancy
bound `FunctionDiscrepancyBound d α β σ T` with
`β⁻¹ ≤ X^(2^μ)`, `σ⁻¹ ≤ exp(X^(2^μ))` and `T ≤ exp(exp(X^(2^μ)))`, `X = 2/α`.
* `envBound_three`: degree three at `μ = 62`, from the Fejér cubic bound.
* `envBound_step`: the single-piece step in dimension `k` takes
  `EnvBound (k+1) μ` to `EnvBound (k+2) (envStep k μD μ₀ μK μ)`, given
  uniform covers in dimensions `≤ k` and the recurrence profile in
  dimension `k`.
* The fixed constants: `polyPartConst_le`, `s5_one_le`.

The step costs `envStep − μ ≈ densDeg k μD μ₀`, dominated by the nest:
`(μD + 1)·(2^k − 1)` (Notes L.7a). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- **The phase-refinement threshold.** -/
theorem inv_thr_le {X : Real} (hX : 2 ≤ X) {k : Nat} {η β e σ : Real} {M s : Nat}
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hηi : η⁻¹ ≤ X ^ (2 ^ M)) (hβi : β⁻¹ ≤ X ^ (2 ^ M)) (hs0 : 0 < σ) (hs16 : σ ≤ 16)
    (hσ'0 : 0 < inverseStepExponent (k + 1) e σ)
    (hσ' : (inverseStepExponent (k + 1) e σ)⁻¹ ≤ Real.exp (X ^ (2 ^ s))) :
    inverseStepThreshold (k + 1) η β e (6 * ((k + 1 : Nat) : Real)) σ ≤
      Real.exp (Real.exp (X ^ (2 ^ (max (max (40 * (k + 2) ^ 3 + 1090)
        (M + 4 * (k + 3) ^ 2 + 10)) s + 1)))) := by
  set Q := max (40 * (k + 2) ^ 3 + 1090) (M + 4 * (k + 3) ^ 2 + 10) with hQdef
  -- the refinement constant at `b = ηβ/2`
  have hb : 0 < η * β / 2 := by positivity
  have hbi : (η * β / 2)⁻¹ ≤ X ^ (2 ^ (M + 2)) := by
    rw [show (η * β / 2)⁻¹ = 2 * (η⁻¹ * β⁻¹) by field_simp]
    have h1 := pw_mul hX (inv_pos.mpr hβ0).le hηi hβi
    exact pw_mul' hX (by positivity) (hX.trans (pw_X hX M)) h1 |>.trans
      (pw_mono hX le_rfl (by omega))
  have hb1 : 1 ≤ (η * β / 2)⁻¹ := by
    rw [one_le_inv₀ hb]
    have : η * β ≤ 1 := mul_le_one₀ hη1 hβ0.le hβ1
    linarith
  have hscaled := section5LocalRefinementConstant_le_scaled (k + 1 + 1) (η * β / 2)
    (η * β / 2)⁻¹ hb hb1 le_rfl
  have hs5 : section5LocalRefinementConstant (k + 1 + 1) 1 ≤ X ^ (2 ^ (40 * (k + 1 + 1) ^ 3 + 2)) :=
    (s5_one_le (d := k + 1 + 1) (by omega)).trans (pow_le_pow_left₀ (by norm_num) hX _)
  have hpow : ((η * β / 2)⁻¹) ^ polynomialPartitionConstant (k + 1 + 1) ≤
      X ^ (2 ^ (M + 2 + 4 * (k + 1 + 1 + 1) ^ 2)) :=
    pw_pow hX (inv_pos.mpr hb).le hbi (polyPartConst_le (k + 1 + 1))
  have hR : section5LocalRefinementConstant (k + 1 + 1) (η * β / 2) ≤ X ^ (2 ^ (Q - 1)) := by
    refine hscaled.trans ?_
    have := pw_mul' hX
      (pow_nonneg (inv_pos.mpr hb).le _) hs5 hpow
    refine this.trans (pw_natpow hX (Nat.pow_le_pow_right (by norm_num) ?_))
    have e1 : k + 1 + 1 = k + 2 := by ring
    have e2 : k + 1 + 1 + 1 = k + 3 := by ring
    rw [e1, e2]
    rw [hQdef]
    omega
  -- the count constant
  have hσ16 : σ / 16 ≤ 1 := by linarith
  have hσ16' : 0 ≤ σ / 16 := by positivity
  have hr1 : (1 : Real) ≤ 2 * ((k + 1 + 2 : Nat) : Real) := by push_cast; linarith
  have hc1 : (1 : Real) ≤ 6 * ((k + 1 : Nat) : Real) := by push_cast; linarith
  have hrpow : (2 * ((k + 1 + 2 : Nat) : Real)) ^ (1 - σ / 16) ≤ 2 * ((k + 1 + 2 : Nat) : Real) := by
    calc (2 * ((k + 1 + 2 : Nat) : Real)) ^ (1 - σ / 16) ≤
          (2 * ((k + 1 + 2 : Nat) : Real)) ^ (1 : Real) :=
          Real.rpow_le_rpow_of_exponent_le hr1 (by linarith)
      _ = _ := Real.rpow_one _
  have hcpow : (6 * ((k + 1 : Nat) : Real)) ^ (σ / 16) ≤ 6 * ((k + 1 : Nat) : Real) := by
    calc (6 * ((k + 1 : Nat) : Real)) ^ (σ / 16) ≤ (6 * ((k + 1 : Nat) : Real)) ^ (1 : Real) :=
          Real.rpow_le_rpow_of_exponent_le hc1 hσ16
      _ = _ := Real.rpow_one _
  have hB0 : 0 ≤ boundaryRefinementConstant (1 / 16) := (section5LocalRefinementConstant_pos _ _).le
  have hr : 2 * ((k + 1 + 2 : Nat) : Real) ≤ X ^ (2 ^ (k + 3)) := by
    have := small_nat_le_pw hX (k := k) (c := 2 * (k + 1 + 2)) (by omega)
    push_cast at this ⊢; linarith
  have hc : 6 * ((k + 1 : Nat) : Real) ≤ X ^ (2 ^ (k + 3)) := by
    have := small_nat_le_pw hX (k := k) (c := 6 * (k + 1)) (by omega)
    push_cast at this ⊢; linarith
  have h2B : 2 * boundaryRefinementConstant (1 / 16) ≤ X ^ (2 ^ (1083 + 1)) :=
    pw_mul hX hB0 (hX.trans (pw_X hX _)) (pw_const hX cubic_boundary_refinement_constant_upper)
  have hD : inverseStepCountConstant (k + 1) (6 * ((k + 1 : Nat) : Real)) σ ≤
      X ^ (2 ^ (max (1083 + 1) (k + 3) + 1 + 1 + 1)) := by
    unfold inverseStepCountConstant localInverseAssemblyConstant
    have hmax : max 1 (2 * boundaryRefinementConstant (1 / 16) *
        (2 * ((k + 1 + 2 : Nat) : Real)) ^ (1 - σ / 16)) ≤
        X ^ (2 ^ (max (1083 + 1) (k + 3) + 1)) :=
      max_le (one_le_pw hX _) (pw_mul' hX
        (Real.rpow_nonneg (by linarith) _) h2B (hrpow.trans hr))
    have := pw_mul' hX (Real.rpow_nonneg (by linarith) _) hmax
      (hcpow.trans hc)
    exact this.trans (pw_mono hX le_rfl (by omega))
  have hD1 : 1 ≤ inverseStepCountConstant (k + 1) (6 * ((k + 1 : Nat) : Real)) σ := by
    unfold inverseStepCountConstant localInverseAssemblyConstant
    exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) (Real.one_le_rpow hc1 hσ16')
  have hP1 : (1 : Real) ≤ polynomialPartitionConstant (k + 1 + 1) := by
    exact_mod_cast polyPartConst_pos (k + 1 + 1)
  have hDp : (inverseStepCountConstant (k + 1) (6 * ((k + 1 : Nat) : Real)) σ) ^
      ((polynomialPartitionConstant (k + 1 + 1) : Real))⁻¹ ≤
      inverseStepCountConstant (k + 1) (6 * ((k + 1 : Nat) : Real)) σ := by
    calc _ ≤ (inverseStepCountConstant (k + 1) (6 * ((k + 1 : Nat) : Real)) σ) ^ (1 : Real) :=
          Real.rpow_le_rpow_of_exponent_le hD1 (inv_le_one_of_one_le₀ hP1)
      _ = _ := Real.rpow_one _
  have hPIC : phaseInverseConstant (k + 1 + 1) (η * β / 2)
      (inverseStepCountConstant (k + 1) (6 * ((k + 1 : Nat) : Real)) σ) ≤ X ^ (2 ^ Q) := by
    unfold phaseInverseConstant
    have := pw_mul' hX (Real.rpow_nonneg (le_trans zero_le_one hD1) _) hR (hDp.trans hD)
    refine this.trans (pw_mono hX le_rfl ?_)
    have hk3 : k + 2 ≤ (k + 2) ^ 3 := Nat.le_self_pow (by norm_num) _
    rw [hQdef]; omega
  unfold inverseStepThreshold
  have hppt := positivePowerThreshold_one_le_double_exp hσ'0.le
    (le_exp_exp_of_le_exp (ex_of_pw hPIC)) hσ'
  refine hppt.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr ?_))
  exact pw_add hX (pw_mono hX le_rfl (le_max_left Q s)) (pw_mono hX le_rfl (le_max_right Q s))

/-! ### The step -/

/-- The log-degree after one step. -/
def envStep (k μD μ0 μK μ : Nat) : Nat :=
  max (GenParams.densDeg k μD μ0 + μ + 4 * (k + 3) ^ 2 + 14)
    (max (GenParams.threshDeg k μD μ0 μK + 3) (40 * (k + 2) ^ 3 + 1095))

/-- **The single-piece step in dimension `k`, with envelopes.** -/
theorem envBound_step {V : Real} {D k K p μV μD μ0 μK μ : Nat}
    (H : GenParams.StdHyp V D k K p μV μD μ0 μK) (hk : 1 ≤ k) (hcov : UniformCovers k V D)
    (hrec : Section16RecurrenceProfileWith k (familyRecThr k K p) (familyRecExp k p))
    (hlow : EnvBound (k + 1) μ) : EnvBound (k + 2) (envStep k μD μ0 μK μ) := by
  intro alpha ha ha2
  obtain ⟨hV, hVμ, hμ0, hD, hkD, hk0, hK, hKμ, hp, hpμ⟩ := H
  have hX := two_div_ge_two ha ha2
  set E := GenParams.expDeg k μD μ0 μK with hEdef
  set Th := GenParams.threshDeg k μD μ0 μK with hThdef
  set dd := GenParams.densDeg k μD μ0 with hdddef
  set M1 := dd + 1 + μ with hM1def
  have hETh : E + 4 ≤ Th := by rw [hThdef]; unfold GenParams.threshDeg; exact le_max_left _ _
  have hk3 : k + 2 ≤ (k + 2) ^ 3 := Nat.le_self_pow (by norm_num) _
  -- the input parameter and the lower-degree bound
  obtain ⟨he0, he8, hei, hy0, hyle, hyi⟩ :=
    GenParams.yIn_bounds (K := K) (p := p) ha ha2 hV hVμ hμ0 hD hkD hk0
  have hy2 : (GenParams.std V D k K p μ0).yIn alpha ≤ 1 / 2 := hyle.trans ha2
  obtain ⟨β, σ, T, hB, b0, b1, s0, s16, bi, si, Ti⟩ := hlow _ hy0 hy2
  obtain ⟨-, hYμ⟩ := input_scale_le (μ := μ) ha ha2 hy0 hyi
  have bi' : β⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) := bi.trans hYμ
  have si' : σ⁻¹ ≤ Real.exp ((2 / alpha) ^ (2 ^ M1)) := si.trans (Real.exp_le_exp.mpr hYμ)
  have Ti' : T ≤ Real.exp (Real.exp ((2 / alpha) ^ (2 ^ M1))) :=
    Ti.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hYμ))
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
      Real.exp ((2 / alpha) ^ (2 ^ S)) := by
    rw [σeq]
    have h1 := pw_mul' hX (inv_pos.mpr hEl0).le h32P hEli
    exact ex_mul' hX (inv_pos.mpr s0).le (ex_of_pw h1) si'
  -- the thresholds
  have hTl := GenParams.Tloc_le_exp ⟨hV, hVμ, hμ0, hD, hkD, hk0, hK, hKμ, hp, hpμ⟩ hk ha ha2
  have hshort := short_thr_step_le hX (k := k) hEl0 hEli Ti' hTl
  have hinv := inv_thr_le hX (k := k) he0 heta1 b0 b1 hei' bi' s0 s16 σ0' hσ'
  -- assemble
  refine ⟨(GenParams.std V D k K p μ0).eta alpha * β / 4, _, _, hstep,
    div_pos (mul_pos he0 b0) (by norm_num), ?_, σ0', σ16',
    ?_, ex_mono hX hσ' ?_, ?_⟩
  · have : (GenParams.std V D k K p μ0).eta alpha * β ≤ 1 := mul_le_one₀ heta1 b0.le b1
    linarith
  · refine pw_mono hX (inv_mul_div_four_le_pw hX he0 b0 hei' bi') ?_
    unfold envStep; rw [← hdddef]; omega
  · unfold envStep; rw [← hdddef, ← hThdef]; omega
  · refine max_le (dex_mono hX hshort ?_) (dex_mono hX hinv ?_)
    · unfold envStep; rw [← hdddef, ← hThdef]; omega
    · unfold envStep; rw [← hdddef, ← hThdef]; omega

end LeanProofs.GowersSzemeredi
