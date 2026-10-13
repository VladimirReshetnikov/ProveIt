import GowersSzemeredi.Proofs18FinalStep

/-! **The final route, part 3: the envelopes and their fits** (Notes L.16-final).

One step for each theorem over the single class table `tDegT3`:
* Theorem 18.1: `envStepJT3` and the envelope `polyGenMuJT3` (joint slices);
* Theorem 18.2: `envStepKTx3` and the envelope `genMuXK3` (joint slices,
  sharp partition constant).
Beyond dimension `14` the closed forms bound both envelopes by `16·2^k - 4k - 128`;
`decide +kernel` evaluates them below. Fits:
* `polyGenMuJT3 k + 1 ≤ 16·2^k, 32·2^k, 64·2^k` from `k = 9, 6, 2`;
* `genMuXK3 k + 2k + 22 ≤ 16·2^k, 32·2^k, 64·2^k, 128·2^k` from `k = 9, 7, 4, 2`.
With them, Theorem 16.2 and Corollary 16.11 with polynomial controls at
`tDegT3`. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

/-- The polynomial base budget. -/
def tightMu0Z (k : Nat) : Nat := max (tightMuW k) (pDeg k) + 2

/-- The polynomial bound on the family constants: `K, p ≤ 2^(2^(4k+16))`. -/
def genMuKZ (k : Nat) : Nat := 4 * k + 16

/-- `32(k+5)² ≤ 2^k` for `k ≥ 14`. -/
theorem thirtytwo_sq_le_two_pow_fourteen : ∀ k, 14 ≤ k → 32 * (k + 5) ^ 2 ≤ 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hstep : (k + 1 + 5) ^ 2 ≤ 2 * (k + 5) ^ 2 := by nlinarith
    calc 32 * (k + 1 + 5) ^ 2 ≤ 2 * (32 * (k + 5) ^ 2) := by omega
      _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left _ ih
      _ = 2 ^ (k + 1) := by rw [pow_succ]; ring

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

/-- The partition constant fits `2^(2^(k+9))`: `4(k+3)² + 5 ≤ 2^(k+9)`. -/
theorem four_sq_add_five_le (k : Nat) : 4 * (k + 3) ^ 2 + 5 ≤ 2 ^ (k + 9) := by
  rcases Nat.lt_or_ge k 4 with h | h
  · interval_cases k <;> norm_num
  · have h1 := sq_le_two_pow_four k h
    have h2 : (k + 3) ^ 2 ≤ (k + 4) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h9 : 2 ^ (k + 9) = 512 * 2 ^ k := by rw [pow_add]; ring
    have h3 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

/-- `(n+1)² ≤ 4^n` for `n ≥ 1`. -/
theorem succ_sq_le_four_pow : ∀ n, 1 ≤ n → (n + 1) ^ 2 ≤ 4 ^ n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    calc (n + 1 + 1) ^ 2 ≤ (2 * (n + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = 4 * (n + 1) ^ 2 := by ring
      _ ≤ 4 * 4 ^ n := Nat.mul_le_mul_left 4 ih
      _ = 4 ^ (n + 1) := by ring

/-- `(d!)² · 2^d ≤ 2^(d²)`. -/
theorem factorial_sq_mul_two_pow_le : ∀ d : Nat, d.factorial ^ 2 * 2 ^ d ≤ 2 ^ (d * d)
  | 0 => by norm_num
  | n + 1 => by
    have ih := factorial_sq_mul_two_pow_le n
    have h4 : (n + 1) ^ 2 * 2 ≤ 2 ^ (2 * n + 1) := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; norm_num
      · have h1 := succ_sq_le_four_pow n h
        have e : 2 ^ (2 * n + 1) = 4 ^ n * 2 := by
          rw [pow_succ, pow_mul]; norm_num
        rw [e]; omega
    have e1 : (n + 1).factorial ^ 2 * 2 ^ (n + 1) =
        (n.factorial ^ 2 * 2 ^ n) * ((n + 1) ^ 2 * 2) := by
      rw [Nat.factorial_succ]; ring
    have e2 : 2 ^ ((n + 1) * (n + 1)) = 2 ^ (n * n) * 2 ^ (2 * n + 1) := by
      rw [← pow_add]; congr 1 <;> ring
    rw [e1, e2]
    exact Nat.mul_le_mul ih h4

/-- The log-degree of the partition constant of the step: `(k+3)² + (k+2)(k+1)`. -/
def partDeg (k : Nat) : Nat := (k + 3) ^ 2 + (k + 2) * (k + 1)

/-- **The polynomial partition constant, sharply**: `(d!)²·2^((d+1)²) ≤ 2^((d+1)² + d(d-1))`
at `d = k + 2` (`polyPartConst_le` charges `2^(4(d+1)²)`). -/
theorem polyPartConst_le_sharp (k : Nat) :
    polynomialPartitionConstant (k + 1 + 1) ≤ 2 ^ partDeg k := by
  unfold polynomialPartitionConstant partDeg
  have h := factorial_sq_mul_two_pow_le (k + 1 + 1)
  have e : 2 ^ ((k + 1 + 1) * (k + 1 + 1)) = 2 ^ ((k + 2) * (k + 1)) * 2 ^ (k + 1 + 1) := by
    rw [← pow_add]; congr 1 <;> ring
  rw [e] at h
  have h' : (k + 1 + 1).factorial ^ 2 ≤ 2 ^ ((k + 2) * (k + 1)) :=
    Nat.le_of_mul_le_mul_right h (by positivity)
  calc (k + 1 + 1).factorial ^ 2 * 2 ^ ((k + 1 + 1 + 1) ^ 2)
      ≤ 2 ^ ((k + 2) * (k + 1)) * 2 ^ ((k + 1 + 1 + 1) ^ 2) := Nat.mul_le_mul_right _ h'
    _ = 2 ^ ((k + 3) ^ 2 + (k + 2) * (k + 1)) := by rw [← pow_add]; congr 1 <;> ring

/-- **The phase-refinement threshold, with the constants at the exponential
level**, with the partition constant at `2^partDeg k`. -/
theorem inv_thr_le_ex_sharp {X : Real} (hX : 2 ≤ X) {k : Nat} {η β e σ : Real} {M s : Nat}
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hηi : η⁻¹ ≤ X ^ (2 ^ M)) (hβi : β⁻¹ ≤ X ^ (2 ^ M)) (hs0 : 0 < σ) (hs16 : σ ≤ 16)
    (hσ'0 : 0 < inverseStepExponent (k + 1) e σ)
    (hσ' : (inverseStepExponent (k + 1) e σ)⁻¹ ≤ Real.exp (X ^ (2 ^ s))) :
    inverseStepThreshold (k + 1) η β e (6 * ((k + 1 : Nat) : Real)) σ ≤
      Real.exp (Real.exp (X ^ (2 ^ (max (max (M + partDeg k + 4) (k + 16)) s + 1)))) := by
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
      X ^ (2 ^ (M + 2 + partDeg k)) :=
    pw_pow hX (inv_pos.mpr hb).le hbi (polyPartConst_le_sharp k)
  have hR : section5LocalRefinementConstant (k + 1 + 1) (η * β / 2) ≤
      Real.exp (X ^ (2 ^ (max (k + 11) (M + 2 + partDeg k) + 1))) :=
    hscaled.trans (ex_mul' hX (pow_nonneg (inv_pos.mpr hb).le _) hs5 (ex_of_pw hpow))
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
      inverseStepCountConstant (k + 1) (6 * ((k + 1 : Nat) : Real)) σ := by
    calc _ ≤ (inverseStepCountConstant (k + 1) (6 * ((k + 1 : Nat) : Real)) σ) ^ (1 : Real) :=
          Real.rpow_le_rpow_of_exponent_le hD1 (inv_le_one_of_one_le₀ hP1)
      _ = _ := Real.rpow_one _
  have hPIC : phaseInverseConstant (k + 1 + 1) (η * β / 2)
      (inverseStepCountConstant (k + 1) (6 * ((k + 1 : Nat) : Real)) σ) ≤
      Real.exp (X ^ (2 ^ (max (max (M + partDeg k + 4) (k + 16)) s))) := by
    unfold phaseInverseConstant
    have := ex_mul' hX (Real.rpow_nonneg (le_trans zero_le_one hD1) _) hR (hDp.trans hD)
    exact ex_mono hX this (by omega)
  unfold inverseStepThreshold
  have hppt := positivePowerThreshold_one_le_double_exp hσ'0.le (le_exp_exp_of_le_exp hPIC) hσ'
  refine hppt.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr ?_))
  exact pw_add hX (pw_mono hX le_rfl le_rfl) (pw_mono hX le_rfl (le_max_right _ s))

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

/-- The standing hypotheses at the polynomial base budget. -/
theorem tightHyp_of_profiles_fejerJT3 (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ (4 * k + 16))) {k : Nat}
    (hk : 2 ≤ k) :
    (⟨classV Kc pc k, k, Kc k, pc k, tightMu0Z k⟩ : GenParamsJT3).CHyp (tightMuW k) (genMuKZ k) := by
  have hKr : (Kc k : Real) ≤ 2 ^ ((2 : Nat) ^ genMuKZ k) := by
    have := hconst k; unfold genMuKZ; linarith [Nat.cast_nonneg (α := Real) (pc k)]
  have hpr : (pc k : Real) ≤ 2 ^ ((2 : Nat) ^ genMuKZ k) := by
    have := hconst k; unfold genMuKZ; linarith [Nat.cast_nonneg (α := Real) (Kc k)]
  refine ⟨one_le_classV Kc pc k, classV_le_poly Kc pc hconst k, le_rfl, ?_, hK k, ?_, hp k, ?_⟩
  · show k ≤ 2 ^ tightMu0Z k
    calc k ≤ 2 ^ k := Nat.lt_two_pow_self.le
      _ ≤ 2 ^ tightMu0Z k := Nat.pow_le_pow_right (by norm_num) (by
          unfold tightMu0Z; have := five_k_le_pDeg k
          have := le_max_right (tightMuW k) (pDeg k); omega)
  · have : ((Kc k : Nat) : Real) ≤ ((2 ^ 2 ^ genMuKZ k : Nat) : Real) := by push_cast; exact hKr
    exact_mod_cast this
  · have : ((pc k : Nat) : Real) ≤ ((2 ^ 2 ^ genMuKZ k : Nat) : Real) := by push_cast; exact hpr
    exact_mod_cast this

/-- The envelope after one step, with the threshold, without the cubic branch. -/
def envStepKTx3 (k μ0 μK μ : Nat) : Nat :=
  max (GenParamsJT3.densDegJT3 k μ0 + μ + partDeg k + 14)
    (max (GenParamsJT3.threshDegJT3 k μ0 μK + 3) (k + 20))

/-- **The single-piece step, with envelopes and the sharper phase-refinement
threshold.** -/
theorem envBound_stepKx3 (P : GenParamsJT3) {μV μK μ : Nat} (H : P.CHyp μV μK) (hk : 1 ≤ P.k)
    (hcov : ∀ l, 1 ≤ l → l ≤ P.k → PolyCoverAt l (uCount P.V (uDegT3 l)) (uExp P.V (uDegT3 l)))
    (hrec : Section16RecurrenceProfileWith P.k (familyRecThr P.k P.K P.p) (familyRecExp P.k P.p))
    (hlow : EnvBound (P.k + 1) μ) : EnvBound (P.k + 2) (envStepKTx3 P.k P.μ0 μK μ) := by
  intro alpha ha ha2
  have hX := two_div_ge_two ha ha2
  -- everything that mentions `P.k`, before naming it
  obtain ⟨he0, he8, hei, hy0, hyle, hyi⟩ := P.yIn_boundsJT3 ha ha2 H.hV H.hVμ H.hμ0
  have hy2 : P.yIn alpha ≤ 1 / 2 := hyle.trans ha2
  obtain ⟨β, σ, T, hB, b0, b1, s0, s16, bi, si, Ti⟩ := hlow _ hy0 hy2
  have hstep := P.inverse_step H.hV H.hK H.hp hk hcov hrec ha ha2 hB b0 s0 s16
  obtain ⟨hEl0, hEli⟩ := P.Eloc_inv_leJT3 H ha ha2
  obtain ⟨-, hEl2, -⟩ := P.Eloc_pos_le H.hV H.hp ha ha2
  have hTl := P.Tloc_le_expJT3 H hk ha ha2
  set k := P.k with hkdef
  set E := GenParamsJT3.expDegJT3 k P.μ0 μK with hEdef
  set Th := GenParamsJT3.threshDegJT3 k P.μ0 μK with hThdef
  set dd := GenParamsJT3.densDegJT3 k P.μ0 with hdddef
  set M1 := dd + 1 + μ with hM1def
  have hETh : E + 4 ≤ Th := by rw [hThdef]; unfold GenParamsJT3.threshDegJT3; exact le_max_left _ _
  have hk3 : k + 2 ≤ (k + 2) ^ 3 := Nat.le_self_pow (by norm_num) _
  obtain ⟨-, hYμ⟩ := input_scale_le (μ := μ) ha ha2 hy0 hyi
  have bi' : β⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) := bi.trans hYμ
  have si' : σ⁻¹ ≤ Real.exp ((2 / alpha) ^ (2 ^ M1)) := si.trans (Real.exp_le_exp.mpr hYμ)
  have Ti' : T ≤ Real.exp (Real.exp ((2 / alpha) ^ (2 ^ M1))) :=
    Ti.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hYμ))
  have hei' : (P.eta alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) :=
    pw_mono hX hei (by rw [hM1def, hdddef]; unfold GenParamsJT3.densDegJT3; omega)
  have heta1 : P.eta alpha ≤ 1 := by linarith
  -- the localization exponent and `σ′`
  obtain ⟨σ0', σ16', σeq⟩ := sigma_step (d := k + 1) hEl0 hEl2 s0 s16
  have h32P : 32 * (polynomialPartitionConstant (k + 1 + 1) : Real) ≤
      (2 / alpha) ^ (2 ^ (partDeg k + 4)) := by
    refine pw_const hX ?_
    have hP := polyPartConst_le_sharp k
    have hn : partDeg k + 5 ≤ 2 ^ (partDeg k + 4) :=
      Nat.lt_two_pow_self (n := partDeg k + 4)
    have hnat : 32 * polynomialPartitionConstant (k + 1 + 1) ≤ 2 ^ (2 ^ (partDeg k + 4)) := by
      calc 32 * polynomialPartitionConstant (k + 1 + 1) ≤ 2 ^ 5 * 2 ^ (partDeg k) :=
            Nat.mul_le_mul (by norm_num) hP
        _ = 2 ^ (partDeg k + 5) := by rw [← pow_add]; ring_nf
        _ ≤ 2 ^ (2 ^ (partDeg k + 4)) := Nat.pow_le_pow_right (by norm_num) hn
    exact_mod_cast hnat
  set S := max (max (partDeg k + 4) (E + 3) + 1) M1 + 1 with hSdef
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
  have hinv := inv_thr_le_ex_sharp hX (k := k) he0 heta1 b0 b1 hei' bi' s0 s16 σ0' hσ'
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
    unfold envStepKTx3; rw [← hdddef]; omega
  · unfold envStepKTx3; rw [← hdddef, ← hThdef]; omega
  · refine max_le (dex_mono hX hshort ?_) (dex_mono hX hinv ?_)
    · unfold envStepKTx3; rw [← hdddef, ← hThdef]; omega
    · unfold envStepKTx3; rw [← hdddef, ← hThdef]; omega

/-- The Theorem 18.2 envelope at the tight base budget, without the cubic branch. -/
def genMuXK3 : Nat → Nat
  | 0 => 62
  | 1 => 62
  | k + 2 => envStepKTx3 (k + 2) (tightMu0Z (k + 2)) (genMuKZ (k + 2)) (genMuXK3 (k + 1))

theorem genMuXK3_succ {k : Nat} (hk : 1 ≤ k) :
    genMuXK3 (k + 1) = envStepKTx3 (k + 1) (tightMu0Z (k + 1)) (genMuKZ (k + 1)) (genMuXK3 k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rfl

theorem envBound_allXK3 (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ (4 * k + 16))) :
    ∀ k, 2 ≤ k → EnvBound (k + 2) (genMuXK3 k) := by
  have hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))) :=
    fun k hk => abstractFamilyLemma166At_of k (hK k) (hp k) (hrec k hk)
  have hK1 : ∀ k, 1 ≤ Kc k := fun k => le_trans (by norm_num) (hK k)
  have hstep : ∀ k, 2 ≤ k → ∀ μ, EnvBound (k + 1) μ →
      EnvBound (k + 2) (envStepKTx3 k (tightMu0Z k) (genMuKZ k) μ) := by
    intro k hk μ hlow
    let P : GenParamsJT3 := ⟨classV Kc pc k, k, Kc k, pc k, tightMu0Z k⟩
    have H : P.CHyp (tightMuW k) (genMuKZ k) := tightHyp_of_profiles_fejerJT3 Kc pc hK hp hconst hk
    have hcov : ∀ l, 1 ≤ l → l ≤ P.k →
        PolyCoverAt l (uCount P.V (uDegT3 l)) (uExp P.V (uDegT3 l)) := by
      intro l hl1 hlk
      have hcl := polyCoverAt_classT3 Kc pc hK1 hp hlem hl1
      exact hcl.uniform_mono (one_le_classV Kc pc l) (classV_mono Kc pc hlk) le_rfl
    exact envBound_stepKx3 P H (by show 1 ≤ k; omega) hcov (hrec k (by omega)) hlow
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact hstep 2 le_rfl 62 envBound_three
  | succ k hk ih =>
    rw [genMuXK3_succ (by omega)]
    exact hstep (k + 1) (by omega) (genMuXK3 k) ih

theorem envStepKTx3_le_tight {k : Nat} (hk : 15 ≤ k) (μ : Nat) :
    envStepKTx3 k (tightMu0Z k) (genMuKZ k) μ ≤
      μ + 10 * 2 ^ (k - 1) + 6 * (k + 4) ^ 2 + partDeg k + 6 * k + 59 := by
  unfold envStepKTx3 GenParamsJT3.densDegJT3 GenParamsJT3.threshDegJT3 GenParamsJT3.expDegJT3
    GenParamsJT3.rhoDegJT3 tightMu0Z tightMuW genMuKZ pDeg
  rw [tDegT3_eq_of_ge hk]
  have := Nat.lt_two_pow_self (n := k - 1)
  have hkq : k ≤ partDeg k := by unfold partDeg; nlinarith
  generalize partDeg k = q at hkq ⊢
  generalize (k + 4) ^ 2 = s
  generalize 2 ^ (k - 1) = y at *
  omega

theorem envStepKTx3_ge (k μ0 μK μ : Nat) : 5 * k + 33 ≤ envStepKTx3 k μ0 μK μ := by
  unfold envStepKTx3 GenParamsJT3.threshDegJT3
  omega

theorem genMuXK3_fifteen : genMuXK3 15 + 4 * 15 + 128 ≤ 16 * 2 ^ 15 := by decide +kernel

/-- **The Theorem 18.2 envelope with the sharp partition constant**:
`μ_k + 4k + 128 ≤ 16·2^k` for `k ≥ 15`. -/
theorem genMuXK3_le16 : ∀ k, 15 ≤ k → genMuXK3 k + 4 * k + 128 ≤ 16 * 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact genMuXK3_fifteen
  | succ k hk ih =>
    rw [genMuXK3_succ (by omega)]
    have h1 := envStepKTx3_le_tight (k := k + 1) (by omega) (genMuXK3 k)
    have h2 := thirtytwo_sq_le_two_pow_fourteen k (by omega)
    have h3 : partDeg (k + 1) ≤ 2 * (k + 5) ^ 2 := by unfold partDeg; nlinarith
    have h4 : 6 * k + 70 ≤ (k + 5) ^ 2 := by nlinarith
    rw [show k + 1 + 4 = k + 5 by ring, show k + 1 - 1 = k by omega] at h1
    rw [pow_succ]
    generalize partDeg (k + 1) = q at *
    generalize (k + 5) ^ 2 = s5 at *
    generalize 2 ^ k = x at *
    omega

theorem genMuXK3_ge {k : Nat} (hk : 2 ≤ k) : 5 * k + 33 ≤ genMuXK3 k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [genMuXK3_succ (by omega)]
  exact envStepKTx3_ge _ _ _ _

theorem genMuXK3_small16 {k : Nat} (h1 : 9 ≤ k) (h2 : k ≤ 14) :
    genMuXK3 k + 2 * k + 22 ≤ 16 * 2 ^ k := by
  interval_cases k <;> decide +kernel

theorem genMuXK3_fit16 {k : Nat} (hk : 9 ≤ k) : genMuXK3 k + 2 * k + 22 ≤ 16 * 2 ^ k := by
  rcases Nat.lt_or_ge k 15 with h | h
  · exact genMuXK3_small16 hk (by omega)
  · have := genMuXK3_le16 k h
    have h16 : 16 * 2 ^ k ≤ 16 * 2 ^ k := Nat.mul_le_mul_right _ (by norm_num)
    omega

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

theorem tightMuW_le_tightMuV (k : Nat) : tightMuW k ≤ tightMuV k := by
  unfold tightMuW tightMuV
  have h := Nat.lt_two_pow_self (n := k)
  have h16 : 2 ^ (k + 4) = 16 * 2 ^ k := by rw [pow_add]; ring
  omega

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

theorem singlePieceEtaFJ_le_density {Qb : Nat → Real → Real → Real → Real} {alpha : Real}
    {k : Nat} (ha : 0 < alpha) (ha1 : alpha ≤ 1) (hD : 0 ≤ singlePieceGlobalDensityFJ Qb alpha (alpha / 2) k) :
    singlePieceEtaFJ Qb alpha k ≤ singlePieceGlobalDensityFJ Qb alpha (alpha / 2) k := by
  unfold singlePieceEtaFJ
  set D := singlePieceGlobalDensityFJ Qb alpha (alpha / 2) k
  have h1 : (2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num) (neg_nonpos.mpr (by positivity))
  have h1' : (0 : Real) ≤ (2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)) := by positivity
  have h2 : (1 : Real) ≤ (2 : Real) ^ (k + 1) := one_le_pow₀ (by norm_num)
  have h3 : alpha ^ 2 / 4 ≤ 1 := by nlinarith
  have h4 : D / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4 ≤ D := by
    have h5 : D / (2 : Real) ^ (k + 1) ≤ D := div_le_self hD h2
    have h6 : 0 ≤ D / (2 : Real) ^ (k + 1) := by positivity
    calc D / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4 = D / (2 : Real) ^ (k + 1) * (alpha ^ 2 / 4) := by
          ring
      _ ≤ D / (2 : Real) ^ (k + 1) * 1 := mul_le_mul_of_nonneg_left h3 h6
      _ ≤ D := by rw [mul_one]; exact h5
  have h7 : 0 ≤ D / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4 := by positivity
  calc (2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)) * (D / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4)
      ≤ 1 * D := mul_le_mul h1 h4 h7 (by norm_num)
    _ = D := one_mul D

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

theorem uDegT3_le_uDeg68 {k : Nat} (hk : 1 ≤ k) : uDegT3 k ≤ uDeg68 k := by
  unfold uDegT3 uDeg68
  refine Nat.pow_le_pow_right (by norm_num) ?_
  rcases Nat.lt_or_ge k 15 with h | h
  · interval_cases k <;> decide
  · rw [tDegT3_eq_of_ge h]
    have h1 := sq_le_two_pow_four k (by omega)
    have h2 : 2 ^ k = 2 * 2 ^ (k - 1) := by
      rw [show k = (k - 1) + 1 by omega, pow_succ]; simp; ring
    have h3 : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
    omega

/-- The exponent degree of the joint-slice step at `(tDegT3, tightMu0Z)`: two
class degrees (`3·tDegT3` at the X step). -/
theorem expDegJT3_tight_le (k : Nat) :
    GenParamsJT3.expDegJT3 k (tightMu0Z k) (genMuKZ k) + 3 ≤ 2 * tDegT3 k + 7 * k + 38 := by
  unfold GenParamsJT3.expDegJT3 GenParamsJT3.rhoDegJT3 tightMu0Z tightMuW genMuKZ pDeg
  simp only [max_def]
  split_ifs <;> omega

/-- **Theorem 16.2 with polynomial controls in every dimension**, from the
recurrence profiles. -/
theorem theorem_16_2_polynomial_fejerT3_of_profiles (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ (4 * k + 16)))
    {k : Nat} (hk : 1 ≤ k) :
    PolyCoverAt k (uCount (2 ^ (2 ^ tightMuW k)) (uDegT3 k))
      (uExp (2 ^ (2 ^ tightMuW k)) (uDegT3 k)) := by
  have hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))) :=
    fun k hk => abstractFamilyLemma166At_of k (hK k) (hp k) (hrec k hk)
  have hK1 : ∀ k, 1 ≤ Kc k := fun k => le_trans (by norm_num) (hK k)
  exact (polyCoverAt_classT3 Kc pc hK1 hp hlem hk).uniform_mono (one_le_classV Kc pc k)
    (classV_le_poly Kc pc hconst k) le_rfl

/-- **Corollary 16.11 with polynomial exponents in dimension `k + 1`**, from
the recurrence profiles. -/
theorem corollary_16_11_polynomial_fejerJT3_of_profiles (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ (4 * k + 16)))
    {k : Nat} (hk : 2 ≤ k) :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 / 2 →
      ∃ e : Real, 0 < e ∧
        e⁻¹ ≤ (2 / alpha) ^ (2 ^ (GenParamsJT3.expDegJT3 k (tightMu0Z k) (genMuKZ k) + 3)) ∧
        ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
          ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha (k + 2) →
            ∃ P : Box N (k + 1), ∃ mu : Point N (k + 1) → ZMod N,
              IsMultilinear mu ∧ (N : Real) ^ e ≤ P.width ∧
              e * P.carrier.card ≤ section16LargeMultilinearFrequencyCount f P mu alpha := by
  intro alpha ha ha2
  have hX := two_div_ge_two ha ha2
  have hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))) :=
    fun k hk => abstractFamilyLemma166At_of k (hK k) (hp k) (hrec k hk)
  have hK1 : ∀ k, 1 ≤ Kc k := fun k => le_trans (by norm_num) (hK k)
  let P : GenParamsJT3 := ⟨classV Kc pc k, k, Kc k, pc k, tightMu0Z k⟩
  have H : P.CHyp (tightMuW k) (genMuKZ k) := tightHyp_of_profiles_fejerJT3 Kc pc hK hp hconst hk
  have hcov : ∀ l, 1 ≤ l → l ≤ P.k →
      PolyCoverAt l (uCount P.V (uDegT3 l)) (uExp P.V (uDegT3 l)) := by
    intro l hl1 hlk
    have hcl := polyCoverAt_classT3 Kc pc hK1 hp hlem hl1
    exact hcl.uniform_mono (one_le_classV Kc pc l) (classV_mono Kc pc hlk) le_rfl
  have hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ uCount P.V (uDegT3 l) g t s :=
    fun l g t s _ _ => one_le_uCount P.V (uDegT3 l) g t s
  have hretile : ∀ q, Section16RetiledLinearityBound P.k q (familyRecExp P.k P.p q)
      (familyRecThr P.k P.K P.p q) :=
    fun q => ((hrec k (by omega)).retiled_family
      (fun q => familyRecThr_pos (by have := hK k; omega) q) q).single
  -- the two exponents
  obtain ⟨hEl0, hEli⟩ := P.Eloc_inv_leJT3 H ha ha2
  obtain ⟨-, -, hei, -, -, -⟩ := P.yIn_boundsJT3 ha ha2 H.hV H.hVμ H.hμ0
  set D := singlePieceGlobalDensityFJ (fun l => uCount P.V (uDegT3 l)) alpha (alpha / 2) P.k with hDdef
  have hD0 : 0 < D := singlePieceGlobalDensityFJ_pos ha (by linarith) hQb
  have heta0 : 0 < P.eta alpha := by
    exact singlePieceEtaFJ_pos ha (by linarith) hQb
  have hetaD : P.eta alpha ≤ D := singlePieceEtaFJ_le_density ha (by linarith) hD0.le
  have hDi : D⁻¹ ≤ (2 / alpha) ^ (2 ^ (GenParamsJT3.expDegJT3 k (tightMu0Z k) (genMuKZ k) + 3)) := by
    refine (inv_anti₀ heta0 hetaD).trans (pw_mono hX hei ?_)
    show GenParamsJT3.rhoDegJT3 k (tightMu0Z k) + tDegT3 k + 10 ≤
      GenParamsJT3.expDegJT3 k (tightMu0Z k) (genMuKZ k) + 3
    unfold GenParamsJT3.expDegJT3
    have := le_max_left (GenParamsJT3.rhoDegJT3 k (tightMu0Z k) + tDegT3 k + 9)
      (max (GenParamsJT3.rhoDegJT3 k (tightMu0Z k) + tDegT3 k + k + 7) (genMuKZ k + 2))
    omega
  refine ⟨min (P.Eloc alpha) D, lt_min hEl0 hD0, ?_, ⌈P.Tloc alpha⌉₊, ?_⟩
  · rcases min_choice (P.Eloc alpha) D with h | h
    · rw [h]; exact hEli
    · rw [h]; exact hDi
  · intro N _ _ hN f hf hnot
    have hT : P.Tloc alpha ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
    obtain ⟨hodd, h15, -, m, hscale, hwide⟩ :=
      P.modulus_conditions H.hV H.hK H.hp ha ha2 N hT
    obtain ⟨q, hq, B, mu, -, hmu, hBw, hcount⟩ := single_piece_frequency_box_global_cover_fejer_joint
      (Qb := fun l => uCount P.V (uDegT3 l)) (Eb := fun l => uExp P.V (uDegT3 l))
      (by show 1 ≤ k; omega) ha ha2 hcov hQb
      (fun l g t s _ _ => (uExp_pos_le P.V (uDegT3 l) g t s).1)
      (fun l g t s _ _ => (uExp_pos_le P.V (uDegT3 l) g t s).2)
      (familyRecExp P.k P.p) (familyRecThr P.k P.K P.p) hretile hodd h15 m hscale f hf hnot
    have hN1 : (1 : Real) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    refine ⟨B, mu, hmu, ?_, ?_⟩
    · calc (N : Real) ^ min (P.Eloc alpha) D ≤ (N : Real) ^ P.Eloc alpha :=
            Real.rpow_le_rpow_of_exponent_le hN1 (min_le_left _ _)
        _ ≤ _ := hwide q hq
        _ ≤ B.width := by exact_mod_cast hBw
    · calc min (P.Eloc alpha) D * B.carrier.card ≤ D * B.carrier.card :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _)
        _ ≤ _ := hcount

/-- **The polynomial form at `uDegT3` implies the printed Theorem 16.2.** -/
theorem theorem162At_of_polynomial_fejerT3 {k : Nat} (hk : 1 ≤ k)
    (h : PolyCoverAt k (uCount (2 ^ (2 ^ tightMuW k)) (uDegT3 k))
      (uExp (2 ^ (2 ^ tightMuW k)) (uDegT3 k))) : Theorem162At k :=
  theorem162At_of_polynomial (h.uniform_mono (one_le_pow₀ (by norm_num))
    (pow_le_pow_right₀ (by norm_num) (Nat.pow_le_pow_right (by norm_num) (tightMuW_le_tightMuV k)))
    (uDegT3_le_uDeg68 hk))

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

/-- The envelope after one step (no threshold). -/
def envStepJT3 (k μ0 μK μ : Nat) : Nat :=
  max (GenParamsJT3.densDegJT3 k μ0 + μ + k + 19) (GenParamsJT3.expDegJT3 k μ0 μK + 6)

/-- **The single-piece step with polynomial envelopes.** -/
theorem polyEnvBound_stepJT3 (P : GenParamsJT3) {μV μK μ : Nat} (H : P.CHyp μV μK) (hk : 1 ≤ P.k)
    (hcov : ∀ l, 1 ≤ l → l ≤ P.k → PolyCoverAt l (uCount P.V (uDegT3 l)) (uExp P.V (uDegT3 l)))
    (hrec : Section16RecurrenceProfileWith P.k (familyRecThr P.k P.K P.p) (familyRecExp P.k P.p))
    (hlow : PolyEnvBound (P.k + 1) μ) : PolyEnvBound (P.k + 2) (envStepJT3 P.k P.μ0 μK μ) := by
  intro alpha ha ha2
  have hX := two_div_ge_two ha ha2
  -- the input parameter, the lower-degree bound, the step and `Eloc`
  obtain ⟨he0, he8, hei, hy0, hyle, hyi⟩ := P.yIn_boundsJT3 ha ha2 H.hV H.hVμ H.hμ0
  have hy2 : P.yIn alpha ≤ 1 / 2 := hyle.trans ha2
  obtain ⟨β, σ, T, hB, b0, b1, s0, s16, bi, si⟩ := hlow _ hy0 hy2
  have hstep := P.inverse_step H.hV H.hK H.hp hk hcov hrec ha ha2 hB b0 s0 s16
  obtain ⟨hEl0, hEli⟩ := P.Eloc_inv_leJT3 H ha ha2
  obtain ⟨-, hEl2, -⟩ := P.Eloc_pos_le H.hV H.hp ha ha2
  set k := P.k with hkdef
  set E := GenParamsJT3.expDegJT3 k P.μ0 μK with hEdef
  set dd := GenParamsJT3.densDegJT3 k P.μ0 with hdddef
  set M1 := dd + 1 + μ with hM1def
  obtain ⟨-, hYμ⟩ := input_scale_le (μ := μ) ha ha2 hy0 hyi
  have bi' : β⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) := bi.trans hYμ
  have si' : σ⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) := si.trans hYμ
  have hei' : (P.eta alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) :=
    pw_mono hX hei (by rw [hM1def, hdddef]; unfold GenParamsJT3.densDegJT3; omega)
  have heta1 : P.eta alpha ≤ 1 := by linarith
  obtain ⟨σ0', σ16', σeq⟩ := sigma_step (d := k + 1) hEl0 hEl2 s0 s16
  have h32P : 32 * (polynomialPartitionConstant (k + 1 + 1) : Real) ≤
      (2 / alpha) ^ (2 ^ (k + 9)) := by
    refine pw_const hX ?_
    have hP := polyPartConst_le (k + 1 + 1)
    rw [show k + 1 + 1 + 1 = k + 3 by ring] at hP
    have hn : 4 * (k + 3) ^ 2 + 5 ≤ 2 ^ (k + 9) := four_sq_add_five_le k
    have hnat : 32 * polynomialPartitionConstant (k + 1 + 1) ≤ 2 ^ (2 ^ (k + 9)) := by
      calc 32 * polynomialPartitionConstant (k + 1 + 1) ≤ 2 ^ 5 * 2 ^ (4 * (k + 3) ^ 2) :=
            Nat.mul_le_mul (by norm_num) hP
        _ = 2 ^ (4 * (k + 3) ^ 2 + 5) := by rw [← pow_add]; ring_nf
        _ ≤ 2 ^ (2 ^ (k + 9)) := Nat.pow_le_pow_right (by norm_num) hn
    exact_mod_cast hnat
  set S := max (max (k + 9) (E + 3) + 1) M1 + 1 with hSdef
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
    unfold envStepJT3; rw [← hdddef]; omega
  · unfold envStepJT3; rw [← hdddef, ← hEdef]; omega


/-- The Theorem 18.1 envelope at the tight base budget. -/
def polyGenMuJT3 : Nat → Nat
  | 0 => 74
  | 1 => 74
  | k + 2 => envStepJT3 (k + 2) (tightMu0Z (k + 2)) (genMuKZ (k + 2)) (polyGenMuJT3 (k + 1))

theorem polyGenMuJT3_succ {k : Nat} (hk : 1 ≤ k) :
    polyGenMuJT3 (k + 1) = envStepJT3 (k + 1) (tightMu0Z (k + 1)) (genMuKZ (k + 1)) (polyGenMuJT3 k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rfl


theorem polyEnvBound_allJT3 (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ (4 * k + 16)))
    {Kφ : Real} {pφ : Nat} (hpp : ProgressionPhasePartition Kφ pφ) (hpφ : 0 < pφ)
    (hKφ : Kφ ≤ 2 ^ pφ) (hpφB : (pφ : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64)) :
    ∀ k, 2 ≤ k → PolyEnvBound (k + 2) (polyGenMuJT3 k) := by
  have hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))) :=
    fun k hk => abstractFamilyLemma166At_of k (hK k) (hp k) (hrec k hk)
  have hK1 : ∀ k, 1 ≤ Kc k := fun k => le_trans (by norm_num) (hK k)
  have hstep : ∀ k, 2 ≤ k → ∀ μ, PolyEnvBound (k + 1) μ →
      PolyEnvBound (k + 2) (envStepJT3 k (tightMu0Z k) (genMuKZ k) μ) := by
    intro k hk μ hlow
    let P : GenParamsJT3 := ⟨classV Kc pc k, k, Kc k, pc k, tightMu0Z k⟩
    have H : P.CHyp (tightMuW k) (genMuKZ k) := tightHyp_of_profiles_fejerJT3 Kc pc hK hp hconst hk
    have hcov : ∀ l, 1 ≤ l → l ≤ P.k →
        PolyCoverAt l (uCount P.V (uDegT3 l)) (uExp P.V (uDegT3 l)) := by
      intro l hl1 hlk
      have hcl := polyCoverAt_classT3 Kc pc hK1 hp hlem hl1
      exact hcl.uniform_mono (one_le_classV Kc pc l) (classV_mono Kc pc hlk) le_rfl
    exact polyEnvBound_stepJT3 P H (by show 1 ≤ k; omega) hcov (hrec k (by omega)) hlow
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    exact hstep 2 le_rfl 74 (polyEnvBound_three_of_phase_partition hpp hpφ hKφ hpφB)
  | succ k hk ih =>
    rw [polyGenMuJT3_succ (by omega)]
    exact hstep (k + 1) (by omega) (polyGenMuJT3 k) ih


/-! ### Closed forms -/

theorem envStepJT3_le_tight {k : Nat} (hk : 15 ≤ k) (μ : Nat) :
    envStepJT3 k (tightMu0Z k) (genMuKZ k) μ ≤
      μ + 10 * 2 ^ (k - 1) + 6 * (k + 4) ^ 2 + 7 * k + 64 := by
  unfold envStepJT3 GenParamsJT3.densDegJT3 GenParamsJT3.expDegJT3 GenParamsJT3.rhoDegJT3 tightMu0Z tightMuW
    genMuKZ pDeg
  rw [tDegT3_eq_of_ge hk]
  have := Nat.lt_two_pow_self (n := k - 1)
  generalize (k + 4) ^ 2 = s
  generalize 2 ^ (k - 1) = y at *
  omega

theorem polyGenMuJT3_fifteen : polyGenMuJT3 15 + 4 * 15 + 128 ≤ 16 * 2 ^ 15 := by decide +kernel

theorem polyGenMuJT3_le16 : ∀ k, 15 ≤ k → polyGenMuJT3 k + 4 * k + 128 ≤ 16 * 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact polyGenMuJT3_fifteen
  | succ k hk ih =>
    rw [polyGenMuJT3_succ (by omega)]
    have h1 := envStepJT3_le_tight (k := k + 1) (by omega) (polyGenMuJT3 k)
    have h2 := thirtytwo_sq_le_two_pow_fourteen k (by omega)
    have h4 : 7 * k + 80 ≤ (k + 5) ^ 2 := by nlinarith
    rw [show k + 1 + 4 = k + 5 by ring, show k + 1 - 1 = k by omega] at h1
    rw [pow_succ]
    generalize (k + 5) ^ 2 = s5 at *
    generalize 2 ^ k = x at *
    omega

theorem polyGenMuJT3_small16 {k : Nat} (h1 : 9 ≤ k) (h2 : k ≤ 14) :
    polyGenMuJT3 k + 1 ≤ 16 * 2 ^ k := by
  interval_cases k <;> decide +kernel

theorem polyGenMuJT3_fit16 {k : Nat} (hk : 9 ≤ k) : polyGenMuJT3 k + 1 ≤ 16 * 2 ^ k := by
  rcases Nat.lt_or_ge k 15 with h | h
  · exact polyGenMuJT3_small16 hk (by omega)
  · have := polyGenMuJT3_le16 k h
    have h16 : 16 * 2 ^ k ≤ 16 * 2 ^ k := Nat.mul_le_mul_right _ (by norm_num)
    omega

theorem polyGenMuJT3_small32 {k : Nat} (h1 : 6 ≤ k) (h2 : k ≤ 14) :
    polyGenMuJT3 k + 1 ≤ 32 * 2 ^ k := by
  interval_cases k <;> decide +kernel

theorem polyGenMuJT3_fit32 {k : Nat} (hk : 6 ≤ k) : polyGenMuJT3 k + 1 ≤ 32 * 2 ^ k := by
  rcases Nat.lt_or_ge k 15 with h | h
  · exact polyGenMuJT3_small32 hk (by omega)
  · have := polyGenMuJT3_le16 k h
    have h16 : 16 * 2 ^ k ≤ 32 * 2 ^ k := Nat.mul_le_mul_right _ (by norm_num)
    omega

theorem polyGenMuJT3_small64 {k : Nat} (h1 : 2 ≤ k) (h2 : k ≤ 14) :
    polyGenMuJT3 k + 1 ≤ 64 * 2 ^ k := by
  interval_cases k <;> decide +kernel

theorem polyGenMuJT3_fit64 {k : Nat} (hk : 2 ≤ k) : polyGenMuJT3 k + 1 ≤ 64 * 2 ^ k := by
  rcases Nat.lt_or_ge k 15 with h | h
  · exact polyGenMuJT3_small64 hk (by omega)
  · have := polyGenMuJT3_le16 k h
    have h16 : 16 * 2 ^ k ≤ 64 * 2 ^ k := Nat.mul_le_mul_right _ (by norm_num)
    omega

theorem genMuXK3_small32 {k : Nat} (h1 : 7 ≤ k) (h2 : k ≤ 14) :
    genMuXK3 k + 2 * k + 22 ≤ 32 * 2 ^ k := by
  interval_cases k <;> decide +kernel

theorem genMuXK3_fit32 {k : Nat} (hk : 7 ≤ k) : genMuXK3 k + 2 * k + 22 ≤ 32 * 2 ^ k := by
  rcases Nat.lt_or_ge k 15 with h | h
  · exact genMuXK3_small32 hk (by omega)
  · have := genMuXK3_le16 k h
    have h16 : 16 * 2 ^ k ≤ 32 * 2 ^ k := Nat.mul_le_mul_right _ (by norm_num)
    omega

theorem genMuXK3_small64 {k : Nat} (h1 : 4 ≤ k) (h2 : k ≤ 14) :
    genMuXK3 k + 2 * k + 22 ≤ 64 * 2 ^ k := by
  interval_cases k <;> decide +kernel

theorem genMuXK3_fit64 {k : Nat} (hk : 4 ≤ k) : genMuXK3 k + 2 * k + 22 ≤ 64 * 2 ^ k := by
  rcases Nat.lt_or_ge k 15 with h | h
  · exact genMuXK3_small64 hk (by omega)
  · have := genMuXK3_le16 k h
    have h16 : 16 * 2 ^ k ≤ 64 * 2 ^ k := Nat.mul_le_mul_right _ (by norm_num)
    omega

theorem genMuXK3_small128 {k : Nat} (h1 : 2 ≤ k) (h2 : k ≤ 14) :
    genMuXK3 k + 2 * k + 22 ≤ 128 * 2 ^ k := by
  interval_cases k <;> decide +kernel

theorem genMuXK3_fit128 {k : Nat} (hk : 2 ≤ k) : genMuXK3 k + 2 * k + 22 ≤ 128 * 2 ^ k := by
  rcases Nat.lt_or_ge k 15 with h | h
  · exact genMuXK3_small128 hk (by omega)
  · have := genMuXK3_le16 k h
    have h16 : 16 * 2 ^ k ≤ 128 * 2 ^ k := Nat.mul_le_mul_right _ (by norm_num)
    omega

end LeanProofs.GowersSzemeredi
