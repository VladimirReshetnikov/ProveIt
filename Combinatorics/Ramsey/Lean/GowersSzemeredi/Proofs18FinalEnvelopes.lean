import GowersSzemeredi.Proofs18FinalStep
import GowersSzemeredi.Proofs18EnvelopeInduction
import GowersSzemeredi.Proofs18RefinementThresholdBounds

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
    rw [← pow_add]; congr 1
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
  exact inv_thr_le_ex_of_partition_bound hX (polyPartConst_le_sharp k)
    hη0 hη1 hβ0 hβ1 hηi hβi hs0 hs16 hσ'0 hσ'

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

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
  set k := P.k
  set E := GenParamsJT3.expDegJT3 k P.μ0 μK
  set Th := GenParamsJT3.threshDegJT3 k P.μ0 μK with hThdef
  set dd := GenParamsJT3.densDegJT3 k P.μ0 with hdddef
  set M1 := dd + 1 + μ with hM1def
  have hETh : E + 4 ≤ Th := by rw [hThdef]; unfold GenParamsJT3.threshDegJT3; exact le_max_left _ _
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
      (2 / alpha) ^ (2 ^ (partDeg k + 4)) :=
    mul32_nat_le_pw hX (polyPartConst_le_sharp k)
      (Nat.lt_two_pow_self (n := partDeg k + 4))
  set S := max (max (partDeg k + 4) (E + 3) + 1) M1 + 1
  have hσ' : (inverseStepExponent (k + 1) (P.Eloc alpha) σ)⁻¹ ≤
      Real.exp ((2 / alpha) ^ (2 ^ S)) := by
    rw [σeq]
    have h1 := pw_mul' hX (inv_pos.mpr hEl0).le
      h32P hEli
    exact ex_mul' hX (inv_pos.mpr s0).le (ex_of_pw h1) si'
  -- the thresholds
  have hshort := short_thr_step_le hX (k := k) hEl0 hEli Ti' hTl
  have hinv := inv_thr_le_ex_sharp hX (k := k) he0 heta1 b0 b1 hei' bi' s0 s16 σ0' hσ'
  -- assemble
  refine ⟨P.eta alpha * β / 4, _, _, hstep, div_pos (mul_pos he0 b0) (by norm_num), ?_, σ0', σ16',
    ?_, ex_mono hX hσ' ?_, ?_⟩
  · have : P.eta alpha * β ≤ 1 := mul_le_one₀ heta1 b0.le b1
    linarith
  · refine pw_mono hX (inv_mul_div_four_le_pw hX he0 b0 hei' bi') ?_
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

theorem envStepKTx3_le_tight {k : Nat} (hk : 15 ≤ k) (μ : Nat) :
    envStepKTx3 k (tightMu0Z k) (genMuKZ k) μ ≤
      μ + 10 * 2 ^ (k - 1) + 6 * (k + 4) ^ 2 + partDeg k + 6 * k + 59 := by
  unfold envStepKTx3 GenParamsJT3.densDegJT3 GenParamsJT3.threshDegJT3 GenParamsJT3.expDegJT3
    GenParamsJT3.rhoDegJT3 tightMu0Z tightMuW genMuKZ pDeg
  rw [tDegT3_eq_of_ge hk]
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

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

theorem singlePieceEtaFJ_le_density {Qb : Nat → Real → Real → Real → Real} {alpha : Real}
    {k : Nat} (ha : 0 < alpha) (ha1 : alpha ≤ 1) (hD : 0 ≤ singlePieceGlobalDensityFJ Qb alpha (alpha / 2) k) :
    singlePieceEtaFJ Qb alpha k ≤ singlePieceGlobalDensityFJ Qb alpha (alpha / 2) k := by
  exact singlePieceEta_scalar_le hD ha.le ha1

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

/-- The exponent degree of the joint-slice step at `(tDegT3, tightMu0Z)`: two
class degrees (`3·tDegT3` at the X step). -/
theorem expDegJT3_tight_le (k : Nat) :
    GenParamsJT3.expDegJT3 k (tightMu0Z k) (genMuKZ k) + 3 ≤ 2 * tDegT3 k + 7 * k + 38 := by
  unfold GenParamsJT3.expDegJT3 GenParamsJT3.rhoDegJT3 tightMu0Z tightMuW genMuKZ pDeg
  simp only [max_def]
  split_ifs <;> omega

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
  set k := P.k
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
      (2 / alpha) ^ (2 ^ (k + 9)) :=
    mul32_nat_le_pw hX
      (by simpa only [show k + 1 + 1 + 1 = k + 3 by omega]
        using polyPartConst_le (k + 1 + 1)) (four_sq_add_five_le k)
  set S := max (max (k + 9) (E + 3) + 1) M1 + 1
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

/-! ### Closed forms -/

theorem envStepJT3_le_tight {k : Nat} (hk : 15 ≤ k) (μ : Nat) :
    envStepJT3 k (tightMu0Z k) (genMuKZ k) μ ≤
      μ + 10 * 2 ^ (k - 1) + 6 * (k + 4) ^ 2 + 7 * k + 64 := by
  unfold envStepJT3 GenParamsJT3.densDegJT3 GenParamsJT3.expDegJT3 GenParamsJT3.rhoDegJT3 tightMu0Z tightMuW
    genMuKZ pDeg
  rw [tDegT3_eq_of_ge hk]
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

/-- **The inputs of the final route**: recurrence profiles with family constants
`Kc`, `pc` at most `2^(2^(4k+16))`, and a progression phase partition. -/
structure FinalInputs where
  Kc : Nat → Nat
  pc : Nat → Nat
  two_le_Kc : ∀ k, 2 ≤ Kc k
  pc_pos : ∀ k, 0 < pc k
  profile : ∀ k, 1 ≤ k →
    Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k))
  const : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ (4 * k + 16))
  phase : ∃ (K : Real) (p : Nat), ProgressionPhasePartition K p ∧ 0 < p ∧ K ≤ 2 ^ p ∧
    (p : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64)

/-- The fit of the Theorem 18.1 envelope from `k0` on, given the dimensions `k0, …, 14`. -/
theorem polyGenMuJT3_fit {C k0 k : Nat} (hC : 16 ≤ C)
    (hsmall : ∀ j, k0 ≤ j → j ≤ 14 → polyGenMuJT3 j + 1 ≤ C * 2 ^ j) (hk : k0 ≤ k) :
    polyGenMuJT3 k + 1 ≤ C * 2 ^ k := by
  rcases Nat.lt_or_ge k 15 with h | h
  · exact hsmall k hk (by omega)
  · have := polyGenMuJT3_le16 k h
    have := Nat.mul_le_mul_right (2 ^ k) hC
    omega

/-- The fit of the Theorem 18.2 envelope from `k0` on, given the dimensions `k0, …, 14`. -/
theorem genMuXK3_fit {C k0 k : Nat} (hC : 16 ≤ C)
    (hsmall : ∀ j, k0 ≤ j → j ≤ 14 → genMuXK3 j + 2 * j + 22 ≤ C * 2 ^ j) (hk : k0 ≤ k) :
    genMuXK3 k + 2 * k + 22 ≤ C * 2 ^ k := by
  rcases Nat.lt_or_ge k 15 with h | h
  · exact hsmall k hk (by omega)
  · have := genMuXK3_le16 k h
    have := Nat.mul_le_mul_right (2 ^ k) hC
    omega

namespace FinalInputs

variable (I : FinalInputs)
include I

/-- The parameters of the step in dimension `k`. -/
def params (k : Nat) : GenParamsJT3 := ⟨classV I.Kc I.pc k, k, I.Kc k, I.pc k, tightMu0Z k⟩

/-- The standing hypotheses of the step at the polynomial base budget. -/
theorem hyp {k : Nat} (hk : 2 ≤ k) : (I.params k).CHyp (tightMuW k) (genMuKZ k) := by
  have hKr : (I.Kc k : Real) ≤ 2 ^ ((2 : Nat) ^ genMuKZ k) := by
    have := I.const k; unfold genMuKZ; linarith [Nat.cast_nonneg (α := Real) (I.pc k)]
  have hpr : (I.pc k : Real) ≤ 2 ^ ((2 : Nat) ^ genMuKZ k) := by
    have := I.const k; unfold genMuKZ; linarith [Nat.cast_nonneg (α := Real) (I.Kc k)]
  refine ⟨one_le_classV I.Kc I.pc k, classV_le_poly I.Kc I.pc I.const k, le_rfl, ?_, I.two_le_Kc k,
    ?_, I.pc_pos k, ?_⟩
  · show k ≤ 2 ^ tightMu0Z k
    calc k ≤ 2 ^ k := Nat.lt_two_pow_self.le
      _ ≤ 2 ^ tightMu0Z k := Nat.pow_le_pow_right (by norm_num) (by
          unfold tightMu0Z; have := five_k_le_pDeg k
          have := le_max_right (tightMuW k) (pDeg k); omega)
  · have : ((I.Kc k : Nat) : Real) ≤ ((2 ^ 2 ^ genMuKZ k : Nat) : Real) := by push_cast; exact hKr
    exact_mod_cast this
  · have : ((I.pc k : Nat) : Real) ≤ ((2 ^ 2 ^ genMuKZ k : Nat) : Real) := by push_cast; exact hpr
    exact_mod_cast this

/-- The polynomial covers at the classes `tDegT3`, over the class base in dimension `l`. -/
theorem cover {l : Nat} (hl : 1 ≤ l) :
    PolyCoverAt l (uCount (classV I.Kc I.pc l) (uDegT3 l)) (uExp (classV I.Kc I.pc l) (uDegT3 l)) :=
  polyCoverAt_classT3 I.Kc I.pc (fun k => le_trans (by norm_num) (I.two_le_Kc k)) I.pc_pos
    (fun k hk => abstractFamilyLemma166At_of k (I.two_le_Kc k) (I.pc_pos k) (I.profile k hk)) hl

/-- The covers the step in dimension `k` needs. -/
theorem covers (k : Nat) : ∀ l, 1 ≤ l → l ≤ (I.params k).k →
    PolyCoverAt l (uCount (I.params k).V (uDegT3 l)) (uExp (I.params k).V (uDegT3 l)) :=
  fun _ hl1 hlk => (I.cover hl1).uniform_mono (one_le_classV I.Kc I.pc _)
    (classV_mono I.Kc I.pc hlk) le_rfl

/-- **The Theorem 18.2 envelope** in every dimension `k ≥ 2`. -/
theorem envBound : ∀ k, 2 ≤ k → EnvBound (k + 2) (genMuXK3 k) := by
  have hstep : ∀ k, 2 ≤ k → ∀ μ, EnvBound (k + 1) μ →
      EnvBound (k + 2) (envStepKTx3 k (tightMu0Z k) (genMuKZ k) μ) := by
    intro k hk μ hlow
    exact envBound_stepKx3 (I.params k) (I.hyp hk) (by show 1 ≤ k; omega) (I.covers k)
      (I.profile k (by omega)) hlow
  intro k hk
  exact envelope_induction (P := EnvBound) (budget := genMuXK3) hstep
    envBound_three (fun _ h => genMuXK3_succ h) k (by omega)

/-- **The Theorem 18.1 envelope** in every dimension `k ≥ 2`. -/
theorem polyEnvBound : ∀ k, 2 ≤ k → PolyEnvBound (k + 2) (polyGenMuJT3 k) := by
  obtain ⟨K, p, hpp, hp, hK, hpB⟩ := I.phase
  have hstep : ∀ k, 2 ≤ k → ∀ μ, PolyEnvBound (k + 1) μ →
      PolyEnvBound (k + 2) (envStepJT3 k (tightMu0Z k) (genMuKZ k) μ) := by
    intro k hk μ hlow
    exact polyEnvBound_stepJT3 (I.params k) (I.hyp hk) (by show 1 ≤ k; omega) (I.covers k)
      (I.profile k (by omega)) hlow
  intro k hk
  exact envelope_induction (P := PolyEnvBound) (budget := polyGenMuJT3) hstep
    (polyEnvBound_three_of_phase_partition hpp hp hK hpB)
    (fun _ h => polyGenMuJT3_succ h) k (by omega)

/-- **Theorem 16.2 with polynomial controls** at the classes `tDegT3`, in every dimension. -/
theorem theorem_16_2_polynomial {k : Nat} (hk : 1 ≤ k) :
    PolyCoverAt k (uCount (2 ^ (2 ^ tightMuW k)) (uDegT3 k))
      (uExp (2 ^ (2 ^ tightMuW k)) (uDegT3 k)) :=
  (I.cover hk).uniform_mono (one_le_classV I.Kc I.pc k) (classV_le_poly I.Kc I.pc I.const k) le_rfl

/-- **Corollary 16.11 with polynomial exponents** in dimension `k + 1`. -/
theorem corollary_16_11_polynomial {k : Nat} (hk : 2 ≤ k) :
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
  let P := I.params k
  have H : P.CHyp (tightMuW k) (genMuKZ k) := I.hyp hk
  have hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ uCount P.V (uDegT3 l) g t s :=
    fun l g t s _ _ => one_le_uCount P.V (uDegT3 l) g t s
  have hretile : ∀ q, Section16RetiledLinearityBound P.k q (familyRecExp P.k P.p q)
      (familyRecThr P.k P.K P.p q) :=
    fun q => ((I.profile k (by omega)).retiled_family
      (fun q => familyRecThr_pos (by have := I.two_le_Kc k; omega) q) q).single
  -- the two exponents
  obtain ⟨hEl0, hEli⟩ := P.Eloc_inv_leJT3 H ha ha2
  obtain ⟨-, -, hei, -, -, -⟩ := P.yIn_boundsJT3 ha ha2 H.hV H.hVμ H.hμ0
  set D := singlePieceGlobalDensityFJ (fun l => uCount P.V (uDegT3 l)) alpha (alpha / 2) P.k
  have hD0 : 0 < D := singlePieceGlobalDensityFJ_pos ha (by linarith) hQb
  have heta0 : 0 < P.eta alpha := by
    exact singlePieceEtaFJ_pos ha (by linarith) hQb
  have hetaD : P.eta alpha ≤ D := singlePieceEtaFJ_le_density ha (by linarith) hD0.le
  have hDi : D⁻¹ ≤ (2 / alpha) ^ (2 ^ (GenParamsJT3.expDegJT3 k (tightMu0Z k) (genMuKZ k) + 3)) := by
    refine (inv_anti₀ heta0 hetaD).trans (pw_mono hX hei ?_)
    show GenParamsJT3.rhoDegJT3 k (tightMu0Z k) + tDegT3 k + 10 ≤
      GenParamsJT3.expDegJT3 k (tightMu0Z k) (genMuKZ k) + 3
    unfold GenParamsJT3.expDegJT3
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
      (by show 1 ≤ k; omega) ha ha2 (I.covers k) hQb
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

end FinalInputs

end LeanProofs.GowersSzemeredi
