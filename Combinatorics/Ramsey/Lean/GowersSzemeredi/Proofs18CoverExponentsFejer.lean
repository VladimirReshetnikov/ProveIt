import GowersSzemeredi.Proofs18CoverExponents
import GowersSzemeredi.Proofs18CoverDensityFejer
import GowersSzemeredi.Proofs18CoverBudget

/-! **The width exponents and thresholds of the Section 18 step under the
Fejér θ₁** (Notes L.16d).

The Fejér instance of `Proofs18CoverExponents` (generated; no printed
parameter survives): `expDegF`, `threshDegF` and their bounds, with the class
degree `23·2^k` in place of `68·2^k`. The fixed parameters enter through
`Proofs18FejerEnvelopeBase` at the printed exponents. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

namespace GenParamsF

/-- The standing hypotheses on the parameters (no bound on `k`). -/
structure CHyp (P : GenParamsF) (μV μK : Nat) : Prop where
  hV : 1 ≤ P.V
  hVμ : P.V ≤ 2 ^ (2 ^ μV)
  hμ0 : max μV (fixDeg P.k) + 2 ≤ P.μ0
  hk0 : P.k ≤ 2 ^ P.μ0
  hK : 2 ≤ P.K
  hKμ : P.K ≤ 2 ^ 2 ^ μK
  hp : 0 < P.p
  hpμ : P.p ≤ 2 ^ (2 ^ μK)

variable (P : GenParamsF) {alpha : Real}

/-- The log-degree of the width exponents. -/
def expDegF (k μ0 μK : Nat) : Nat :=
  max (rhoDegF k μ0 + 2 * (23 * 2 ^ k) + 9) (max (rhoDegF k μ0 + 23 * 2 ^ k + k + 7) (μK + 2))

/-- **`Em`, `QM` and `Bexp`**. -/
theorem spectrum_exps_inv_leF {μV μK : Nat} (H : CHyp P μV μK) (ha : 0 < alpha)
    (ha2 : alpha ≤ 1 / 2) :
    (P.Em alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ (rhoDegF P.k P.μ0 + 23 * 2 ^ P.k + 2)) ∧
      (P.QM alpha : Real) + 1 ≤ (2 / alpha) ^ (2 ^ (rhoDegF P.k P.μ0 + 23 * 2 ^ P.k + 3)) ∧
      (P.Bexp alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ expDegF P.k P.μ0 μK) := by
  have hX := two_div_ge_two ha ha2
  have hX1 : (1 : Real) ≤ 2 / alpha := by linarith
  have hri := P.rho1_inv_leF ha ha2 H.hV H.hVμ H.hμ0
  set k := P.k with hkdef
  set ρ := rhoDegF k P.μ0 with hρdef
  set μD := 23 * 2 ^ k with hμDdef
  have hρ1 : μD + P.μ0 + 3 ≤ ρ := (rhoDegC_gF k P.μ0).1
  have hM2 : ρ + μD + k + 7 ≤ expDegF k P.μ0 μK := by
    unfold expDegF; exact (le_max_left _ _).trans (le_max_right _ _)
  have hM3 : μK + 2 ≤ expDegF k P.μ0 μK := by
    unfold expDegF; exact (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨hB0, hB1, hBi⟩ := budget_gen_bounds_fejer k ha ha2
  obtain ⟨hd0, hd1, hdi⟩ := delta_gen_bounds_fejer k ha ha2
  obtain ⟨ht0, ht1, -⟩ := T2_gen_bounds_fejer k ha ha2
  obtain ⟨hr0, hr1⟩ : 0 < P.Rho1 alpha ∧ P.Rho1 alpha ≤ 1 := P.rho1_pos_le ha ha2
  have hq0 : 0 < P.Rho1 alpha / 2 / 2 := by linarith
  have hq1 : P.Rho1 alpha / 2 / 2 ≤ 1 := by linarith
  have hqi : (P.Rho1 alpha / 2 / 2)⁻¹ ≤ (2 / alpha) ^ (2 ^ (ρ + 1)) := by
    rw [show (P.Rho1 alpha / 2 / 2)⁻¹ = 4 * (P.Rho1 alpha)⁻¹ by field_simp; ring]
    have h4 : (4 : Real) ≤ (2 / alpha) ^ (2 ^ ρ) := pw_const hX (by
      have : 2 ≤ 2 ^ ρ := le_trans (by norm_num : 2 ≤ 2 ^ 1)
        (Nat.pow_le_pow_right (by norm_num) (by omega))
      calc (4 : Real) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 ^ ρ) := pow_le_pow_right₀ (by norm_num) this)
    exact pw_mul hX (by norm_num) (inv_pos.mpr hr0).le h4 hri
  have hQ := uCount_scale_le (c := ρ + 1) (D := uDeg23 k) (μD := μD) hX H.hV H.hVμ H.hμ0 hd0 hd1 hdi
    hB0 hB1 hBi hq0 hq1 hqi le_rfl
  rw [max_eq_right (show P.μ0 ≤ ρ + 1 by omega)] at hQ
  have hQv : singlePieceGlobalQmaxF (fun l => uCount P.V (uDeg23 l)) alpha
      (alpha / 2) k ≤ (2 / alpha) ^ (2 ^ (ρ + 1 + 1 + μD)) := hQ
  have hQv1 : 1 ≤ singlePieceGlobalQmaxF (fun l => uCount P.V (uDeg23 l))
      alpha (alpha / 2) k := one_le_uCount _ _ _ _ _
  have hQM := GenParams.floor_succ_le_pw hX hQv1 hQv
  have hQM' : (P.QM alpha : Real) + 1 ≤ (2 / alpha) ^ (2 ^ (ρ + μD + 3)) :=
    hQM.trans (pw_natpow hX (Nat.pow_le_pow_right (by norm_num) (by omega)))
  refine ⟨?_, hQM', ?_⟩
  · show (uCount P.V (uDeg23 k) _ _ _)⁻¹⁻¹ ≤ _
    rw [inv_inv]
    exact hQ.trans (pw_natpow hX (Nat.pow_le_pow_right (by norm_num) (by omega)))
  · show (familyRecExp k P.p (P.QM alpha) / 2)⁻¹ ≤ _
    rw [GenParams.half_familyRecExp_inv]
    have hq0' : (0 : Real) ≤ (P.QM alpha : Real) + 1 := by
      have := Nat.cast_nonneg (α := Real) (P.QM alpha); linarith
    have hk2 : 2 * 2 ^ (k + 1) ≤ 2 ^ (k + 2) := by rw [pow_succ 2 (k + 1)]; omega
    have hpow := pw_pow hX hq0' hQM' hk2
    have hp' : (P.p : Real) ≤ (2 / alpha) ^ (2 ^ μK) := pw_const hX (by exact_mod_cast H.hpμ)
    have h4 : (4 : Real) ≤ (2 / alpha) ^ (2 ^ (μK + 1)) := pw_const hX (by
      have : 2 ≤ 2 ^ (μK + 1) := le_trans (by norm_num : 2 ≤ 2 ^ 1)
        (Nat.pow_le_pow_right (by norm_num) (by omega))
      calc (4 : Real) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 ^ (μK + 1)) := pow_le_pow_right₀ (by norm_num) this)
    have hpq0 : (0 : Real) ≤ ((P.QM alpha : Real) + 1) ^ (2 * 2 ^ (k + 1)) := pow_nonneg hq0' _
    have h1 := pw_mul' hX (Nat.cast_nonneg _) hpq0 hp' hpow
    have h2 := pw_mul' hX (by norm_num) (mul_nonneg (Nat.cast_nonneg _) hpq0) h4 h1
    refine pw_mono hX h2 ?_
    have : max μK (ρ + μD + 3 + (k + 2)) + 1 ≤ expDegF k P.μ0 μK - 1 := by omega
    omega

/-- **The slice exponents `Eth` and `Ec`**. -/
theorem slice_exps_inv_leF {μV μK : Nat} (H : CHyp P μV μK) (ha : 0 < alpha)
    (ha2 : alpha ≤ 1 / 2) :
    (P.Eth alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ (rhoDegF P.k P.μ0 + 2 * (23 * 2 ^ P.k) + 9)) ∧
      (P.Ec alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ (rhoDegF P.k P.μ0 + 2 * (23 * 2 ^ P.k) + 9)) := by
  have hX := two_div_ge_two ha ha2
  have hX1 : (1 : Real) ≤ 2 / alpha := by linarith
  have hri := P.rho1_inv_leF ha ha2 H.hV H.hVμ H.hμ0
  set k := P.k with hkdef
  set ρ := rhoDegF k P.μ0 with hρdef
  set μD := 23 * 2 ^ k with hμDdef
  have hρ1 : μD + P.μ0 + 3 ≤ ρ := (rhoDegC_gF k P.μ0).1
  obtain ⟨hB0, hB1, hBi⟩ := budget_gen_bounds_fejer k ha ha2
  obtain ⟨ht0, ht1, -⟩ := T2_gen_bounds_fejer k ha ha2
  obtain ⟨hr0, hr1⟩ : 0 < P.Rho1 alpha ∧ P.Rho1 alpha ≤ 1 := P.rho1_pos_le ha ha2
  obtain ⟨hR0, hR1, hRi⟩ := GenParams.rho_step hX hr0 hr1 hri (by omega)
  obtain ⟨hS0, hS1, hSi⟩ := GenParams.thetaS_step hX hR0 hR1 hRi
  have hThS : P.ThS alpha =
      singlePieceTheta ((P.Rho1 alpha) / 2 * ((P.Rho1 alpha) / 2 / 2)) 1 := rfl
  rw [← hThS] at hS0 hS1 hSi
  have hbase := baseCF_recipPowerLB (D := uDeg23 k) (k := k) ha ha2 H.hV H.hVμ
    H.hμ0
  have ha0 : uDeg23 k * 2 ^ P.μ0 + 1 ≤ 2 ^ (μD + P.μ0 + 1) := by
    have h1 : uDeg23 k * 2 ^ P.μ0 ≤ 2 ^ μD * 2 ^ P.μ0 := Nat.mul_le_mul_right _ le_rfl
    have h2 : 2 ^ (μD + P.μ0 + 1) = 2 * (2 ^ μD * 2 ^ P.μ0) := by rw [pow_add, pow_add]; ring
    have h3 : 1 ≤ 2 ^ μD * 2 ^ P.μ0 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hb0 : uDeg23 k + 1 ≤ 2 ^ (μD + 1) := by
    have : 2 ^ (μD + 1) = 2 * 2 ^ μD := by rw [pow_succ]; ring
    have := Nat.one_le_two_pow (n := μD)
    have hD : uDeg23 k ≤ 2 ^ μD := le_rfl
    omega
  obtain ⟨hc0, hc1, hci⟩ := GenParams.cS_step hX hbase hS0 hS1 hSi ha0 hb0 (by omega)
  have hCS : P.CS alpha =
      baseCF P.V (uDeg23 k) P.k alpha (P.ThS alpha) := rfl
  rw [← hCS] at hc0 hc1 hci
  have hslice : ∀ {s : Real} {m : Nat}, 0 < s → s ≤ 1 → s⁻¹ ≤ (2 / alpha) ^ (2 ^ m) →
      P.μ0 ≤ m + 1 → (uExp P.V (uDeg23 k) (alpha / 2) (globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k) (s / 2))⁻¹ ≤
        (2 / alpha) ^ (2 ^ (m + 1 + 1 + μD)) := by
    intro s m hs0 hs1 hsi hm
    have hs20 : 0 < s / 2 := half_pos hs0
    have hs2i : (s / 2)⁻¹ ≤ (2 / alpha) ^ (2 ^ (m + 1)) := by
      rw [inv_div, div_eq_mul_inv]
      exact pw_mul hX (by norm_num) (inv_pos.mpr hs0).le (hX.trans (pw_X hX _)) hsi
    have h := uCount_scale_le (c := m + 1) (D := uDeg23 k) (μD := μD) hX H.hV H.hVμ H.hμ0
      (half_pos ha) (by linarith) (GenParams.half_inv_le k ha ha2) hB0 hB1 hBi hs20 (by linarith)
      hs2i le_rfl
    rw [max_eq_right hm] at h
    show (uCount P.V (uDeg23 k) _ _ _)⁻¹⁻¹ ≤ _
    rw [inv_inv]; exact h
  constructor
  · exact pw_mono hX (hslice hS0 hS1 hSi (by omega)) (by omega)
  · exact pw_mono hX (hslice hc0 hc1 hci (by omega)) (by omega)

/-- **The localization exponent is polynomially small.** -/
theorem Eloc_inv_leF {μV μK : Nat} (H : CHyp P μV μK) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < P.Eloc alpha ∧ (P.Eloc alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ (expDegF P.k P.μ0 μK + 3)) := by
  have hX := two_div_ge_two ha ha2
  set M := expDegF P.k P.μ0 μK with hMdef
  have hM1 : rhoDegF P.k P.μ0 + 2 * (23 * 2 ^ P.k) + 9 ≤ M := by
    rw [hMdef]; unfold expDegF; exact le_max_left _ _
  have hM2 : rhoDegF P.k P.μ0 + 23 * 2 ^ P.k + P.k + 7 ≤ M := by
    rw [hMdef]; unfold expDegF; exact (le_max_left _ _).trans (le_max_right _ _)
  obtain ⟨hE0, -, -, -, -, -⟩ := P.Eloc_pos_le H.hV H.hp ha ha2
  obtain ⟨-, -, -, -, -, -, -, ⟨hEm0, -⟩, ⟨hEth0, -⟩, ⟨hEc0, -⟩, ⟨hN0, -, -⟩, ⟨hBx0, -⟩,
    -, -⟩ := P.ranges H.hV H.hp ha ha2
  have hNE := P.nestExp_inv_leF ha ha2 H.hV H.hVμ H.hμ0
  obtain ⟨hEm, -, hBx⟩ := P.spectrum_exps_inv_leF H ha ha2
  obtain ⟨hEth, hEc⟩ := P.slice_exps_inv_leF H ha ha2
  refine ⟨hE0, ?_⟩
  have hval : (P.Eloc alpha)⁻¹ =
      32 * ((P.NestExp alpha)⁻¹ * (P.Em alpha)⁻¹) *
      ((P.Bexp alpha)⁻¹ * ((P.Eth alpha)⁻¹ * (P.Ec alpha)⁻¹)) := by
    show ((P.NestExp alpha * (P.Em alpha / 2)) *
      (P.Bexp alpha * (P.Eth alpha * P.Ec alpha) / 2) / 8)⁻¹ = _
    field_simp
    ring
  rw [hval]
  have hNE' := pw_mono hX hNE (show rhoDegF P.k P.μ0 + 23 * 2 ^ P.k + 3 + P.k ≤ M by omega)
  have hEm' := pw_mono hX hEm (show rhoDegF P.k P.μ0 + 23 * 2 ^ P.k + 2 ≤ M by omega)
  have hEth' := pw_mono hX hEth hM1
  have hEc' := pw_mono hX hEc hM1
  have h32 : (32 : Real) ≤ (2 / alpha) ^ (2 ^ (M + 1)) := pw_const hX (by
    have : 5 ≤ 2 ^ (M + 1) := by have := Nat.lt_two_pow_self (n := M + 1); omega
    calc (32 : Real) = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ (2 ^ (M + 1)) := pow_le_pow_right₀ (by norm_num) this)
  have p1 := pw_mul hX (inv_pos.mpr hN0).le (inv_pos.mpr hEm0).le hNE' hEm'
  have p2 := pw_mul hX (inv_pos.mpr hEth0).le (inv_pos.mpr hEc0).le hEth' hEc'
  have p3 := pw_mul' hX (inv_pos.mpr hBx0).le (by positivity) hBx p2
  have p4 := pw_mul hX (by norm_num) (by positivity) h32 p1
  have p5 := pw_mul' hX (by positivity) (by positivity) p4 p3
  exact pw_mono hX p5 (by omega)


/-- The threshold degree of the step. -/
def threshDegF (k μ0 μK : Nat) : Nat := max (expDegF k μ0 μK + 4) (2 ^ (k + 6) + 5)

/-- **The requirement on `m`**. -/
theorem MReq_le_expF {μV μK : Nat} (H : CHyp P μV μK) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    1 ≤ P.MReq alpha ∧
      P.MReq alpha ≤ Real.exp ((2 / alpha) ^ (2 ^ max (expDegF P.k P.μ0 μK + 3) (2 ^ (P.k + 6) + 4))) := by
  have hX := two_div_ge_two ha ha2
  have hX1 : (1 : Real) ≤ 2 / alpha := by linarith
  obtain ⟨-, hQM, hBx⟩ := P.spectrum_exps_inv_leF H ha ha2
  have hri := P.rho1_inv_leF ha ha2 H.hV H.hVμ H.hμ0
  set k := P.k with hkdef
  set E := expDegF k P.μ0 μK with hEdef
  set Z := 2 ^ (k + 6) + 1 with hZdef
  have hZ2 : 2 ≤ Z := by rw [hZdef]; have := Nat.one_le_two_pow (n := k + 6); omega
  have hρE : rhoDegF k P.μ0 + 23 * 2 ^ k + k + 7 ≤ E := by
    rw [hEdef]; unfold expDegF; exact (le_max_left _ _).trans (le_max_right _ _)
  have hKE : μK + 2 ≤ E := by
    rw [hEdef]; unfold expDegF; exact (le_max_right _ _).trans (le_max_right _ _)
  -- the recurrence threshold
  have hthr := familyRecThr_le_exp (k := k) hX (by have := H.hK; omega) H.hKμ H.hpμ hQM
  have hthr' : (familyRecThr k P.K P.p (P.QM alpha) : Real) ≤
      Real.exp ((2 / alpha) ^ (2 ^ (E + 3))) := ex_mono hX hthr (by omega)
  have hthr1 : (1 : Real) ≤ (familyRecThr k P.K P.p (P.QM alpha) : Real) :=
    Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr
      (familyRecThr_pos (k := k) (p := P.p) (by have := H.hK; omega) _).ne')
  -- the Bohr radius and `ρ`
  obtain ⟨hz0, hzi⟩ := zeta_gen_bounds_fejer k ha ha2
  have hz1 : tightZeta (fejerThetaOne alpha (alpha / 2) k / 4) ≤ 1 / 2 :=
    (tightZeta_pos_le_half (fejerThetaOne_bounds k ha (by linarith) (half_pos ha) (by linarith)).1 (by linarith [(fejerThetaOne_bounds k ha (by linarith) (half_pos ha) (by linarith)).2])).2
  have hzeq : P.Zeta alpha = tightZeta (fejerThetaOne alpha (alpha / 2) k / 4) := rfl
  obtain ⟨ht0, ht1, -⟩ := T2_gen_bounds_fejer k ha ha2
  obtain ⟨hr0, hr1⟩ : 0 < P.Rho1 alpha ∧ P.Rho1 alpha ≤ 1 := P.rho1_pos_le ha ha2
  have hρ1 : 1 ≤ rhoDegF k P.μ0 := by have := (rhoDegC_gF k P.μ0).1; omega
  obtain ⟨hR0, hR1, hRi⟩ := GenParams.rho_step hX hr0 hr1 hri hρ1
  have hReq : P.Rho alpha = P.Rho1 alpha / 2 * (P.Rho1 alpha / 2 / 2) := rfl
  rw [← hReq] at hR0 hR1 hRi
  have hBpos : 0 < P.Bexp alpha := by
    have := familyRecExp_pos k P.p (P.QM alpha) H.hp
    show 0 < familyRecExp k P.p _ / 2; positivity
  set z := P.Zeta alpha with hzdef
  set R := P.Rho alpha with hRdef
  set B := P.Bexp alpha with hBdef
  rw [← hzeq] at hz0 hzi hz1
  have h8 : (8 : Real) ≤ Real.exp ((2 / alpha) ^ (2 ^ 2)) := ex_of_pw (pw_const hX (by norm_num))
  have hzi' : z⁻¹ ≤ Real.exp ((2 / alpha) ^ (2 ^ Z)) := hzi
  have h8z : 8 / z ≤ Real.exp ((2 / alpha) ^ (2 ^ (Z + 1))) := by
    rw [div_eq_mul_inv]
    exact ex_mono hX (ex_mul' hX (inv_pos.mpr hz0).le h8 hzi') (by omega)
  have h16 : (16 : Real) ≤ Real.exp ((2 / alpha) ^ (2 ^ 2)) := ex_of_pw (pw_const hX (by norm_num))
  have h16z : 16 / z ≤ Real.exp ((2 / alpha) ^ (2 ^ (Z + 1))) := by
    rw [div_eq_mul_inv]
    exact ex_mono hX (ex_mul' hX (inv_pos.mpr hz0).le h16 hzi') (by omega)
  have hR3 : (R ^ 3)⁻¹ ≤ (2 / alpha) ^ (2 ^ (rhoDegF k P.μ0 + 2 + 2)) := by
    rw [← inv_pow]; exact pw_pow hX (inv_pos.mpr hR0).le hRi (by norm_num)
  have h4zr : 4 / (z * R ^ 3) ≤
      Real.exp ((2 / alpha) ^ (2 ^ (max (Z + 1) (rhoDegF k P.μ0 + 4) + 1))) := by
    rw [div_eq_mul_inv, mul_inv, ← mul_assoc]
    have h4z : 4 * z⁻¹ ≤ Real.exp ((2 / alpha) ^ (2 ^ (Z + 1))) := by
      have h4 : (4 : Real) ≤ Real.exp ((2 / alpha) ^ (2 ^ 2)) := ex_of_pw (pw_const hX (by norm_num))
      exact ex_mono hX (ex_mul' hX (inv_pos.mpr hz0).le h4 hzi') (by omega)
    exact ex_mul' hX (inv_pos.mpr (pow_pos hR0 3)).le h4z (ex_of_pw hR3)
  have h8z1 : 1 ≤ 8 / z := by rw [le_div_iff₀ hz0]; linarith
  have h16z1 : 1 ≤ 16 / z := by rw [le_div_iff₀ hz0]; linarith
  have h4zr1 : 1 ≤ 4 / (z * R ^ 3) := by
    rw [le_div_iff₀ (by positivity)]
    have : R ^ 3 ≤ 1 := pow_le_one₀ hR0.le hR1
    have : z * R ^ 3 ≤ 1 / 2 * 1 := mul_le_mul hz1 this (by positivity) (by norm_num)
    linarith
  have hBe : 1 / B ≤ (2 / alpha) ^ (2 ^ E) := by rw [one_div]; exact hBx
  have hBe2 : 2 / B ≤ (2 / alpha) ^ (2 ^ (E + 1)) := by
    rw [div_eq_mul_inv]
    exact pw_mul hX (by norm_num) (inv_pos.mpr hBpos).le (hX.trans (pw_X hX _)) hBx
  have e1 := ex_rpow hX h8z1 h8z (by positivity) hBe
  have e2 := ex_rpow hX h4zr1 h4zr (by positivity) hBe
  have e3 := ex_rpow hX h16z1 h16z (by positivity) hBe2
  refine ⟨hthr1.trans (le_max_left _ _), ?_⟩
  show max (familyRecThr k P.K P.p (P.QM alpha) : Real)
    (max ((8 / z) ^ (1 / B)) (max ((4 / (z * R ^ 3)) ^ (1 / B)) ((16 / z) ^ (2 / B)))) ≤ _
  refine max_le (ex_mono hX hthr' (le_max_left _ _)) (max_le ?_ (max_le ?_ ?_))
  · exact ex_mono hX e1 (by rw [hZdef]; have := Nat.one_le_two_pow (n := k + 6); omega)
  · exact ex_mono hX e2 (by rw [hZdef]; have := Nat.one_le_two_pow (n := k + 6); omega)
  · exact ex_mono hX e3 (by rw [hZdef]; have := Nat.one_le_two_pow (n := k + 6); omega)

/-- **The modulus threshold of the step is single exponential.** -/
theorem Tloc_le_expF {μV μK : Nat} (H : CHyp P μV μK) (hk : 1 ≤ P.k) (ha : 0 < alpha)
    (ha2 : alpha ≤ 1 / 2) :
    P.Tloc alpha ≤ Real.exp ((2 / alpha) ^ (2 ^ threshDegF P.k P.μ0 μK)) := by
  have hX := two_div_ge_two ha ha2
  have hX1 : (1 : Real) ≤ 2 / alpha := by linarith
  obtain ⟨hEl0, hEli⟩ := P.Eloc_inv_leF H ha ha2
  obtain ⟨hEm, -, -⟩ := P.spectrum_exps_inv_leF H ha ha2
  have hNE := P.nestExp_inv_leF ha ha2 H.hV H.hVμ H.hμ0
  obtain ⟨-, -, -, -, -, -, -, ⟨hEm0, -⟩, -, -, ⟨hN0, -, -⟩, -, -, -⟩ :=
    P.ranges H.hV H.hp ha ha2
  obtain ⟨hR1, hR⟩ := P.MReq_le_expF H ha ha2
  have hL := lemma156_gen_le_fejer hk ha ha2
  set k := P.k with hkdef
  set E := expDegF k P.μ0 μK with hEdef
  set T := threshDegF k P.μ0 μK with hTdef
  set μD := 23 * 2 ^ k with hμDdef
  have hET : E + 4 ≤ T := by rw [hTdef]; unfold threshDegF; exact le_max_left _ _
  have hZT : 2 ^ (k + 6) + 5 ≤ T := by rw [hTdef]; unfold threshDegF; exact le_max_right _ _
  have hρE : rhoDegF k P.μ0 + μD + k + 7 ≤ E := by
    rw [hEdef]; unfold expDegF; exact (le_max_left _ _).trans (le_max_right _ _)
  obtain ⟨hρ0, hρ2⟩ := rhoDegC_gF k P.μ0
  have hNE' : (P.NestExp alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ E) := pw_mono hX hNE (by omega)
  have hEm' : (P.Em alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ E) := pw_mono hX hEm (by omega)
  have hMx : (P.MExp alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ (E + 2)) := by
    show (P.NestExp alpha * (P.Em alpha / 2))⁻¹ ≤ _
    rw [show (P.NestExp alpha * (P.Em alpha / 2))⁻¹ =
      2 * ((P.NestExp alpha)⁻¹ * (P.Em alpha)⁻¹) by field_simp]
    have p1 := pw_mul hX (inv_pos.mpr hN0).le (inv_pos.mpr hEm0).le hNE' hEm'
    exact pw_mul hX (by norm_num) (by positivity) (hX.trans (pw_X hX _)) p1
  have hMx0 : 0 < P.MExp alpha := by
    show 0 < P.NestExp alpha * (P.Em alpha / 2)
    positivity
  -- the roots
  have h64 : (64 : Real) ^ (1 / P.NestExp alpha) ≤ Real.exp ((2 / alpha) ^ (2 ^ T)) :=
    ex_mono hX (ex_root (j := 3) hX (by norm_num) (by norm_num) hN0 hNE') (by omega)
  have h4 : (4 : Real) ^ (1 / P.NestExp alpha) ≤ Real.exp ((2 / alpha) ^ (2 ^ T)) :=
    ex_mono hX (ex_root (j := 2) hX (by norm_num) (by norm_num) hN0 hNE') (by omega)
  have h6 : (6 : Real) ^ (1 / P.Eloc alpha) ≤ Real.exp ((2 / alpha) ^ (2 ^ T)) :=
    ex_mono hX (ex_root (j := 2) hX (by norm_num) (by norm_num) hEl0 hEli) (by omega)
  have hF : P.F alpha = 8 * P.Eloc alpha := by show P.F alpha = 8 * (P.F alpha / 8); ring
  have h8 : (8 : Real) ^ (2 / P.F alpha) ≤ Real.exp ((2 / alpha) ^ (2 ^ T)) := by
    have hle : 2 / P.F alpha ≤ 1 / P.Eloc alpha := by
      rw [hF, div_le_div_iff₀ (by positivity) hEl0]; nlinarith
    refine (Real.rpow_le_rpow_of_exponent_le (by norm_num) hle).trans ?_
    exact ex_mono hX (ex_root (j := 2) hX (by norm_num) (by norm_num) hEl0 hEli) (by omega)
  -- the requirement on `m`
  have hMR : P.MReq alpha ^ (1 / P.MExp alpha) ≤ Real.exp ((2 / alpha) ^ (2 ^ T)) := by
    rw [one_div]
    refine ex_mono hX (ex_rpow hX hR1 hR (inv_pos.mpr hMx0).le hMx) ?_
    rw [hTdef]; unfold threshDegF; omega
  have hMT : P.MThr alpha ≤ Real.exp ((2 / alpha) ^ (2 ^ T)) :=
    max_le (Real.one_le_exp (by positivity)) h64
  -- Lemma 15.6
  have hL' : fejerProductThreshold k (alpha / 2) (alpha / 2) ≤
      Real.exp ((2 / alpha) ^ (2 ^ T)) := by
    refine ex_of_pw (pw_mono hX hL ?_)
    have : 2 ^ (k + 4) + 4 * k + 13 ≤ 2 ^ (k + 6) + 5 := by
      have h := Nat.lt_two_pow_self (n := k)
      have h4 : 2 ^ (k + 4) = 16 * 2 ^ k := by rw [pow_add]; ring
      have : 2 ^ (k + 6) = 64 * 2 ^ k := by rw [pow_add]; ring
      omega
    omega
  have h3 : (3 : Real) ≤ Real.exp ((2 / alpha) ^ (2 ^ T)) :=
    ex_of_pw (pw_const hX (by
      calc (3 : Real) ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 ^ T) := pow_le_pow_right₀ (by norm_num) (by
            have := Nat.lt_two_pow_self (n := T); omega)))
  show max (max 3 (fejerProductThreshold k (alpha / 2) (alpha / 2)))
    (max (P.MThr alpha)
      (max (4 ^ (1 / P.NestExp alpha))
        (max (P.MReq alpha ^ (1 / P.MExp alpha))
          (max (6 ^ (1 / P.Eloc alpha)) (8 ^ (2 / P.F alpha)))))) ≤ _
  exact max_le (max_le h3 hL') (max_le hMT (max_le h4 (max_le hMR (max_le h6 h8))))

end GenParamsF

/-- The standing hypotheses at the tight base budget. -/
theorem tightHyp_of_profiles_fejer (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5)))) {k : Nat}
    (hk : 2 ≤ k) :
    (⟨classV Kc pc k, k, Kc k, pc k, tightMu0 k⟩ : GenParamsF).CHyp (tightMuV k) (genMuK k) := by
  obtain ⟨hV, -, -, -, -, -, hKk, hKμ, hpk, hpμ⟩ := stdHyp_of_profiles Kc pc hK hp hconst hk
  refine ⟨hV, classV_le_tight Kc pc hconst k, le_rfl, ?_, hKk, hKμ, hpk, hpμ⟩
  show k ≤ 2 ^ tightMu0 k
  calc k ≤ 2 ^ k := Nat.lt_two_pow_self.le
    _ ≤ 2 ^ tightMu0 k := Nat.pow_le_pow_right (by norm_num) (by
        unfold tightMu0 fixDeg; have := Nat.lt_two_pow_self (n := k + 5)
        have := le_max_right (tightMuV k) (2 ^ (k + 5) + 7); omega)

end LeanProofs.GowersSzemeredi
