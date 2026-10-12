import GowersSzemeredi.Proofs18CoverModulusFejerJ
import GowersSzemeredi.Proofs18CoverDensityFejerZ

/-! **The Section 18 step with joint slices**, part 2 (generated from
`Proofs18CoverDensityFejerZ` by `assemble_j.py`).

The joint-slice density `θ·(θ/2)/Q(θ/4)²` equals `8·c(θ/2)²` for
`c(s) = s/2/Q(s/2)`, so it costs one application of the class control
(`GenParams.joint_dens_step`, exponent `m + μ_b + 3`) instead of two
(`GenParams.dens_step`, `m + 2μ_b + 4`). The density degree is
`ρ + tDeg + 11` instead of `ρ + 2·tDeg + 13`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- `3(k+4)² ≤ 2·tDegZ k + 6k + 35`: the side condition of `eta_step_small`
at the joint-slice density degree. -/
theorem sq_le_two_tDegZ (k : Nat) : 3 * (k + 4) ^ 2 ≤ 2 * tDegZ k + 6 * k + 35 := by
  rcases Nat.lt_or_ge k 15 with h | h
  · interval_cases k <;> decide
  · rw [tDegZ_eq_of_ge h]; omega

/-- **The joint-slice density** `θ·(θ - (θ/4 + θ/4))/Q(θ/4)²` for a class control
`c(s) = s/2/Q(s/2)` that is a reciprocal power: one application of `c`. -/
theorem GenParams.joint_dens_step {X : Real} (hX : 2 ≤ X) {c : Real → Real} {a0 b0 : Nat}
    (hc : RecipPowerLB X c a0 b0) {Q : Real → Real} (hcQ : ∀ s, c s = s / 2 / Q (s / 2))
    (hQ1 : ∀ t, 0 < t → t ≤ 1 → 1 ≤ Q t)
    {θ : Real} {m μa μb : Nat} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθi : θ⁻¹ ≤ X ^ (2 ^ m))
    (ha0 : a0 ≤ 2 ^ μa) (hb0 : b0 ≤ 2 ^ μb) (hμa : μa ≤ m) :
    0 < θ * ((θ - (θ / 4 + θ / 4)) / (Q (θ / 4) * Q (θ / 4))) ∧
      θ * ((θ - (θ / 4 + θ / 4)) / (Q (θ / 4) * Q (θ / 4))) ≤ 1 ∧
      (θ * ((θ - (θ / 4 + θ / 4)) / (Q (θ / 4) * Q (θ / 4))))⁻¹ ≤ X ^ (2 ^ (m + μb + 3)) := by
  have hX1 : (1 : Real) ≤ X := by linarith
  have h20 : 0 < θ / 2 := half_pos hθ0
  have h21 : θ / 2 ≤ 1 := by linarith
  have h2i : (θ / 2)⁻¹ ≤ X ^ (2 ^ (m + 1)) := by
    rw [inv_div, div_eq_mul_inv]
    exact pw_mul hX (by norm_num) (inv_pos.mpr hθ0).le (hX.trans (pw_X hX _)) hθi
  obtain ⟨hc0, -, hci⟩ := hc.apply_le hX1 h20 h21 h2i
  have hci' : (c (θ / 2))⁻¹ ≤ X ^ (2 ^ (m + μb + 2)) := by
    refine hci.trans (pow_le_pow_right₀ hX1 ?_)
    have h1 : 2 ^ (m + 1) * b0 ≤ 2 ^ (m + 1) * 2 ^ μb := Nat.mul_le_mul_left _ hb0
    have h2 : 2 ^ (m + 1) * 2 ^ μb = 2 ^ (m + μb + 1) := by rw [← pow_add]; ring_nf
    have h3 : 2 ^ μa ≤ 2 ^ (m + μb + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : 2 ^ (m + μb + 2) = 2 * 2 ^ (m + μb + 1) := by rw [pow_succ]; ring
    omega
  have hq := hQ1 (θ / 4) (by linarith) (by linarith)
  have hqq : 1 ≤ Q (θ / 4) * Q (θ / 4) := by nlinarith
  have hf0 : 0 ≤ (θ - (θ / 4 + θ / 4)) / (Q (θ / 4) * Q (θ / 4)) :=
    div_nonneg (by linarith) (by linarith)
  have hf1 : (θ - (θ / 4 + θ / 4)) / (Q (θ / 4) * Q (θ / 4)) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have hle : θ * ((θ - (θ / 4 + θ / 4)) / (Q (θ / 4) * Q (θ / 4))) ≤ 1 := by nlinarith
  have hQ0 : Q (θ / 4) ≠ 0 := (show (0 : Real) < Q (θ / 4) by linarith).ne'
  have hval : θ * ((θ - (θ / 4 + θ / 4)) / (Q (θ / 4) * Q (θ / 4))) =
      8 * (c (θ / 2) * c (θ / 2)) := by
    rw [hcQ (θ / 2), show θ / 2 / 2 = θ / 4 by ring]
    field_simp
    ring
  rw [hval] at hle ⊢
  have hcc := mul_pos hc0 hc0
  refine ⟨by linarith, hle, ?_⟩
  have hsq := pw_mul hX (inv_pos.mpr hc0).le (inv_pos.mpr hc0).le hci' hci'
  have hinv : (8 * (c (θ / 2) * c (θ / 2)))⁻¹ ≤ (c (θ / 2))⁻¹ * (c (θ / 2))⁻¹ := by
    rw [mul_inv, mul_inv]
    have h0 : 0 ≤ (c (θ / 2))⁻¹ * (c (θ / 2))⁻¹ := by positivity
    nlinarith
  exact hinv.trans hsq

variable {alpha : Real}

/-- **The common precision of the vertex covers.** -/
theorem coverPrec_gen_bounds_fejerJ (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < coverPrecW (fejerThetaOne alpha (alpha / 2) k) k ∧ coverPrecW (fejerThetaOne alpha (alpha / 2) k) k ≤ 1 ∧
      (coverPrecW (fejerThetaOne alpha (alpha / 2) k) k)⁻¹ ≤ (2 / alpha) ^ (2 ^ (pDeg k + 1)) := by
  have hX := two_div_ge_two ha ha2
  obtain ⟨h0, h1⟩ := coverPrecW_pos_le (fejerThetaOne alpha (alpha / 2) k) k (fejerThetaOne_bounds k ha (by linarith) (half_pos ha) (by linarith)).1 (fejerThetaOne_bounds k ha (by linarith) (half_pos ha) (by linarith)).2
  obtain ⟨ht0, -, hti⟩ := T2_gen_bounds_fejerW k ha ha2
  refine ⟨h0, h1, ?_⟩
  have heq : (coverPrecW (fejerThetaOne alpha (alpha / 2) k) k)⁻¹ =
      (2 : Real) ^ (k + 1) * (globalTheta2W (fejerThetaOne alpha (alpha / 2) k))⁻¹ := by
    unfold coverPrecW; rw [inv_div, div_eq_mul_inv]
  rw [heq]
  have h2 : (2 : Real) ^ (k + 1) ≤ (2 / alpha) ^ (2 ^ pDeg k) :=
    (pow_le_pow_left₀ (by norm_num) hX _).trans (pw_natpow hX (k_succ_le_two_pow_pDeg k))
  exact pw_mul hX (by positivity) (inv_pos.mpr ht0).le h2 hti

namespace GenParamsJ

variable (P : GenParamsJ) (alpha : Real)

/-- The localization parameter `η` of the step. -/
def eta : Real := singlePieceEtaFJ (fun l => uCount P.V (uDegZ l)) alpha P.k

/-- The parameter of the lower-degree bound. -/
def yIn : Real := (P.eta alpha / 2) / (2 * (P.k + 1 + 2 : Nat) : Real) ^ (P.k + 1 + 2)

/-- **The single-piece inverse step in dimension `k`, joint-cover remainder.** -/
theorem inverse_step (hV : 1 ≤ P.V) (hK : 2 ≤ P.K) (hp : 0 < P.p) (hk : 1 ≤ P.k)
    (hcov : ∀ l, 1 ≤ l → l ≤ P.k → PolyCoverAt l (uCount P.V (uDegZ l)) (uExp P.V (uDegZ l)))
    (hrec : Section16RecurrenceProfileWith P.k (familyRecThr P.k P.K P.p) (familyRecExp P.k P.p))
    {alpha : Real} (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2)
    {beta sigma T : Real}
    (hbound : FunctionDiscrepancyBound (P.k + 1) (P.yIn alpha) beta sigma T)
    (hb : 0 < beta) (hs : 0 < sigma) (hs16 : sigma ≤ 16) :
    FunctionDiscrepancyBound (P.k + 2) alpha (P.eta alpha * beta / 4)
      (inverseStepExponent (P.k + 1) (P.Eloc alpha) sigma)
      (max (shortLocalizationThreshold (P.k + 1) (P.Eloc alpha) (6 * ((P.k + 1 : Nat) : Real)) T
          (P.Tloc alpha))
        (inverseStepThreshold (P.k + 1) (P.eta alpha) beta (P.Eloc alpha)
          (6 * ((P.k + 1 : Nat) : Real)) sigma)) := by
  obtain ⟨he0, he, -⟩ := P.Eloc_pos_le hV hp ha haHalf
  have hretile : ∀ q, Section16RetiledLinearityBound P.k q (familyRecExp P.k P.p q)
      (familyRecThr P.k P.K P.p q) :=
    fun q => (hrec.retiled_family (fun q => familyRecThr_pos (by omega) q) q).single
  exact single_piece_inverse_step_global_cover_fejer_joint (Qb := fun l => uCount P.V (uDegZ l))
    (Eb := fun l => uExp P.V (uDegZ l)) hk ha haHalf hcov
    (fun l g t s _ _ => one_le_uCount P.V (uDegZ l) g t s)
    (fun l g t s _ _ => (uExp_pos_le P.V (uDegZ l) g t s).1)
    (fun l g t s _ _ => (uExp_pos_le P.V (uDegZ l) g t s).2)
    (familyRecExp P.k P.p) (familyRecThr P.k P.K P.p)
    hretile he0 he hbound hb hs hs16 (fun N _ _ hN => P.modulus_conditions hV hK hp ha haHalf N hN)

variable {alpha}

theorem rho1_pos_le (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < P.Rho1 alpha ∧ P.Rho1 alpha ≤ 1 :=
  coverRho1W_pos_le _ (fun l g t s _ _ => one_le_uCount P.V (uDegZ l) g t s) (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2)
    P.k (fejerThetaOne_bounds P.k ha (by linarith) (half_pos ha) (by linarith)).1 (fejerThetaOne_bounds P.k ha (by linarith) (half_pos ha) (by linarith)).2

/-- **One vertex count at the common precision.** -/
theorem vertex_uCount_le {μV : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) (hV : 1 ≤ P.V)
    (hVμ : P.V ≤ 2 ^ (2 ^ μV)) (hμ0 : max μV (pDeg P.k) + 2 ≤ P.μ0) {l : Nat} (hl : l ≤ P.k) :
    uCount P.V (uDegZ l) (alpha / 2) (globalBudgetW (fejerThetaOne alpha (alpha / 2) P.k) P.k)
        (coverPrecW (fejerThetaOne alpha (alpha / 2) P.k) P.k) ≤
      (2 / alpha) ^ (2 ^ (P.μ0 + 1 + tDegZ P.k)) := by
  have hX := two_div_ge_two ha ha2
  obtain ⟨hB0, hB1, hBi⟩ := budget_gen_bounds_fejerW P.k ha ha2
  obtain ⟨hs0, hs1, hsi⟩ := coverPrec_gen_bounds_fejerJ P.k ha ha2
  have hD : uDegZ l ≤ 2 ^ (tDegZ P.k) := uDegZ_le_pow hl
  have h := uCount_scale_le_deg (c := pDeg P.k + 1) hX hV hVμ (seven_le_pDeg _) hμ0 (half_pos ha) (by linarith)
    (GenParams.half_inv_le_deg (pDeg P.k) ha ha2) hB0 hB1 hBi hs0 hs1 hsi hD
  have hm : max P.μ0 (pDeg P.k + 1) = P.μ0 := by
    have := le_max_right μV (pDeg P.k)
    exact max_eq_left (by omega)
  rw [hm] at h
  exact h

/-- The log-degree of the joint-cover `ρ₁`. -/
def rhoDegJ (k μ0 : Nat) : Nat := max (tDegZ k + μ0 + 3) (pDeg k + 1) + k

theorem rhoDegJ_ge (k μ0 : Nat) :
    tDegZ k + μ0 + 3 ≤ rhoDegJ k μ0 ∧ pDeg k + 1 ≤ rhoDegJ k μ0 := by
  unfold rhoDegJ
  have h1 := le_max_left (tDegZ k + μ0 + 3) (pDeg k + 1)
  have h2 := le_max_right (tDegZ k + μ0 + 3) (pDeg k + 1)
  omega

/-- **The joint-cover density**: `ρ₁⁻¹ ≤ X^(2^rhoDegJ)`, in every dimension. -/
theorem rho1_inv_leJ {μV : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) (hV : 1 ≤ P.V)
    (hVμ : P.V ≤ 2 ^ (2 ^ μV)) (hμ0 : max μV (pDeg P.k) + 2 ≤ P.μ0) :
    (P.Rho1 alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ rhoDegJ P.k P.μ0) := by
  have hX := two_div_ge_two ha ha2
  obtain ⟨ht0, -, hti⟩ := T2_gen_bounds_fejerW P.k ha ha2
  have hf := le_max_right μV (pDeg P.k)
  have hfk : P.k + 1 ≤ pDeg P.k := by
    have := five_k_le_pDeg P.k; omega
  have hka : P.k + 2 ≤ P.μ0 + 1 + tDegZ P.k := by omega
  -- the product of the vertex counts
  have hcc : coverCountW (fun l => uCount P.V (uDegZ l)) (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2) P.k ≤
      (2 / alpha) ^ (2 ^ (P.μ0 + 1 + tDegZ P.k + P.k)) := by
    unfold coverCountW
    refine prod_le_pw _ hX (fun e _ => le_trans zero_le_one (le_trans (one_le_uCount _ _ _ _ _)
      (le_max_left _ _))) (fun e he => max_le ?_ (three_pow_le_pw hX hka)) (nonTop_card_le P.k)
    exact P.vertex_uCount_le ha ha2 hV hVμ hμ0 (nonTop_card_le_k (Finset.mem_filter.mp he).2)
  have hcc0 := coverCountW_pos (fun l => uCount P.V (uDegZ l))
    (fun l g t s _ _ => one_le_uCount P.V (uDegZ l) g t s) (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2) P.k
  have heq : (P.Rho1 alpha)⁻¹ = 2 * (globalTheta2W (fejerThetaOne alpha (alpha / 2) P.k))⁻¹ *
      coverCountW (fun l => uCount P.V (uDegZ l)) (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2) P.k := by
    show (coverRho1W (fun l => uCount P.V (uDegZ l)) (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2) P.k)⁻¹ = _
    unfold coverRho1W
    field_simp
  rw [heq]
  have h2 : 2 * (globalTheta2W (fejerThetaOne alpha (alpha / 2) P.k))⁻¹ ≤ (2 / alpha) ^ (2 ^ (pDeg P.k + 1)) :=
    pw_mul hX (by norm_num) (inv_pos.mpr ht0).le (hX.trans (pw_X hX _)) hti
  have h := pw_mul' hX (by positivity) hcc0.le h2 hcc
  refine pw_mono hX h ?_
  have h1 := rhoDegJ_ge P.k P.μ0
  have hm : max (pDeg P.k + 1) (P.μ0 + 1 + tDegZ P.k + P.k) =
      P.μ0 + 1 + tDegZ P.k + P.k := max_eq_right (by omega)
  rw [hm]
  unfold rhoDegJ
  have := le_max_left (tDegZ P.k + P.μ0 + 3) (pDeg P.k + 1)
  omega

/-- **The joint-cover width exponent.** -/
theorem nestExp_inv_leJ {μV : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) (hV : 1 ≤ P.V)
    (hVμ : P.V ≤ 2 ^ (2 ^ μV)) (hμ0 : max μV (pDeg P.k) + 2 ≤ P.μ0) :
    (P.NestExp alpha)⁻¹ ≤
      (2 / alpha) ^ (2 ^ (rhoDegJ P.k P.μ0 + tDegZ P.k + 3 + P.k)) := by
  have hX := two_div_ge_two ha ha2
  have hf := le_max_right μV (pDeg P.k)
  have hfk : P.k + 1 ≤ pDeg P.k := by
    have := five_k_le_pDeg P.k; omega
  have hka : P.k + 3 ≤ P.μ0 + 1 + tDegZ P.k := by omega
  have heq : (P.NestExp alpha)⁻¹ =
      ∏ e ∈ Finset.univ.filter (fun e : Fin P.k → Bool => e ≠ fun _ => true),
        (16 : Real) ^ (P.k + 1 - (section16VertexDirections e).card) *
          uCount P.V (uDegZ (section16VertexDirections e).card) (alpha / 2)
            (globalBudgetW (fejerThetaOne alpha (alpha / 2) P.k) P.k) (coverPrecW (fejerThetaOne alpha (alpha / 2) P.k) P.k) := by
    show (coverExpW (fun l => uExp P.V (uDegZ l)) (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2) P.k)⁻¹ = _
    unfold coverExpW
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun e _ => ?_
    unfold uExp
    rw [inv_div, div_inv_eq_mul]
  rw [heq]
  have h : ∏ e ∈ Finset.univ.filter (fun e : Fin P.k → Bool => e ≠ fun _ => true),
        (16 : Real) ^ (P.k + 1 - (section16VertexDirections e).card) *
          uCount P.V (uDegZ (section16VertexDirections e).card) (alpha / 2)
            (globalBudgetW (fejerThetaOne alpha (alpha / 2) P.k) P.k) (coverPrecW (fejerThetaOne alpha (alpha / 2) P.k) P.k) ≤
      (2 / alpha) ^ (2 ^ (P.μ0 + 1 + tDegZ P.k + 1 + P.k)) := by
    refine prod_le_pw _ hX ?_ ?_ (nonTop_card_le P.k)
    · intro e _
      exact mul_nonneg (by positivity) (zero_le_one.trans (one_le_uCount _ _ _ _ _))
    · intro e he
      have hl := nonTop_card_le_k (Finset.mem_filter.mp he).2
      have h16 := sixteen_pow_le_pw hX (k := P.k)
        (m := P.k + 1 - (section16VertexDirections e).card) (Nat.sub_le _ _)
      have hu := P.vertex_uCount_le ha ha2 hV hVμ hμ0 hl
      have hm := pw_mul' hX (by positivity) (zero_le_one.trans (one_le_uCount _ _ _ _ _)) h16 hu
      rw [max_eq_right (by omega)] at hm
      exact hm
  refine pw_mono hX h ?_
  have := rhoDegJ_ge P.k P.μ0
  omega

/-- The log-degree of the input parameter `yIn`. -/
def densDegJ (k μ0 : Nat) : Nat := rhoDegJ k μ0 + tDegZ k + 11

/-- **The input parameter of the lower-degree bound**, joint-cover remainder. -/
theorem yIn_boundsJ {μV : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (hV : 1 ≤ P.V) (hVμ : P.V ≤ 2 ^ (2 ^ μV)) (hμ0 : max μV (pDeg P.k) + 2 ≤ P.μ0) :
    0 < P.eta alpha ∧ P.eta alpha ≤ alpha / 8 ∧
      (P.eta alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ (rhoDegJ P.k P.μ0 + tDegZ P.k + 10)) ∧
      0 < P.yIn alpha ∧ P.yIn alpha ≤ alpha ∧
      (P.yIn alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ densDegJ P.k P.μ0) := by
  have hX := two_div_ge_two ha ha2
  have hri := P.rho1_inv_leJ ha ha2 hV hVμ hμ0
  set k := P.k with hkdef
  set μD := tDegZ k with hμDdef
  have hρ1 : μD + P.μ0 + 3 ≤ rhoDegJ k P.μ0 := (rhoDegJ_ge k P.μ0).1
  have hρ2 : pDeg k + 1 ≤ rhoDegJ k P.μ0 := (rhoDegJ_ge k P.μ0).2
  have hbase := baseCFW_recipPowerLB (D := uDegZ k) (k := k) ha ha2 hV hVμ hμ0
  have hD : uDegZ k ≤ 2 ^ μD := le_rfl
  have ha0 : uDegZ k * 2 ^ P.μ0 + 1 ≤ 2 ^ (μD + P.μ0 + 1) := by
    have h1 : uDegZ k * 2 ^ P.μ0 ≤ 2 ^ μD * 2 ^ P.μ0 := Nat.mul_le_mul_right _ hD
    have h2 : 2 ^ (μD + P.μ0 + 1) = 2 * (2 ^ μD * 2 ^ P.μ0) := by rw [pow_add, pow_add]; ring
    have h3 : 1 ≤ 2 ^ μD * 2 ^ P.μ0 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hb0 : uDegZ k + 1 ≤ 2 ^ (μD + 1) := by
    have : 2 ^ (μD + 1) = 2 * 2 ^ μD := by rw [pow_succ]; ring
    have := Nat.one_le_two_pow (n := μD)
    omega
  -- `ρ₁`
  obtain ⟨hr0, hr1⟩ := P.rho1_pos_le ha ha2
  -- `ρ`, `θ_S`, the density
  obtain ⟨hR0, hR1, hRi⟩ := GenParams.rho_step hX hr0 hr1 hri (by omega)
  obtain ⟨hS0, hS1, hSi⟩ := GenParams.thetaS_step hX hR0 hR1 hRi
  obtain ⟨hd0, hd1, hdi⟩ := GenParams.joint_dens_step hX hbase
    (Q := uCount P.V (uDegZ k) (alpha / 2) (globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k))
    (fun _ => rfl) (fun _ _ _ => one_le_uCount _ _ _ _ _) hS0 hS1 hSi ha0 hb0 (by omega)
  -- `η`, `yIn`
  -- the polynomial side condition of `eta_step_small`, from the class degree
  have hm : 3 * (k + 4) ^ 2 ≤ rhoDegJ k P.μ0 + 2 + 3 + (μD + 1) + 3 := by
    have h1 := sq_le_two_tDegZ k
    have h6 : tDegZ k + P.μ0 + 3 + k ≤ rhoDegJ k P.μ0 := by
      unfold rhoDegJ; have := le_max_left (tDegZ k + P.μ0 + 3) (pDeg k + 1); omega
    have h2 := le_max_right μV (pDeg k)
    have h3 : μD = tDegZ k := hμDdef
    have h5 : pDeg k = 5 * k + 21 := rfl
    omega
  obtain ⟨he0, he8, hei⟩ := GenParams.eta_step_small (k := k) ha ha2 hd0 hd1 hdi hm
  obtain ⟨hy0, hyle, hyi⟩ := GenParams.yIn_step_small (k := k) ha ha2 he0 he8 hei (by omega)
  have e1 : rhoDegJ k P.μ0 + 2 + 3 + (μD + 1) + 3 + 1 = rhoDegJ k P.μ0 + μD + 10 := by
    ring
  have e2 : rhoDegJ k P.μ0 + 2 + 3 + (μD + 1) + 3 + 1 + 1 = densDegJ k P.μ0 := by
    unfold densDegJ; ring
  rw [e1] at hei
  rw [e2] at hyi
  exact ⟨he0, he8, hei, hy0, hyle, hyi⟩

end GenParamsJ

end LeanProofs.GowersSzemeredi
