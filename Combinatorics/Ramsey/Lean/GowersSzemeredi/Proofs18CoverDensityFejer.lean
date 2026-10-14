import GowersSzemeredi.Proofs18CoverDensity
import GowersSzemeredi.Proofs18CoverModulusFejer

/-! **The density envelope of the Section 18 step under the Fejér θ₁**
(Notes L.16d).

The Fejér instance of `Proofs18CoverDensity` (generated; no printed parameter
survives). The log-degrees are the corpus's with the class degree
`23·2^k` in place of `68·2^k`:
* `rhoDegF k μ₀ = max(23·2^k + μ₀ + 3, fixDeg k + 1) + k` (`rho1_inv_leF`);
* `densDegF k μ₀ = rhoDegF k μ₀ + 2·(23·2^k) + 13` (`yIn_boundsF`). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

variable {alpha : Real}

/-- **The common precision of the vertex covers.** -/
theorem coverPrec_gen_bounds_fejer (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < coverPrecW (fejerThetaOne alpha (alpha / 2) k) k ∧ coverPrecW (fejerThetaOne alpha (alpha / 2) k) k ≤ 1 ∧
      (coverPrecW (fejerThetaOne alpha (alpha / 2) k) k)⁻¹ ≤ (2 / alpha) ^ (2 ^ (fixDeg k + 1)) := by
  have hX := two_div_ge_two ha ha2
  obtain ⟨h0, h1⟩ := coverPrecW_pos_le (fejerThetaOne alpha (alpha / 2) k) k (fejerThetaOne_bounds k ha (by linarith) (half_pos ha) (by linarith)).1 (fejerThetaOne_bounds k ha (by linarith) (half_pos ha) (by linarith)).2
  obtain ⟨ht0, -, hti⟩ := T2_gen_bounds_fejer k ha ha2
  refine ⟨h0, h1, ?_⟩
  have heq : (coverPrecW (fejerThetaOne alpha (alpha / 2) k) k)⁻¹ =
      (2 : Real) ^ (k + 1) * (globalTheta2W (fejerThetaOne alpha (alpha / 2) k))⁻¹ := by
    unfold coverPrecW; rw [inv_div, div_eq_mul_inv]
  rw [heq]
  have h2 : (2 : Real) ^ (k + 1) ≤ (2 / alpha) ^ (2 ^ fixDeg k) :=
    (pow_le_pow_left₀ (by norm_num) hX _).trans (pw_natpow hX (k_succ_le_two_pow_fixDeg k))
  exact pw_mul hX (inv_pos.mpr ht0).le h2 hti

namespace GenParamsF

variable (P : GenParamsF) (alpha : Real)

/-- The localization parameter `η` of the step. -/
def eta : Real := singlePieceEtaF (fun l => uCount P.V (uDeg23 l)) alpha P.k

/-- The parameter of the lower-degree bound. -/
def yIn : Real := (P.eta alpha / 2) / (2 * (P.k + 1 + 2 : Nat) : Real) ^ (P.k + 1 + 2)

/-- **The single-piece inverse step in dimension `k`, joint-cover remainder.** -/
theorem inverse_step (hV : 1 ≤ P.V) (hK : 2 ≤ P.K) (hp : 0 < P.p) (hk : 1 ≤ P.k)
    (hcov : ∀ l, 1 ≤ l → l ≤ P.k → PolyCoverAt l (uCount P.V (uDeg23 l)) (uExp P.V (uDeg23 l)))
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
  exact single_piece_inverse_step_global_cover_fejer (Qb := fun l => uCount P.V (uDeg23 l))
    (Eb := fun l => uExp P.V (uDeg23 l)) hk ha haHalf hcov
    (fun l g t s _ _ => one_le_uCount P.V (uDeg23 l) g t s)
    (fun l g t s _ _ => (uExp_pos_le P.V (uDeg23 l) g t s).1)
    (fun l g t s _ _ => (uExp_pos_le P.V (uDeg23 l) g t s).2)
    (familyRecExp P.k P.p) (familyRecThr P.k P.K P.p)
    hretile he0 he hbound hb hs hs16 (fun N _ _ hN => P.modulus_conditions hV hK hp ha haHalf N hN)

variable {alpha}

theorem rho1_pos_le (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < P.Rho1 alpha ∧ P.Rho1 alpha ≤ 1 :=
  coverRho1W_pos_le _ (fun l g t s _ _ => one_le_uCount P.V (uDeg23 l) g t s) (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2)
    P.k (fejerThetaOne_bounds P.k ha (by linarith) (half_pos ha) (by linarith)).1 (fejerThetaOne_bounds P.k ha (by linarith) (half_pos ha) (by linarith)).2

/-- **One vertex count at the common precision.** -/
theorem vertex_uCount_le {μV : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) (hV : 1 ≤ P.V)
    (hVμ : P.V ≤ 2 ^ (2 ^ μV)) (hμ0 : max μV (fixDeg P.k) + 2 ≤ P.μ0) {l : Nat} (hl : l ≤ P.k) :
    uCount P.V (uDeg23 l) (alpha / 2) (globalBudgetW (fejerThetaOne alpha (alpha / 2) P.k) P.k)
        (coverPrecW (fejerThetaOne alpha (alpha / 2) P.k) P.k) ≤
      (2 / alpha) ^ (2 ^ (P.μ0 + 1 + 23 * 2 ^ P.k)) := by
  have hX := two_div_ge_two ha ha2
  obtain ⟨hB0, hB1, hBi⟩ := budget_gen_bounds_fejer P.k ha ha2
  obtain ⟨hs0, hs1, hsi⟩ := coverPrec_gen_bounds_fejer P.k ha ha2
  have hD : uDeg23 l ≤ 2 ^ (23 * 2 ^ P.k) := Nat.pow_le_pow_right (by norm_num)
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hl))
  have h := uCount_scale_le (c := fixDeg P.k + 1) hX hV hVμ hμ0 (half_pos ha) (by linarith)
    (GenParams.half_inv_le P.k ha ha2) hB0 hB1 hBi hs0 hs1 hsi hD
  have hm : max P.μ0 (fixDeg P.k + 1) = P.μ0 := by
    have := le_max_right μV (fixDeg P.k)
    exact max_eq_left (by omega)
  rw [hm] at h
  exact h

/-- The log-degree of the joint-cover `ρ₁`. -/
def rhoDegF (k μ0 : Nat) : Nat := max (23 * 2 ^ k + μ0 + 3) (fixDeg k + 1) + k

theorem rhoDegC_gF (k μ0 : Nat) :
    23 * 2 ^ k + μ0 + 3 ≤ rhoDegF k μ0 ∧ fixDeg k + 1 ≤ rhoDegF k μ0 := by
  unfold rhoDegF
  have h1 := le_max_left (23 * 2 ^ k + μ0 + 3) (fixDeg k + 1)
  have h2 := le_max_right (23 * 2 ^ k + μ0 + 3) (fixDeg k + 1)
  omega

/-- **The joint-cover density**: `ρ₁⁻¹ ≤ X^(2^rhoDegF)`, in every dimension. -/
theorem rho1_inv_leF {μV : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) (hV : 1 ≤ P.V)
    (hVμ : P.V ≤ 2 ^ (2 ^ μV)) (hμ0 : max μV (fixDeg P.k) + 2 ≤ P.μ0) :
    (P.Rho1 alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ rhoDegF P.k P.μ0) := by
  have hX := two_div_ge_two ha ha2
  obtain ⟨ht0, -, hti⟩ := T2_gen_bounds_fejer P.k ha ha2
  have hf := le_max_right μV (fixDeg P.k)
  have hfk : P.k + 1 ≤ fixDeg P.k := by
    unfold fixDeg; have := Nat.lt_two_pow_self (n := P.k + 5); omega
  have hka : P.k + 2 ≤ P.μ0 + 1 + 23 * 2 ^ P.k := by omega
  -- the product of the vertex counts
  have hcc : coverCountW (fun l => uCount P.V (uDeg23 l)) (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2) P.k ≤
      (2 / alpha) ^ (2 ^ (P.μ0 + 1 + 23 * 2 ^ P.k + P.k)) := by
    unfold coverCountW
    refine prod_le_pw _ hX (fun e _ => le_trans zero_le_one (le_trans (one_le_uCount _ _ _ _ _)
      (le_max_left _ _))) (fun e he => max_le ?_ (three_pow_le_pw hX hka)) (nonTop_card_le P.k)
    exact P.vertex_uCount_le ha ha2 hV hVμ hμ0 (nonTop_card_le_k (Finset.mem_filter.mp he).2)
  have hcc0 := coverCountW_pos (fun l => uCount P.V (uDeg23 l))
    (fun l g t s _ _ => one_le_uCount P.V (uDeg23 l) g t s) (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2) P.k
  have heq : (P.Rho1 alpha)⁻¹ = 2 * (globalTheta2W (fejerThetaOne alpha (alpha / 2) P.k))⁻¹ *
      coverCountW (fun l => uCount P.V (uDeg23 l)) (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2) P.k := by
    show (coverRho1W (fun l => uCount P.V (uDeg23 l)) (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2) P.k)⁻¹ = _
    unfold coverRho1W
    field_simp
  rw [heq]
  have h2 : 2 * (globalTheta2W (fejerThetaOne alpha (alpha / 2) P.k))⁻¹ ≤ (2 / alpha) ^ (2 ^ (fixDeg P.k + 1)) :=
    pw_mul hX (inv_pos.mpr ht0).le (hX.trans (pw_X hX _)) hti
  have h := pw_mul' hX (by positivity) hcc0.le h2 hcc
  refine pw_mono hX h ?_
  have hm : max (fixDeg P.k + 1) (P.μ0 + 1 + 23 * 2 ^ P.k + P.k) =
      P.μ0 + 1 + 23 * 2 ^ P.k + P.k := max_eq_right (by omega)
  rw [hm]
  unfold rhoDegF
  have := le_max_left (23 * 2 ^ P.k + P.μ0 + 3) (fixDeg P.k + 1)
  omega

/-- **The joint-cover width exponent.** -/
theorem nestExp_inv_leF {μV : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) (hV : 1 ≤ P.V)
    (hVμ : P.V ≤ 2 ^ (2 ^ μV)) (hμ0 : max μV (fixDeg P.k) + 2 ≤ P.μ0) :
    (P.NestExp alpha)⁻¹ ≤
      (2 / alpha) ^ (2 ^ (rhoDegF P.k P.μ0 + 23 * 2 ^ P.k + 3 + P.k)) := by
  have hX := two_div_ge_two ha ha2
  have hf := le_max_right μV (fixDeg P.k)
  have hfk : P.k + 1 ≤ fixDeg P.k := by
    unfold fixDeg; have := Nat.lt_two_pow_self (n := P.k + 5); omega
  have hka : P.k + 3 ≤ P.μ0 + 1 + 23 * 2 ^ P.k := by omega
  refine pw_mono hX (a := P.μ0 + 1 + 23 * 2 ^ P.k + 1 + P.k) ?_ ?_
  · unfold NestExp coverExpW
    rw [← Finset.prod_inv_distrib]
    simp only [uExp, inv_div, div_inv_eq_mul]
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
  · have := rhoDegC_gF P.k P.μ0
    omega

/-- The log-degree of the input parameter `yIn`. -/
def densDegF (k μ0 : Nat) : Nat := rhoDegF k μ0 + 2 * (23 * 2 ^ k) + 13

/-- **The input parameter of the lower-degree bound**, joint-cover remainder. -/
theorem yIn_boundsF {μV : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (hV : 1 ≤ P.V) (hVμ : P.V ≤ 2 ^ (2 ^ μV)) (hμ0 : max μV (fixDeg P.k) + 2 ≤ P.μ0) :
    0 < P.eta alpha ∧ P.eta alpha ≤ alpha / 8 ∧
      (P.eta alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ (rhoDegF P.k P.μ0 + 2 * (23 * 2 ^ P.k) + 12)) ∧
      0 < P.yIn alpha ∧ P.yIn alpha ≤ alpha ∧
      (P.yIn alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ densDegF P.k P.μ0) := by
  have hX := two_div_ge_two ha ha2
  have hri := P.rho1_inv_leF ha ha2 hV hVμ hμ0
  set k := P.k
  set μD := 23 * 2 ^ k
  have hρ1 : μD + P.μ0 + 3 ≤ rhoDegF k P.μ0 := (rhoDegC_gF k P.μ0).1
  have hρ2 : fixDeg k + 1 ≤ rhoDegF k P.μ0 := (rhoDegC_gF k P.μ0).2
  have hbase := baseCF_recipPowerLB (D := uDeg23 k) (k := k) ha ha2 hV hVμ hμ0
  have hD : uDeg23 k ≤ 2 ^ μD := le_rfl
  have ha0 : uDeg23 k * 2 ^ P.μ0 + 1 ≤ 2 ^ (μD + P.μ0 + 1) := by
    have h1 : uDeg23 k * 2 ^ P.μ0 ≤ 2 ^ μD * 2 ^ P.μ0 := Nat.mul_le_mul_right _ hD
    have h2 : 2 ^ (μD + P.μ0 + 1) = 2 * (2 ^ μD * 2 ^ P.μ0) := by rw [pow_add, pow_add]; ring
    have h3 : 1 ≤ 2 ^ μD * 2 ^ P.μ0 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hb0 : uDeg23 k + 1 ≤ 2 ^ (μD + 1) := by
    have : 2 ^ (μD + 1) = 2 * 2 ^ μD := by rw [pow_succ]; ring
    have := Nat.one_le_two_pow (n := μD)
    omega
  -- `ρ₁`
  obtain ⟨hr0, hr1⟩ := P.rho1_pos_le ha ha2
  -- `ρ`, `θ_S`, the density
  obtain ⟨hR0, hR1, hRi⟩ := GenParams.rho_step hX hr0 hr1 hri (by omega)
  obtain ⟨hS0, hS1, hSi⟩ := GenParams.thetaS_step hX hR0 hR1 hRi
  obtain ⟨hd0, hd1, hdi⟩ := GenParams.dens_step hX hbase hS0 hS1 hSi ha0 hb0 (by omega)
  -- `η`, `yIn`
  have hm : fixDeg k ≤ rhoDegF k P.μ0 + 2 + 3 + 2 * (μD + 1) + 4 := by omega
  obtain ⟨he0, he8, hei⟩ := GenParams.eta_step (k := k) ha ha2 hd0 hd1 hdi hm
  obtain ⟨hy0, hyle, hyi⟩ := GenParams.yIn_step (k := k) ha ha2 he0 he8 hei (by omega)
  have e1 : rhoDegF k P.μ0 + 2 + 3 + 2 * (μD + 1) + 4 + 1 = rhoDegF k P.μ0 + 2 * μD + 12 := by
    ring
  have e2 : rhoDegF k P.μ0 + 2 + 3 + 2 * (μD + 1) + 4 + 1 + 1 = densDegF k P.μ0 := by
    unfold densDegF; ring
  rw [e1] at hei
  rw [e2] at hyi
  exact ⟨he0, he8, hei, hy0, hyle, hyi⟩

end GenParamsF

end LeanProofs.GowersSzemeredi
