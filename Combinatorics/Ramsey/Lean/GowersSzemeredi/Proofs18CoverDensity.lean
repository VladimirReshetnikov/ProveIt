import GowersSzemeredi.Proofs18CoverModulus
import GowersSzemeredi.Proofs18GenericDensity
import GowersSzemeredi.Proofs18GenericExponents

/-! The density envelope of the single-piece step with the joint-cover
remainder (Notes L.12).

* `GenParamsC.inverse_step`: `single_piece_inverse_step_global_cover` for the
  parameters `GenParamsC`, with the covers at degree `uDeg68 l` in face
  dimension `l`.
* `vertex_uCount_le`: every vertex count at the common precision
  `coverPrec` is at most `X^(2^(μ₀ + 1 + 68·2^k))`, where `X = 2/α`.
* `rho1_inv_leC`: `ρ₁⁻¹ ≤ X^(2^rhoDegC)` with
  `rhoDegC k μ₀ = max(68·2^k + μ₀ + 3, fixDeg k + 1) + k`.
  The product over the `2^k − 1` vertices costs only `+ k` in the
  log-degree, where the graded nest cost `136·3^k + 2^k − 136·2^k − 1`.
* `nestExp_inv_leC`: the same for the width exponent `coverExp`.
* `yIn_boundsC`: the input parameter of the lower-degree bound.
No bound on `k` is needed anywhere (the graded chain needed `k + 1 ≤ 2^68`). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A product of `≤ 2^c` factors, each at most `X^(2^a)`, is at most `X^(2^(a+c))`. -/
theorem prod_le_pw {ι : Type*} (s : Finset ι) {X : Real} (hX : 2 ≤ X) {f : ι → Real} {a c : Nat}
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ X ^ (2 ^ a)) (hs : s.card ≤ 2 ^ c) :
    ∏ i ∈ s, f i ≤ X ^ (2 ^ (a + c)) := by
  calc ∏ i ∈ s, f i ≤ ∏ _i ∈ s, X ^ (2 ^ a) := Finset.prod_le_prod h0 h
    _ = (X ^ (2 ^ a)) ^ s.card := Finset.prod_const _
    _ ≤ X ^ (2 ^ (a + c)) := pw_pow hX (zero_le_one.trans (one_le_pw hX a)) le_rfl hs

theorem nonTop_card_le (k : Nat) :
    (Finset.univ.filter (fun e : Fin k → Bool => e ≠ fun _ => true)).card ≤ 2 ^ k := by
  rw [nonTopVertices_card]; exact Nat.sub_le _ _

theorem nonTop_card_le_k {k : Nat} {e : Fin k → Bool} (he : e ≠ fun _ => true) :
    (section16VertexDirections e).card ≤ k := by
  have := section16VertexDirections_card_lt he
  omega

theorem k_succ_le_two_pow_fixDeg (k : Nat) : k + 1 ≤ 2 ^ fixDeg k := by
  have h1 := Nat.lt_two_pow_self (n := k + 1)
  have h2 : 2 ^ (k + 1) ≤ 2 ^ fixDeg k := Nat.pow_le_pow_right (by norm_num) (by
    unfold fixDeg; have := Nat.lt_two_pow_self (n := k + 5); omega)
  omega

variable {alpha : Real}

/-- **The common precision of the vertex covers.** -/
theorem coverPrec_gen_bounds (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < coverPrec alpha (alpha / 2) k ∧ coverPrec alpha (alpha / 2) k ≤ 1 ∧
      (coverPrec alpha (alpha / 2) k)⁻¹ ≤ (2 / alpha) ^ (2 ^ (fixDeg k + 1)) := by
  have hX := two_div_ge_two ha ha2
  obtain ⟨h0, h1⟩ := coverPrec_pos_le alpha (alpha / 2) k ha (by linarith) (half_pos ha)
    (by linarith)
  obtain ⟨ht0, -, hti⟩ := T2_gen_bounds k ha ha2
  refine ⟨h0, h1, ?_⟩
  have heq : (coverPrec alpha (alpha / 2) k)⁻¹ =
      (2 : Real) ^ (k + 1) * (globalTheta2 alpha (alpha / 2) k)⁻¹ := by
    unfold coverPrec; rw [inv_div, div_eq_mul_inv]
  rw [heq]
  have h2 : (2 : Real) ^ (k + 1) ≤ (2 / alpha) ^ (2 ^ fixDeg k) :=
    (pow_le_pow_left₀ (by norm_num) hX _).trans (pw_natpow hX (k_succ_le_two_pow_fixDeg k))
  exact pw_mul hX (by positivity) (inv_pos.mpr ht0).le h2 hti

/-- `3^(k+1) ≤ X^(2^a)` once `k + 2 ≤ a`. -/
theorem three_pow_le_pw {X : Real} (hX : 2 ≤ X) {k a : Nat} (hka : k + 2 ≤ a) :
    (((3 ^ (k + 1) : Nat) : Real)) ≤ X ^ (2 ^ a) := by
  refine pw_const hX ?_
  have h1 : 3 ^ (k + 1) ≤ 4 ^ (k + 1) := Nat.pow_le_pow_left (by norm_num) _
  have h2 : (4 : Nat) ^ (k + 1) = 2 ^ (2 * (k + 1)) := by
    rw [pow_mul]; norm_num
  have h3 : 2 * (k + 1) ≤ 2 ^ a := by
    have := Nat.lt_two_pow_self (n := k)
    have h4 : 2 ^ (k + 2) ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hka
    have h5 : 2 ^ (k + 2) = 4 * 2 ^ k := by rw [pow_add]; ring
    omega
  have h6 : 3 ^ (k + 1) ≤ 2 ^ (2 ^ a) :=
    h1.trans (h2 ▸ Nat.pow_le_pow_right (by norm_num) h3)
  exact_mod_cast h6

/-- `16^m ≤ X^(2^(k+3))` for `m ≤ k + 1`. -/
theorem sixteen_pow_le_pw {X : Real} (hX : 2 ≤ X) {k m : Nat} (hm : m ≤ k + 1) :
    (16 : Real) ^ m ≤ X ^ (2 ^ (k + 3)) := by
  refine pw_const hX ?_
  have h1 : (16 : Real) ^ m = 2 ^ (4 * m) := by rw [pow_mul]; norm_num
  rw [h1]
  refine pow_le_pow_right₀ (by norm_num) ?_
  have := Nat.lt_two_pow_self (n := k)
  have h5 : 2 ^ (k + 3) = 8 * 2 ^ k := by rw [pow_add]; ring
  omega

namespace GenParamsC

variable (P : GenParamsC) (alpha : Real)

/-- The localization parameter `η` of the step. -/
def eta : Real := singlePieceEtaC (fun l => uCount P.V (uDeg68 l)) alpha P.k

/-- The parameter of the lower-degree bound. -/
def yIn : Real := (P.eta alpha / 2) / (2 * (P.k + 1 + 2 : Nat) : Real) ^ (P.k + 1 + 2)

/-- **The single-piece inverse step in dimension `k`, joint-cover remainder.** -/
theorem inverse_step (hV : 1 ≤ P.V) (hK : 2 ≤ P.K) (hp : 0 < P.p) (hk : 1 ≤ P.k)
    (hcov : ∀ l, 1 ≤ l → l ≤ P.k → PolyCoverAt l (uCount P.V (uDeg68 l)) (uExp P.V (uDeg68 l)))
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
  exact single_piece_inverse_step_global_cover (Qb := fun l => uCount P.V (uDeg68 l))
    (Eb := fun l => uExp P.V (uDeg68 l)) hk ha haHalf hcov
    (fun l g t s _ _ => one_le_uCount P.V (uDeg68 l) g t s)
    (fun l g t s _ _ => (uExp_pos_le P.V (uDeg68 l) g t s).1)
    (fun l g t s _ _ => (uExp_pos_le P.V (uDeg68 l) g t s).2)
    (familyRecExp P.k P.p) (familyRecThr P.k P.K P.p)
    hretile he0 he hbound hb hs hs16 (fun N _ _ hN => P.modulus_conditions hV hK hp ha haHalf N hN)

variable {alpha}

theorem rho1_pos_le (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < P.Rho1 alpha ∧ P.Rho1 alpha ≤ 1 :=
  coverRho1_pos_le _ (fun l g t s _ _ => one_le_uCount P.V (uDeg68 l) g t s) alpha (alpha / 2)
    P.k ha (by linarith) (half_pos ha) (by linarith)

/-- **One vertex count at the common precision.** -/
theorem vertex_uCount_le {μV : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) (hV : 1 ≤ P.V)
    (hVμ : P.V ≤ 2 ^ (2 ^ μV)) (hμ0 : max μV (fixDeg P.k) + 2 ≤ P.μ0) {l : Nat} (hl : l ≤ P.k) :
    uCount P.V (uDeg68 l) (alpha / 2) (globalBudget alpha (alpha / 2) P.k)
        (coverPrec alpha (alpha / 2) P.k) ≤
      (2 / alpha) ^ (2 ^ (P.μ0 + 1 + 68 * 2 ^ P.k)) := by
  have hX := two_div_ge_two ha ha2
  obtain ⟨hB0, hB1, hBi⟩ := budget_gen_bounds P.k ha ha2
  obtain ⟨hs0, hs1, hsi⟩ := coverPrec_gen_bounds P.k ha ha2
  have hD : uDeg68 l ≤ 2 ^ (68 * 2 ^ P.k) := Nat.pow_le_pow_right (by norm_num)
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hl))
  have h := uCount_scale_le (c := fixDeg P.k + 1) hX hV hVμ hμ0 (half_pos ha) (by linarith)
    (GenParams.half_inv_le P.k ha ha2) hB0 hB1 hBi hs0 hs1 hsi hD
  have hm : max P.μ0 (fixDeg P.k + 1) = P.μ0 := by
    have := le_max_right μV (fixDeg P.k)
    exact max_eq_left (by omega)
  rw [hm] at h
  exact h

/-- The log-degree of the joint-cover `ρ₁`. -/
def rhoDegC (k μ0 : Nat) : Nat := max (68 * 2 ^ k + μ0 + 3) (fixDeg k + 1) + k

theorem rhoDegC_ge (k μ0 : Nat) :
    68 * 2 ^ k + μ0 + 3 ≤ rhoDegC k μ0 ∧ fixDeg k + 1 ≤ rhoDegC k μ0 := by
  unfold rhoDegC
  have h1 := le_max_left (68 * 2 ^ k + μ0 + 3) (fixDeg k + 1)
  have h2 := le_max_right (68 * 2 ^ k + μ0 + 3) (fixDeg k + 1)
  omega

/-- **The joint-cover density**: `ρ₁⁻¹ ≤ X^(2^rhoDegC)`, in every dimension. -/
theorem rho1_inv_leC {μV : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) (hV : 1 ≤ P.V)
    (hVμ : P.V ≤ 2 ^ (2 ^ μV)) (hμ0 : max μV (fixDeg P.k) + 2 ≤ P.μ0) :
    (P.Rho1 alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ rhoDegC P.k P.μ0) := by
  have hX := two_div_ge_two ha ha2
  obtain ⟨ht0, -, hti⟩ := T2_gen_bounds P.k ha ha2
  have hf := le_max_right μV (fixDeg P.k)
  have hfk : P.k + 1 ≤ fixDeg P.k := by
    unfold fixDeg; have := Nat.lt_two_pow_self (n := P.k + 5); omega
  have hka : P.k + 2 ≤ P.μ0 + 1 + 68 * 2 ^ P.k := by omega
  -- the product of the vertex counts
  have hcc : coverCount (fun l => uCount P.V (uDeg68 l)) alpha (alpha / 2) P.k ≤
      (2 / alpha) ^ (2 ^ (P.μ0 + 1 + 68 * 2 ^ P.k + P.k)) := by
    unfold coverCount
    refine prod_le_pw _ hX (fun e _ => le_trans zero_le_one (le_trans (one_le_uCount _ _ _ _ _)
      (le_max_left _ _))) (fun e he => max_le ?_ (three_pow_le_pw hX hka)) (nonTop_card_le P.k)
    exact P.vertex_uCount_le ha ha2 hV hVμ hμ0 (nonTop_card_le_k (Finset.mem_filter.mp he).2)
  have hcc0 := coverCount_pos (fun l => uCount P.V (uDeg68 l))
    (fun l g t s _ _ => one_le_uCount P.V (uDeg68 l) g t s) alpha (alpha / 2) P.k
  have heq : (P.Rho1 alpha)⁻¹ = 2 * (globalTheta2 alpha (alpha / 2) P.k)⁻¹ *
      coverCount (fun l => uCount P.V (uDeg68 l)) alpha (alpha / 2) P.k := by
    show (coverRho1 (fun l => uCount P.V (uDeg68 l)) alpha (alpha / 2) P.k)⁻¹ = _
    unfold coverRho1
    field_simp
  rw [heq]
  have h2 : 2 * (globalTheta2 alpha (alpha / 2) P.k)⁻¹ ≤ (2 / alpha) ^ (2 ^ (fixDeg P.k + 1)) :=
    pw_mul hX (by norm_num) (inv_pos.mpr ht0).le (hX.trans (pw_X hX _)) hti
  have h := pw_mul' hX (by positivity) hcc0.le h2 hcc
  refine pw_mono hX h ?_
  have h1 := rhoDegC_ge P.k P.μ0
  have hm : max (fixDeg P.k + 1) (P.μ0 + 1 + 68 * 2 ^ P.k + P.k) =
      P.μ0 + 1 + 68 * 2 ^ P.k + P.k := max_eq_right (by omega)
  rw [hm]
  unfold rhoDegC
  have := le_max_left (68 * 2 ^ P.k + P.μ0 + 3) (fixDeg P.k + 1)
  omega

/-- **The joint-cover width exponent.** -/
theorem nestExp_inv_leC {μV : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) (hV : 1 ≤ P.V)
    (hVμ : P.V ≤ 2 ^ (2 ^ μV)) (hμ0 : max μV (fixDeg P.k) + 2 ≤ P.μ0) :
    (P.NestExp alpha)⁻¹ ≤
      (2 / alpha) ^ (2 ^ (rhoDegC P.k P.μ0 + 68 * 2 ^ P.k + 3 + P.k)) := by
  have hX := two_div_ge_two ha ha2
  have hf := le_max_right μV (fixDeg P.k)
  have hfk : P.k + 1 ≤ fixDeg P.k := by
    unfold fixDeg; have := Nat.lt_two_pow_self (n := P.k + 5); omega
  have hka : P.k + 3 ≤ P.μ0 + 1 + 68 * 2 ^ P.k := by omega
  have heq : (P.NestExp alpha)⁻¹ =
      ∏ e ∈ Finset.univ.filter (fun e : Fin P.k → Bool => e ≠ fun _ => true),
        (16 : Real) ^ (P.k + 1 - (section16VertexDirections e).card) *
          uCount P.V (uDeg68 (section16VertexDirections e).card) (alpha / 2)
            (globalBudget alpha (alpha / 2) P.k) (coverPrec alpha (alpha / 2) P.k) := by
    show (coverExp (fun l => uExp P.V (uDeg68 l)) alpha (alpha / 2) P.k)⁻¹ = _
    unfold coverExp
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun e _ => ?_
    unfold uExp
    rw [inv_div, div_inv_eq_mul]
  rw [heq]
  have h : ∏ e ∈ Finset.univ.filter (fun e : Fin P.k → Bool => e ≠ fun _ => true),
        (16 : Real) ^ (P.k + 1 - (section16VertexDirections e).card) *
          uCount P.V (uDeg68 (section16VertexDirections e).card) (alpha / 2)
            (globalBudget alpha (alpha / 2) P.k) (coverPrec alpha (alpha / 2) P.k) ≤
      (2 / alpha) ^ (2 ^ (P.μ0 + 1 + 68 * 2 ^ P.k + 1 + P.k)) := by
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
  have := rhoDegC_ge P.k P.μ0
  omega

/-- The log-degree of the input parameter `yIn`. -/
def densDegC (k μ0 : Nat) : Nat := rhoDegC k μ0 + 2 * (68 * 2 ^ k) + 13

/-- **The input parameter of the lower-degree bound**, joint-cover remainder. -/
theorem yIn_boundsC {μV : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (hV : 1 ≤ P.V) (hVμ : P.V ≤ 2 ^ (2 ^ μV)) (hμ0 : max μV (fixDeg P.k) + 2 ≤ P.μ0) :
    0 < P.eta alpha ∧ P.eta alpha ≤ alpha / 8 ∧
      (P.eta alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ (rhoDegC P.k P.μ0 + 2 * (68 * 2 ^ P.k) + 12)) ∧
      0 < P.yIn alpha ∧ P.yIn alpha ≤ alpha ∧
      (P.yIn alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ densDegC P.k P.μ0) := by
  have hX := two_div_ge_two ha ha2
  have hri := P.rho1_inv_leC ha ha2 hV hVμ hμ0
  set k := P.k with hkdef
  set μD := 68 * 2 ^ k with hμDdef
  have hρ1 : μD + P.μ0 + 3 ≤ rhoDegC k P.μ0 := (rhoDegC_ge k P.μ0).1
  have hρ2 : fixDeg k + 1 ≤ rhoDegC k P.μ0 := (rhoDegC_ge k P.μ0).2
  have hbase := GenParams.baseC_recipPowerLB (D := uDeg68 k) (K := P.K) (p := P.p) ha ha2 hV hVμ hμ0
  have hD : uDeg68 k ≤ 2 ^ μD := le_rfl
  have ha0 : uDeg68 k * 2 ^ P.μ0 + 1 ≤ 2 ^ (μD + P.μ0 + 1) := by
    have h1 : uDeg68 k * 2 ^ P.μ0 ≤ 2 ^ μD * 2 ^ P.μ0 := Nat.mul_le_mul_right _ hD
    have h2 : 2 ^ (μD + P.μ0 + 1) = 2 * (2 ^ μD * 2 ^ P.μ0) := by rw [pow_add, pow_add]; ring
    have h3 : 1 ≤ 2 ^ μD * 2 ^ P.μ0 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hb0 : uDeg68 k + 1 ≤ 2 ^ (μD + 1) := by
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
  have hm : fixDeg k ≤ rhoDegC k P.μ0 + 2 + 3 + 2 * (μD + 1) + 4 := by omega
  obtain ⟨he0, he8, hei⟩ := GenParams.eta_step (k := k) ha ha2 hd0 hd1 hdi hm
  obtain ⟨hy0, hyle, hyi⟩ := GenParams.yIn_step (k := k) ha ha2 he0 he8 hei (by omega)
  have e1 : rhoDegC k P.μ0 + 2 + 3 + 2 * (μD + 1) + 4 + 1 = rhoDegC k P.μ0 + 2 * μD + 12 := by
    ring
  have e2 : rhoDegC k P.μ0 + 2 + 3 + 2 * (μD + 1) + 4 + 1 + 1 = densDegC k P.μ0 := by
    unfold densDegC; ring
  rw [e1] at hei
  rw [e2] at hyi
  exact ⟨he0, he8, hei, hy0, hyle, hyi⟩

end GenParamsC

end LeanProofs.GowersSzemeredi
