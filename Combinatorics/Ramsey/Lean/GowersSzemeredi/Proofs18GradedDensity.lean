import GowersSzemeredi.Proofs18GradedModulus
import GowersSzemeredi.Proofs18GenericDensity
import GowersSzemeredi.Proofs16VertexWeightCounts

/-! The graded single-piece step and its density envelope (Notes L.10, G4b–c).

* `GenParamsG.inverse_step`: `single_piece_inverse_step_global_graded` for
  the graded parameters. The covers come from the face-dimension classes, at
  degree `uDeg l` in face dimension `l`.
* `gradedNestC_genC`: the graded nest of `genC` blocks is `X^(−A)·t^B`,
  with `B = Π_j b_j^(n_j)` and `A ≤ (Σ_j a_j)·B`.
* `rho1_inv_leG`: `ρ₁⁻¹ ≤ X^(2^rhoDegG)`, where
  `rhoDegG k μ₀ = max(76·2^k + μ₀ + 2, fixDeg k) + k + 1 + 152·3^k + 2^k`.
  The uniform `rhoDeg` has `(76·2^k + 1)(2^k − 1)` in place of
  `152·3^k + 2^k`.
* `yIn_boundsG`: the input parameter of the lower-degree bound. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-! ### The graded nest of closed-form densities -/

/-- The `X`-exponent of the graded nest. -/
def gradedA (a b n : Nat → Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => a j * geomSum (b j) (n j) + b j ^ (n j) * gradedA a b n j

/-- The `t`-exponent of the graded nest. -/
def gradedB (b n : Nat → Nat) : Nat → Nat
  | 0 => 1
  | j + 1 => b j ^ (n j) * gradedB b n j

/-- **The graded nest of `genC` blocks.** -/
theorem gradedNestC_genC {X : Real} (hX : 1 ≤ X) (a b : Nat → Nat) (c : Nat → Real → Real)
    (k : Nat) (n : Nat → Nat) :
    ∀ K t, 0 < t → t ≤ 1 →
      gradedNestC (fun l => genC X (a l) (b l) (c l) k) n K t =
        (X ^ gradedA a b n K)⁻¹ * t ^ gradedB b n K := by
  intro K
  induction K with
  | zero => intro t _ _; simp [gradedNestC, gradedA, gradedB]
  | succ K ih =>
    intro t ht ht1
    obtain ⟨h0, h1⟩ := gradedNestC_pos_le
      (fun l => genC_pos_le hX (a l) (b l) (c l) k) n K t ht ht1
    show nestC (fun _ => genC X (a K) (b K) (c K) k) (n K)
      (gradedNestC (fun l => genC X (a l) (b l) (c l) k) n K t) = _
    rw [nestC_genC hX (a K) (b K) (c K) k (n K) _ h0 h1, ih t ht ht1]
    simp only [gradedA, gradedB]
    rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, pow_add, mul_inv,
      mul_comm (gradedA a b n K) (b K ^ n K), mul_comm (gradedB b n K) (b K ^ n K)]
    ring

theorem gradedB_pos (b n : Nat → Nat) (hb : ∀ j, 1 ≤ b j) : ∀ K, 1 ≤ gradedB b n K := by
  intro K
  induction K with
  | zero => exact le_rfl
  | succ K ih => exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
      (pow_ne_zero _ (by have := hb K; omega)) (by omega))

/-- `A ≤ (Σ_{j<K} a_j)·B` once every `b_j ≥ 2`. -/
theorem gradedA_le (a b n : Nat → Nat) (hb : ∀ j, 2 ≤ b j) :
    ∀ K, gradedA a b n K ≤ (∑ j ∈ Finset.range K, a j) * gradedB b n K := by
  intro K
  induction K with
  | zero => simp [gradedA]
  | succ K ih =>
    simp only [gradedA, gradedB, Finset.sum_range_succ]
    have hgs := (geomSum_lt (hb K) (n K)).le
    have hB1 := gradedB_pos b n (fun j => le_trans (by norm_num) (hb j)) K
    have h1 : a K * geomSum (b K) (n K) ≤ a K * (b K ^ n K * gradedB b n K) :=
      Nat.mul_le_mul_left _ (hgs.trans (Nat.le_mul_of_pos_right _ hB1))
    have h2 : b K ^ n K * gradedA a b n K ≤
        b K ^ n K * ((∑ j ∈ Finset.range K, a j) * gradedB b n K) := Nat.mul_le_mul_left _ ih
    nlinarith only [h1, h2]

/-- `B ≤ 2^(Σ_{j<K} n_j f_j)` once every `b_j ≤ 2^(f j)`. -/
theorem gradedB_le (b n f : Nat → Nat) (hb : ∀ j, b j ≤ 2 ^ f j) :
    ∀ K, gradedB b n K ≤ 2 ^ (∑ j ∈ Finset.range K, n j * f j) := by
  intro K
  induction K with
  | zero => simp [gradedB]
  | succ K ih =>
    simp only [gradedB, Finset.sum_range_succ]
    calc b K ^ n K * gradedB b n K ≤ (2 ^ f K) ^ n K * 2 ^ (∑ j ∈ Finset.range K, n j * f j) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left (hb K) _) ih
      _ = 2 ^ (∑ j ∈ Finset.range K, n j * f j + n K * f K) := by
          rw [← pow_mul, ← pow_add]; ring_nf

namespace GenParamsG

variable (P : GenParamsG) (alpha : Real)

/-- The localization parameter `η` of the graded step. -/
def eta : Real := singlePieceEtaG (fun l => uCount P.V (uDeg l)) (fun l => P.Cg alpha l) alpha P.k

/-- The parameter of the lower-degree bound. -/
def yIn : Real := (P.eta alpha / 2) / (2 * (P.k + 1 + 2 : Nat) : Real) ^ (P.k + 1 + 2)

/-- **The graded single-piece inverse step in dimension `k`.** -/
theorem inverse_step (hV : 1 ≤ P.V) (hK : 2 ≤ P.K) (hp : 0 < P.p) (hk : 1 ≤ P.k)
    (hcov : ∀ l, 1 ≤ l → l ≤ P.k → PolyCoverAt l (uCount P.V (uDeg l)) (uExp P.V (uDeg l)))
    (hrec : Section16RecurrenceProfileWith P.k (familyRecThr P.k P.K P.p) (familyRecExp P.k P.p))
    {alpha : Real} (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2)
    (hlift : ∀ l, 1 ≤ l → l ≤ P.k → ∀ t,
      P.Cg alpha l t ≤ (liftLastC^[P.k + 1 - l] (P.baseCg alpha l)) t)
    {beta sigma T : Real}
    (hbound : FunctionDiscrepancyBound (P.k + 1) (P.yIn alpha) beta sigma T)
    (hb : 0 < beta) (hs : 0 < sigma) (hs16 : sigma ≤ 16) :
    FunctionDiscrepancyBound (P.k + 2) alpha (P.eta alpha * beta / 4)
      (inverseStepExponent (P.k + 1) (P.Eloc alpha) sigma)
      (max (shortLocalizationThreshold (P.k + 1) (P.Eloc alpha) (6 * ((P.k + 1 : Nat) : Real)) T
          (P.Tloc alpha))
        (inverseStepThreshold (P.k + 1) (P.eta alpha) beta (P.Eloc alpha)
          (6 * ((P.k + 1 : Nat) : Real)) sigma)) := by
  obtain ⟨⟨hB0, hB1⟩, -, -, -, -, -, -, -, -, -, -, -, -, hEw, hC⟩ := P.ranges hV hp ha haHalf
  obtain ⟨he0, he, -⟩ := P.Eloc_pos_le hV hp ha haHalf
  have hg : 0 < alpha / 2 := half_pos ha
  have hg1 : alpha / 2 ≤ 1 := by linarith
  have hretile : ∀ q, Section16RetiledLinearityBound P.k q (familyRecExp P.k P.p q)
      (familyRecThr P.k P.K P.p q) :=
    fun q => (hrec.retiled_family (fun q => familyRecThr_pos (by omega) q) q).single
  refine single_piece_inverse_step_global_graded (Qb := fun l => uCount P.V (uDeg l))
    (Eb := fun l => uExp P.V (uDeg l)) (Cg := fun l => P.Cg alpha l)
    (Wg := fun l => P.Wg alpha l) hk ha haHalf hcov
    (fun l g t s _ _ => one_le_uCount P.V (uDeg l) g t s)
    (fun l g t s _ _ => (uExp_pos_le P.V (uDeg l) g t s).1)
    hC (fun l => genW_mono (hEw l) P.k) ?_ ?_ (familyRecExp P.k P.p) (familyRecThr P.k P.K P.p)
    hretile he0 he hbound hb hs hs16 (fun N _ _ hN => P.modulus_conditions hV hK hp ha haHalf N hN)
  · intro l hl1 hlk t
    exact hlift l hl1 hlk t
  · intro l _ _ t L
    exact genW_le (hEw l) (uExp_mono_rho hV (uDeg l) hg hg1 hB0 hB1) (P.k + 1 - l) (by omega) t L

variable {alpha}

/-- **The graded lift inequality.** In face dimension `l` the lift density is
the uniform one at `D = uDeg l`. -/
theorem lift_le {μV : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) (hV : 1 ≤ P.V)
    (hVμ : P.V ≤ 2 ^ (2 ^ μV)) (hμ0 : max μV (fixDeg P.k) + 2 ≤ P.μ0) :
    ∀ l, 1 ≤ l → l ≤ P.k → ∀ t,
      P.Cg alpha l t ≤ (liftLastC^[P.k + 1 - l] (P.baseCg alpha l)) t := by
  intro l hl1 hlk t
  exact GenParams.std_lift (V := P.V) (D := uDeg l) (k := P.k) (K := P.K) (p := P.p) ha ha2 hV hVμ
    hμ0 (P.k + 1 - l) (by omega) (by show P.k + 1 - l ≤ P.k; omega) t

/-- The log-degree of the graded `ρ₁`. -/
def rhoDegG (k μ0 : Nat) : Nat :=
  max (76 * 2 ^ k + μ0 + 2) (fixDeg k) + k + 1 + (152 * 3 ^ k + 2 ^ k)

/-- **The graded nested density**: `ρ₁⁻¹ ≤ X^(2^rhoDegG)`. -/
theorem rho1_inv_leG (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) (hk0 : P.k ≤ 2 ^ P.μ0)
    (hk76 : P.k + 1 ≤ 2 ^ 76) :
    (P.Rho1 alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ rhoDegG P.k P.μ0) := by
  have hX := two_div_ge_two ha ha2
  have hX1 : (1 : Real) ≤ 2 / alpha := by linarith
  obtain ⟨ht0, ht1, hti⟩ := T2_gen_bounds P.k ha ha2
  set k := P.k with hkdef
  set n := vertexFaceCounts k with hndef
  -- the per-face exponents
  have hD : ∀ j, uDeg j ≤ 2 ^ (76 * 2 ^ j) := fun j => le_rfl
  have hkD : ∀ j, k + 1 ≤ uDeg j := by
    intro j
    refine hk76.trans (Nat.pow_le_pow_right (by norm_num) ?_)
    have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    omega
  have hab : ∀ j, P.ag j ≤ 2 ^ (76 * 2 ^ j + P.μ0 + 2) ∧ P.bg j ≤ 2 ^ (76 * 2 ^ j + 1) :=
    fun j => GenParams.std_exp_le (hD j) (hkD j) hk0
  have hb2 : ∀ j, 2 ≤ P.bg j := by
    intro j; show 2 ≤ uDeg j + 1 + k; have := hkD j; omega
  -- the closed form
  have hnest := gradedNestC_genC hX1 P.ag P.bg (P.baseCg alpha) k n (k + 1) _ ht0 ht1
  have hR : P.Rho1 alpha = ((2 / alpha) ^ gradedA P.ag P.bg n (k + 1))⁻¹ *
      (globalTheta2 alpha (alpha / 2) k) ^ gradedB P.bg n (k + 1) := hnest
  rw [hR, mul_inv, inv_inv, ← inv_pow]
  set A := gradedA P.ag P.bg n (k + 1)
  set B := gradedB P.bg n (k + 1)
  have hT := pow_le_pow_left₀ (inv_pos.mpr ht0).le hti B
  rw [← pow_mul] at hT
  set M := max (76 * 2 ^ k + P.μ0 + 2) (fixDeg k)
  -- `A + 2^fix·B ≤ 2^(M+k+1)·B`
  have hA := gradedA_le P.ag P.bg n hb2 (k + 1)
  have hsum : ∑ j ∈ Finset.range (k + 1), P.ag j ≤ (k + 1) * 2 ^ M := by
    calc ∑ j ∈ Finset.range (k + 1), P.ag j ≤ ∑ _j ∈ Finset.range (k + 1), 2 ^ M := by
          refine Finset.sum_le_sum fun j hj => (hab j).1.trans (Nat.pow_le_pow_right (by norm_num) ?_)
          have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          have h2 : 2 ^ j ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hjk
          have := le_max_left (76 * 2 ^ k + P.μ0 + 2) (fixDeg k)
          omega
      _ = (k + 1) * 2 ^ M := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hfix : 2 ^ fixDeg k ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
  have hk2 : k + 2 ≤ 2 ^ (k + 1) := Nat.lt_two_pow_self
  have hexp1 : A + 2 ^ fixDeg k * B ≤ 2 ^ (M + k + 1) * B := by
    have h1 : A ≤ (k + 1) * 2 ^ M * B := hA.trans (Nat.mul_le_mul_right _ hsum)
    have h2 : 2 ^ fixDeg k * B ≤ 2 ^ M * B := Nat.mul_le_mul_right _ hfix
    have h3 : (k + 2) * 2 ^ M ≤ 2 ^ (M + k + 1) := by
      rw [show M + k + 1 = (k + 1) + M by ring, pow_add]
      exact Nat.mul_le_mul_right _ hk2
    nlinarith only [h1, h2, h3]
  -- `B ≤ 2^(152·3^k + 2^k)`
  have hB := gradedB_le P.bg n (fun j => 76 * 2 ^ j + 1) (fun j => (hab j).2) (k + 1)
  have hBw : B ≤ 2 ^ (152 * 3 ^ k + 2 ^ k) :=
    hB.trans (Nat.pow_le_pow_right (by norm_num) (vertexFaceCounts_weighted_le k))
  calc (2 / alpha) ^ A * (globalTheta2 alpha (alpha / 2) k)⁻¹ ^ B
      ≤ (2 / alpha) ^ A * (2 / alpha) ^ (2 ^ fixDeg k * B) :=
        mul_le_mul_of_nonneg_left hT (by positivity)
    _ = (2 / alpha) ^ (A + 2 ^ fixDeg k * B) := by rw [← pow_add]
    _ ≤ (2 / alpha) ^ (2 ^ rhoDegG k P.μ0) := by
        apply pow_le_pow_right₀ hX1
        refine hexp1.trans ?_
        calc 2 ^ (M + k + 1) * B ≤ 2 ^ (M + k + 1) * 2 ^ (152 * 3 ^ k + 2 ^ k) :=
              Nat.mul_le_mul_left _ hBw
          _ = 2 ^ rhoDegG k P.μ0 := by unfold rhoDegG; rw [← pow_add]

/-- The log-degree of the graded input parameter `yIn`. -/
def densDegG (k μ0 : Nat) : Nat := rhoDegG k μ0 + 2 * (76 * 2 ^ k) + 13

/-- **The input parameter of the lower-degree bound**, graded. -/
theorem yIn_boundsG {μV : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (hV : 1 ≤ P.V) (hVμ : P.V ≤ 2 ^ (2 ^ μV)) (hμ0 : max μV (fixDeg P.k) + 2 ≤ P.μ0)
    (hk0 : P.k ≤ 2 ^ P.μ0) (hk76 : P.k + 1 ≤ 2 ^ 76) :
    0 < P.eta alpha ∧ P.eta alpha ≤ alpha / 8 ∧
      (P.eta alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ (rhoDegG P.k P.μ0 + 2 * (76 * 2 ^ P.k) + 12)) ∧
      0 < P.yIn alpha ∧ P.yIn alpha ≤ alpha ∧
      (P.yIn alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ densDegG P.k P.μ0) := by
  have hX := two_div_ge_two ha ha2
  have hX1 : (1 : Real) ≤ 2 / alpha := by linarith
  have hri := P.rho1_inv_leG ha ha2 hk0 hk76
  set k := P.k with hkdef
  set μD := 76 * 2 ^ k with hμDdef
  have hρ1 : μD + P.μ0 + 3 ≤ rhoDegG k P.μ0 := by
    unfold rhoDegG; have := le_max_left (76 * 2 ^ k + P.μ0 + 2) (fixDeg k); omega
  have hρ2 : fixDeg k + 1 ≤ rhoDegG k P.μ0 := by
    unfold rhoDegG; have := le_max_right (76 * 2 ^ k + P.μ0 + 2) (fixDeg k); omega
  have hbase := GenParams.baseC_recipPowerLB (D := uDeg k) (K := P.K) (p := P.p) ha ha2 hV hVμ hμ0
  have hD : uDeg k ≤ 2 ^ μD := le_rfl
  have ha0 : uDeg k * 2 ^ P.μ0 + 1 ≤ 2 ^ (μD + P.μ0 + 1) := by
    have h1 : uDeg k * 2 ^ P.μ0 ≤ 2 ^ μD * 2 ^ P.μ0 := Nat.mul_le_mul_right _ hD
    have h2 : 2 ^ (μD + P.μ0 + 1) = 2 * (2 ^ μD * 2 ^ P.μ0) := by rw [pow_add, pow_add]; ring
    have h3 : 1 ≤ 2 ^ μD * 2 ^ P.μ0 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hb0 : uDeg k + 1 ≤ 2 ^ (μD + 1) := by
    have : 2 ^ (μD + 1) = 2 * 2 ^ μD := by rw [pow_succ]; ring
    have := Nat.one_le_two_pow (n := μD)
    omega
  -- `ρ₁`
  obtain ⟨ht0, ht1, -⟩ := T2_gen_bounds k ha ha2
  have hC : ∀ l u, 0 < u → u ≤ 1 → 0 < P.Cg alpha l u ∧ P.Cg alpha l u ≤ 1 :=
    fun l => genC_pos_le hX1 _ _ _ _
  obtain ⟨hr0, hr1⟩ : 0 < P.Rho1 alpha ∧ P.Rho1 alpha ≤ 1 :=
    gradedNestC_pos_le hC _ _ _ ht0 ht1
  -- `ρ`, `θ_S`, the density
  obtain ⟨hR0, hR1, hRi⟩ := GenParams.rho_step hX hr0 hr1 hri (by omega)
  obtain ⟨hS0, hS1, hSi⟩ := GenParams.thetaS_step hX hR0 hR1 hRi
  obtain ⟨hd0, hd1, hdi⟩ := GenParams.dens_step hX hbase hS0 hS1 hSi ha0 hb0 (by omega)
  -- `η`, `yIn`
  have hm : fixDeg k ≤ rhoDegG k P.μ0 + 2 + 3 + 2 * (μD + 1) + 4 := by omega
  obtain ⟨he0, he8, hei⟩ := GenParams.eta_step (k := k) ha ha2 hd0 hd1 hdi hm
  obtain ⟨hy0, hyle, hyi⟩ := GenParams.yIn_step (k := k) ha ha2 he0 he8 hei (by omega)
  have e1 : rhoDegG k P.μ0 + 2 + 3 + 2 * (μD + 1) + 4 + 1 = rhoDegG k P.μ0 + 2 * μD + 12 := by
    ring
  have e2 : rhoDegG k P.μ0 + 2 + 3 + 2 * (μD + 1) + 4 + 1 + 1 = densDegG k P.μ0 := by
    unfold densDegG; ring
  rw [e1] at hei
  rw [e2] at hyi
  exact ⟨he0, he8, hei, hy0, hyle, hyi⟩

end GenParamsG

end LeanProofs.GowersSzemeredi
