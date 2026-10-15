import GowersSzemeredi.Proofs18GradedDensity
import GowersSzemeredi.Proofs18GenericExponents

/-! The width exponents of the graded single-piece step (Notes L.10, G4d).

* `gradedNestC_anti`: the graded nest decreases, so every level sits above
  the final `ρ₁`.
* `nestExp_inv_leG`: every level of the graded nested width costs at most
  `X^(2^(rhoDegG + 68·2^k + 3))` (the uniform per-level bound, at the top
  degree `uDeg68 k`). There are `2^k − 1` levels, so the exponent is at most
  `X^(2^(rhoDegG + 68·2^k + 3 + k))`.
* `Eloc_inv_leG`: `Eloc⁻¹ ≤ X^(2^(expDegG + 3))`, where `expDegG` is the
  uniform `expDeg` with `rhoDegG` in place of `rhoDeg`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The non-top vertices number `2^k − 1`. -/
theorem sum_vertexFaceCounts (k : Nat) :
    ∑ j ∈ Finset.range (k + 1), vertexFaceCounts k j = 2 ^ k - 1 := by
  classical
  have h := sum_vertexBlock_eq k (fun e => (section16VertexDirections e).card) (fun _ => 1) (k + 1)
    (fun e he => section16VertexDirections_card_lt he)
  simp only [mul_one, Finset.sum_const, smul_eq_mul] at h
  unfold vertexFaceCounts
  rw [h, nonTopVertices_card]

/-- The graded nest decreases when every block does. -/
theorem gradedNestC_anti {C : Nat → Real → Real}
    (hC : ∀ j t, 0 < t → t ≤ 1 → 0 < C j t ∧ C j t ≤ 1)
    (hdec : ∀ j r t, 0 < t → t ≤ 1 → nestC (fun _ => C j) r t ≤ t) (n : Nat → Nat) {t : Real}
    (ht : 0 < t) (ht1 : t ≤ 1) : ∀ J K, J ≤ K → gradedNestC C n K t ≤ gradedNestC C n J t := by
  intro J K hJK
  induction hJK with
  | refl => exact le_rfl
  | step _ ih =>
    refine le_trans ?_ ih
    obtain ⟨h0, h1⟩ := gradedNestC_pos_le hC n _ t ht ht1
    exact hdec _ _ _ h0 h1

/-- The exponent of the graded nested width, level by level. -/
theorem gradedNestExp_inv_le {E : Nat → Real → Real} {k : Nat} {C : Nat → Real → Real}
    {n : Nat → Nat} {t M : Real} (hM : 1 ≤ M)
    (hE : ∀ l s, 0 < s → s ≤ 1 → 0 < E l s ∧ E l s ≤ 1)
    (hC : ∀ l u, 0 < u → u ≤ 1 → 0 < C l u ∧ C l u ≤ 1) (ht : 0 < t) (ht1 : t ≤ 1)
    (hfac : ∀ j i, i < n j →
      (lwE (E j) k (nestC (fun _ => C j) i (gradedNestC C n j t)))⁻¹ ≤ M) :
    ∀ K, (gradedNestExp E k C n K t)⁻¹ ≤ M ^ (∑ j ∈ Finset.range K, n j) := by
  intro K
  induction K with
  | zero => simp [gradedNestExp]
  | succ K ih =>
    obtain ⟨c0, c1⟩ := gradedNestC_pos_le hC n K t ht ht1
    obtain ⟨g0, -, -, -⟩ := genNest_facts (hE K) k (hC K) (n K) _ c0 c1
    have hblock := genNestExp_inv_le hM (hE K) (hC K) c0 c1 (n K) (fun i hi => hfac K i hi)
    obtain ⟨e0, -, -, -⟩ := gradedNest_facts hE k hC n K t ht ht1
    show (gradedNestExp E k C n K t * genNestExp (E K) k (C K) (n K) (gradedNestC C n K t))⁻¹ ≤ _
    rw [mul_inv, Finset.sum_range_succ, pow_add]
    exact mul_le_mul ih hblock (inv_pos.mpr g0).le (pow_nonneg (le_trans zero_le_one hM) _)

namespace GenParamsG

/-- The standing hypotheses on graded parameters. -/
structure GHyp (P : GenParamsG) (μV μK : Nat) : Prop where
  hV : 1 ≤ P.V
  hVμ : P.V ≤ 2 ^ (2 ^ μV)
  hμ0 : max μV (fixDeg P.k) + 2 ≤ P.μ0
  hk0 : P.k ≤ 2 ^ P.μ0
  hk68 : P.k + 1 ≤ 2 ^ 68
  hK : 2 ≤ P.K
  hKμ : P.K ≤ 2 ^ 2 ^ μK
  hp : 0 < P.p
  hpμ : P.p ≤ 2 ^ (2 ^ μK)

variable (P : GenParamsG) {alpha : Real}

/-- The log-degree of the graded width exponents. -/
def expDegG (k μ0 μK : Nat) : Nat :=
  max (rhoDegG k μ0 + 2 * (68 * 2 ^ k) + 9) (max (rhoDegG k μ0 + 68 * 2 ^ k + k + 7) (μK + 2))

theorem rhoDegG_ge (k μ0 : Nat) : 68 * 2 ^ k + μ0 + 3 ≤ rhoDegG k μ0 ∧ fixDeg k + 1 ≤ rhoDegG k μ0 := by
  unfold rhoDegG
  have h1 := le_max_left (68 * 2 ^ k + μ0 + 2) (fixDeg k)
  have h2 := le_max_right (68 * 2 ^ k + μ0 + 2) (fixDeg k)
  omega

/-- **The graded nested width exponent.** -/
theorem nestExp_inv_leG {μV μK : Nat} (H : GHyp P μV μK) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    (P.NestExp alpha)⁻¹ ≤
      (2 / alpha) ^ (2 ^ (rhoDegG P.k P.μ0 + 68 * 2 ^ P.k + 3 + P.k)) := by
  have hX := two_div_ge_two ha ha2
  have hX1 : (1 : Real) ≤ 2 / alpha := by linarith
  obtain ⟨hρ1, hρ2⟩ := rhoDegG_ge P.k P.μ0
  obtain ⟨ht0, ht1, -⟩ := T2_gen_bounds P.k ha ha2
  have hC : ∀ l u, 0 < u → u ≤ 1 → 0 < P.Cg alpha l u ∧ P.Cg alpha l u ≤ 1 :=
    fun l => genC_pos_le hX1 _ _ _ _
  have hEw : ∀ l s, 0 < s → s ≤ 1 → 0 < P.Ewg alpha l s ∧ P.Ewg alpha l s ≤ 1 :=
    fun l s _ _ => uExp_pos_le _ _ _ _ s
  have hb1 : ∀ l, 1 ≤ P.bg l := fun l => by show 1 ≤ uDeg68 l + 1 + P.k; omega
  obtain ⟨hr0, -⟩ : 0 < P.Rho1 alpha ∧ P.Rho1 alpha ≤ 1 := gradedNestC_pos_le hC _ _ _ ht0 ht1
  have hri := P.rho1_inv_leG ha ha2 H.hk0 H.hk68
  have hdec : ∀ j r t, 0 < t → t ≤ 1 → nestC (fun _ => P.Cg alpha j) r t ≤ t := by
    intro j r t h0 h1
    exact nestC_genC_anti hX1 (hb1 j) (P.baseCg alpha j) P.k h0 h1 0 r (Nat.zero_le _)
  have hDk : ∀ j, j ≤ P.k → uDeg68 j ≤ 2 ^ (68 * 2 ^ P.k) := fun j hj =>
    Nat.pow_le_pow_right (by norm_num)
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hj))
  set M := (2 / alpha) ^ (2 ^ (rhoDegG P.k P.μ0 + 68 * 2 ^ P.k + 3))
  have hfac : ∀ j i, i < vertexFaceCounts P.k j →
      (lwE (P.Ewg alpha j) P.k (nestC (fun _ => P.Cg alpha j) i
        (gradedNestC (fun l => P.Cg alpha l) (vertexFaceCounts P.k) j (P.T2 alpha))))⁻¹ ≤ M := by
    intro j i hi
    have hjk : j ≤ P.k := by
      by_contra hj
      have hzero : vertexFaceCounts P.k j = 0 := by
        unfold vertexFaceCounts
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro e he
        obtain ⟨hne, hge⟩ := (Finset.mem_filter.mp he).2
        have hge' : (section16VertexDirections e).card = j := hge
        have := section16VertexDirections_card_lt hne
        omega
      omega
    obtain ⟨c0, c1⟩ := gradedNestC_pos_le hC (vertexFaceCounts P.k) j _ ht0 ht1
    obtain ⟨u0, u1⟩ := nestC_pos_le (c := fun _ => P.Cg alpha j) (fun _ => hC j) i _ c0 c1
    -- the level lies above `ρ₁`
    have hu1 : nestC (fun _ => P.Cg alpha j) (vertexFaceCounts P.k j)
        (gradedNestC (fun l => P.Cg alpha l) (vertexFaceCounts P.k) j (P.T2 alpha)) ≤
        nestC (fun _ => P.Cg alpha j) i
          (gradedNestC (fun l => P.Cg alpha l) (vertexFaceCounts P.k) j (P.T2 alpha)) :=
      nestC_genC_anti hX1 (hb1 j) (P.baseCg alpha j) P.k c0 c1 i _ hi.le
    have hu2 : P.Rho1 alpha ≤ gradedNestC (fun l => P.Cg alpha l) (vertexFaceCounts P.k) (j + 1)
        (P.T2 alpha) :=
      gradedNestC_anti hC hdec _ ht0 ht1 (j + 1) (P.k + 1) (by omega)
    have hu : P.Rho1 alpha ≤ nestC (fun _ => P.Cg alpha j) i
        (gradedNestC (fun l => P.Cg alpha l) (vertexFaceCounts P.k) j (P.T2 alpha)) :=
      hu2.trans hu1
    have hui := (inv_anti₀ hr0 hu).trans hri
    exact GenParams.lw_level_inv_le (D := uDeg68 j) ha ha2 H.hV H.hVμ H.hμ0 (hDk j hjk) u0 u1 hui
      hρ2 (by omega)
  have h := gradedNestExp_inv_le (one_le_pw hX _) hEw hC ht0 ht1 hfac (P.k + 1)
  rw [sum_vertexFaceCounts] at h
  exact h.trans (pw_pow hX (by positivity) le_rfl (Nat.sub_le _ _))

/-- **`Em`, `QM` and `Bexp`**, graded. -/
theorem spectrum_exps_inv_leG {μV μK : Nat} (H : GHyp P μV μK) (ha : 0 < alpha)
    (ha2 : alpha ≤ 1 / 2) :
    (P.Em alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ (rhoDegG P.k P.μ0 + 68 * 2 ^ P.k + 2)) ∧
      (P.QM alpha : Real) + 1 ≤ (2 / alpha) ^ (2 ^ (rhoDegG P.k P.μ0 + 68 * 2 ^ P.k + 3)) ∧
      (P.Bexp alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ expDegG P.k P.μ0 μK) := by
  have hX := two_div_ge_two ha ha2
  have hX1 : (1 : Real) ≤ 2 / alpha := by linarith
  have hri := P.rho1_inv_leG ha ha2 H.hk0 H.hk68
  set k := P.k
  set ρ := rhoDegG k P.μ0
  set μD := 68 * 2 ^ k
  have hρ1 : μD + P.μ0 + 3 ≤ ρ := (rhoDegG_ge k P.μ0).1
  have hM2 : ρ + μD + k + 7 ≤ expDegG k P.μ0 μK := by
    unfold expDegG; exact (le_max_left _ _).trans (le_max_right _ _)
  have hM3 : μK + 2 ≤ expDegG k P.μ0 μK := by
    unfold expDegG; exact (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨hB0, hB1, hBi⟩ := budget_gen_bounds k ha ha2
  obtain ⟨hd0, hd1, hdi⟩ := delta_gen_bounds k ha ha2
  obtain ⟨ht0, ht1, -⟩ := T2_gen_bounds k ha ha2
  have hC : ∀ l u, 0 < u → u ≤ 1 → 0 < P.Cg alpha l u ∧ P.Cg alpha l u ≤ 1 :=
    fun l => genC_pos_le hX1 _ _ _ _
  obtain ⟨hr0, hr1⟩ : 0 < P.Rho1 alpha ∧ P.Rho1 alpha ≤ 1 := gradedNestC_pos_le hC _ _ _ ht0 ht1
  have hq0 : 0 < P.Rho1 alpha / 2 / 2 := by linarith
  have hq1 : P.Rho1 alpha / 2 / 2 ≤ 1 := by linarith
  have hqi : (P.Rho1 alpha / 2 / 2)⁻¹ ≤ (2 / alpha) ^ (2 ^ (ρ + 1)) := by
    rw [show (P.Rho1 alpha / 2 / 2)⁻¹ = 4 * (P.Rho1 alpha)⁻¹ by field_simp; ring]
    have h4 : (4 : Real) ≤ (2 / alpha) ^ (2 ^ ρ) :=
      pw_mono hX (pw_const hX (a := 1) (by norm_num)) (by omega)
    exact pw_mul hX (inv_pos.mpr hr0).le h4 hri
  have hQ := uCount_scale_le (c := ρ + 1) (D := uDeg68 k) (μD := μD) hX H.hV H.hVμ H.hμ0 hd0 hd1 hdi
    hB0 hB1 hBi hq0 hq1 hqi le_rfl
  rw [max_eq_right (show P.μ0 ≤ ρ + 1 by omega)] at hQ
  have hQv : singlePieceGlobalQmaxG (fun l => uCount P.V (uDeg68 l)) (fun l => P.Cg alpha l) alpha
      (alpha / 2) k ≤ (2 / alpha) ^ (2 ^ (ρ + 1 + 1 + μD)) := hQ
  have hQv1 : 1 ≤ singlePieceGlobalQmaxG (fun l => uCount P.V (uDeg68 l)) (fun l => P.Cg alpha l)
      alpha (alpha / 2) k := one_le_uCount _ _ _ _ _
  have hQM := GenParams.floor_succ_le_pw hX hQv1 hQv
  have hQM' : (P.QM alpha : Real) + 1 ≤ (2 / alpha) ^ (2 ^ (ρ + μD + 3)) :=
    hQM.trans (pw_natpow hX (Nat.pow_le_pow_right (by norm_num) (by omega)))
  refine ⟨?_, hQM', ?_⟩
  · show (uCount P.V (uDeg68 k) _ _ _)⁻¹⁻¹ ≤ _
    rw [inv_inv]
    exact hQ.trans (pw_natpow hX (Nat.pow_le_pow_right (by norm_num) (by omega)))
  · show (familyRecExp k P.p (P.QM alpha) / 2)⁻¹ ≤ _
    rw [GenParams.half_familyRecExp_inv]
    have hq0' : (0 : Real) ≤ (P.QM alpha : Real) + 1 := by
      have := Nat.cast_nonneg (α := Real) (P.QM alpha); linarith
    have hk2 : 2 * 2 ^ (k + 1) ≤ 2 ^ (k + 2) := by rw [pow_succ 2 (k + 1)]; omega
    have hpow := pw_pow hX hq0' hQM' hk2
    have hp' : (P.p : Real) ≤ (2 / alpha) ^ (2 ^ μK) := pw_const hX (by exact_mod_cast H.hpμ)
    have h4 : (4 : Real) ≤ (2 / alpha) ^ (2 ^ (μK + 1)) :=
      pw_mono hX (pw_const hX (a := 1) (by norm_num)) (by omega)
    have hpq0 : (0 : Real) ≤ ((P.QM alpha : Real) + 1) ^ (2 * 2 ^ (k + 1)) := pow_nonneg hq0' _
    have h1 := pw_mul' hX hpq0 hp' hpow
    have h2 := pw_mul' hX (mul_nonneg (Nat.cast_nonneg _) hpq0) h4 h1
    refine pw_mono hX h2 ?_
    have : max μK (ρ + μD + 3 + (k + 2)) + 1 ≤ expDegG k P.μ0 μK - 1 := by omega
    omega

/-- **The slice exponents `Eth` and `Ec`**, graded. -/
theorem slice_exps_inv_leG {μV μK : Nat} (H : GHyp P μV μK) (ha : 0 < alpha)
    (ha2 : alpha ≤ 1 / 2) :
    (P.Eth alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ (rhoDegG P.k P.μ0 + 2 * (68 * 2 ^ P.k) + 9)) ∧
      (P.Ec alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ (rhoDegG P.k P.μ0 + 2 * (68 * 2 ^ P.k) + 9)) := by
  have hX := two_div_ge_two ha ha2
  have hX1 : (1 : Real) ≤ 2 / alpha := by linarith
  have hri := P.rho1_inv_leG ha ha2 H.hk0 H.hk68
  set k := P.k
  set ρ := rhoDegG k P.μ0
  set μD := 68 * 2 ^ k
  have hρ1 : μD + P.μ0 + 3 ≤ ρ := (rhoDegG_ge k P.μ0).1
  obtain ⟨hB0, hB1, hBi⟩ := budget_gen_bounds k ha ha2
  obtain ⟨ht0, ht1, -⟩ := T2_gen_bounds k ha ha2
  have hC : ∀ l u, 0 < u → u ≤ 1 → 0 < P.Cg alpha l u ∧ P.Cg alpha l u ≤ 1 :=
    fun l => genC_pos_le hX1 _ _ _ _
  obtain ⟨hr0, hr1⟩ : 0 < P.Rho1 alpha ∧ P.Rho1 alpha ≤ 1 := gradedNestC_pos_le hC _ _ _ ht0 ht1
  obtain ⟨hR0, hR1, hRi⟩ := GenParams.rho_step hX hr0 hr1 hri (by omega)
  obtain ⟨hS0, hS1, hSi⟩ := GenParams.thetaS_step hX hR0 hR1 hRi
  have hThS : P.ThS alpha =
      singlePieceTheta ((P.Rho1 alpha) / 2 * ((P.Rho1 alpha) / 2 / 2)) 1 := rfl
  rw [← hThS] at hS0 hS1 hSi
  have hbase := GenParams.baseC_recipPowerLB (D := uDeg68 k) (K := P.K) (p := P.p) ha ha2 H.hV H.hVμ
    H.hμ0
  have ha0 : uDeg68 k * 2 ^ P.μ0 + 1 ≤ 2 ^ (μD + P.μ0 + 1) := by
    have h1 : uDeg68 k * 2 ^ P.μ0 ≤ 2 ^ μD * 2 ^ P.μ0 := Nat.mul_le_mul_right _ le_rfl
    have h2 : 2 ^ (μD + P.μ0 + 1) = 2 * (2 ^ μD * 2 ^ P.μ0) := by rw [pow_add, pow_add]; ring
    have h3 : 1 ≤ 2 ^ μD * 2 ^ P.μ0 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hb0 : uDeg68 k + 1 ≤ 2 ^ (μD + 1) := by
    have : 2 ^ (μD + 1) = 2 * 2 ^ μD := by rw [pow_succ]; ring
    have := Nat.one_le_two_pow (n := μD)
    have hD : uDeg68 k ≤ 2 ^ μD := le_rfl
    omega
  obtain ⟨hc0, hc1, hci⟩ := GenParams.cS_step hX hbase hS0 hS1 hSi ha0 hb0 (by omega)
  have hCS : P.CS alpha =
      (GenParams.std P.V (uDeg68 k) P.k P.K P.p P.μ0).baseC alpha (P.ThS alpha) := rfl
  rw [← hCS] at hc0 hc1 hci
  have hslice : ∀ {s : Real} {m : Nat}, 0 < s → s ≤ 1 → s⁻¹ ≤ (2 / alpha) ^ (2 ^ m) →
      P.μ0 ≤ m + 1 → (uExp P.V (uDeg68 k) (alpha / 2) (globalBudget alpha (alpha / 2) k) (s / 2))⁻¹ ≤
        (2 / alpha) ^ (2 ^ (m + 1 + 1 + μD)) := by
    intro s m hs0 hs1 hsi hm
    have hs20 : 0 < s / 2 := half_pos hs0
    have hs2i : (s / 2)⁻¹ ≤ (2 / alpha) ^ (2 ^ (m + 1)) := by
      rw [inv_div, div_eq_mul_inv]
      exact pw_mul hX (inv_pos.mpr hs0).le (hX.trans (pw_X hX _)) hsi
    have h := uCount_scale_le (c := m + 1) (D := uDeg68 k) (μD := μD) hX H.hV H.hVμ H.hμ0
      (half_pos ha) (by linarith) (GenParams.half_inv_le k ha ha2) hB0 hB1 hBi hs20 (by linarith)
      hs2i le_rfl
    rw [max_eq_right hm] at h
    show (uCount P.V (uDeg68 k) _ _ _)⁻¹⁻¹ ≤ _
    rw [inv_inv]; exact h
  constructor
  · exact pw_mono hX (hslice hS0 hS1 hSi (by omega)) (by omega)
  · exact pw_mono hX (hslice hc0 hc1 hci (by omega)) (by omega)

/-- **The graded localization exponent is polynomially small.** -/
theorem Eloc_inv_leG {μV μK : Nat} (H : GHyp P μV μK) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < P.Eloc alpha ∧ (P.Eloc alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ (expDegG P.k P.μ0 μK + 3)) := by
  have hX := two_div_ge_two ha ha2
  set M := expDegG P.k P.μ0 μK with hMdef
  have hM1 : rhoDegG P.k P.μ0 + 2 * (68 * 2 ^ P.k) + 9 ≤ M := by
    rw [hMdef]; unfold expDegG; exact le_max_left _ _
  have hM2 : rhoDegG P.k P.μ0 + 68 * 2 ^ P.k + P.k + 7 ≤ M := by
    rw [hMdef]; unfold expDegG; exact (le_max_left _ _).trans (le_max_right _ _)
  obtain ⟨hE0, -, -, -, -, -⟩ := P.Eloc_pos_le H.hV H.hp ha ha2
  obtain ⟨-, -, -, -, -, -, -, ⟨hEm0, -⟩, ⟨hEth0, -⟩, ⟨hEc0, -⟩, ⟨hN0, -, -⟩, ⟨hBx0, -⟩,
    -, -, -⟩ := P.ranges H.hV H.hp ha ha2
  have hNE := P.nestExp_inv_leG H ha ha2
  obtain ⟨hEm, -, hBx⟩ := P.spectrum_exps_inv_leG H ha ha2
  obtain ⟨hEth, hEc⟩ := P.slice_exps_inv_leG H ha ha2
  refine ⟨hE0, ?_⟩
  have hval : (P.Eloc alpha)⁻¹ =
      32 * ((P.NestExp alpha)⁻¹ * (P.Em alpha)⁻¹) *
      ((P.Bexp alpha)⁻¹ * ((P.Eth alpha)⁻¹ * (P.Ec alpha)⁻¹)) := by
    show ((P.NestExp alpha * (P.Em alpha / 2)) *
      (P.Bexp alpha * (P.Eth alpha * P.Ec alpha) / 2) / 8)⁻¹ = _
    field_simp
    ring
  rw [hval]
  have hNE' := pw_mono hX hNE (show rhoDegG P.k P.μ0 + 68 * 2 ^ P.k + 3 + P.k ≤ M by omega)
  have hEm' := pw_mono hX hEm (show rhoDegG P.k P.μ0 + 68 * 2 ^ P.k + 2 ≤ M by omega)
  have hEth' := pw_mono hX hEth hM1
  have hEc' := pw_mono hX hEc hM1
  have h32 : (32 : Real) ≤ (2 / alpha) ^ (2 ^ (M + 1)) :=
    pw_mono hX (pw_const hX (a := 3) (by norm_num)) (by omega)
  have p1 := pw_mul hX (inv_pos.mpr hEm0).le hNE' hEm'
  have p2 := pw_mul hX (inv_pos.mpr hEc0).le hEth' hEc'
  have p3 := pw_mul' hX (by positivity) hBx p2
  have p4 := pw_mul hX (by positivity) h32 p1
  have p5 := pw_mul' hX (by positivity) p4 p3
  exact pw_mono hX p5 (by omega)

end GenParamsG

end LeanProofs.GowersSzemeredi
