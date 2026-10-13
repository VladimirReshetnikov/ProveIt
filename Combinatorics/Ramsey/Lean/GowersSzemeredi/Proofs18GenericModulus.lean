import GowersSzemeredi.Proofs18GenericLifts

/-! The scale conditions of the single-piece step in any dimension
(Notes L.7a, F3b).

`single_piece_inverse_step_global` at dimension `k` needs, at every large
prime modulus `N`, the conditions `SinglePieceModulusConditions`. This
module proves them above an explicit threshold `GenParams.Tloc`, for the
uniform controls `uCount`, `uExp` and the closed-form lifts `genC`, `genW`.
It is `ls_modulus_conditions` with the dimension `2` and the nest depth `3`
replaced by `k` and `2^k − 1`.

* `genNest_facts`: the `r`-fold nested width is at least `L^(genNestExp)`
  above `genNestThr`, by `WidthPowerLB.comp` at each level.
* `GenParams`: the data `(V, D, k, K, p, a, b)`. Here `V, D` are the cover
  controls, `K, p` the recurrence constants in dimension `k`, and `a, b`
  the exponents of `genC`.
* `GenParams.modulus_conditions`, `GenParams.Eloc_pos_le`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-! ### The nested width -/

/-- The exponent of the `r`-fold nested width. -/
def genNestExp (E : Real → Real) (k : Nat) (C : Real → Real) : Nat → Real → Real
  | 0 => fun _ => 1
  | r + 1 => fun t => genNestExp E k C r t * lwE E k (nestC (fun _ => C) r t)

/-- The threshold of the `r`-fold nested width. -/
def genNestThr (E : Real → Real) (k : Nat) (C : Real → Real) : Nat → Real → Real
  | 0 => fun _ => 1
  | r + 1 => fun t => max (genNestThr E k C r t)
      (genWThr E k (nestC (fun _ => C) r t) ^ (1 / genNestExp E k C r t))

theorem genNest_facts {E : Real → Real} (hE : ∀ s, 0 < s → s ≤ 1 → 0 < E s ∧ E s ≤ 1) (k : Nat)
    {C : Real → Real} (hC : ∀ u, 0 < u → u ≤ 1 → 0 < C u ∧ C u ≤ 1) :
    ∀ r t, 0 < t → t ≤ 1 →
      0 < genNestExp E k C r t ∧ genNestExp E k C r t ≤ 1 ∧ 1 ≤ genNestThr E k C r t ∧
      WidthPowerLB (fun L => nestW (fun _ => C) (fun _ => genW E k) r t L)
        (genNestExp E k C r t) (genNestThr E k C r t) := by
  intro r
  induction r with
  | zero =>
    intro t _ _
    refine ⟨one_pos, le_rfl, le_rfl, ?_⟩
    intro L _
    show (L : Real) ^ (1 : Real) ≤ ((L : Nat) : Real)
    rw [Real.rpow_one]
  | succ r ih =>
    intro t ht ht1
    obtain ⟨e0, e1, t1, hw⟩ := ih t ht ht1
    obtain ⟨c0, c1⟩ := nestC_pos_le (c := fun _ => C) (fun _ => hC) r t ht ht1
    obtain ⟨l0, l1⟩ := lwE_pos_le hE k c0 c1
    have hv := genW_powerLB E k c0 c1
    have hcomp := WidthPowerLB.comp hw hv e0 l0.le t1
      (zero_le_one.trans (one_le_genWThr hE k c0 c1))
    refine ⟨mul_pos e0 l0, ?_, t1.trans (le_max_left _ _), hcomp⟩
    calc genNestExp E k C r t * lwE E k (nestC (fun _ => C) r t) ≤ 1 * 1 :=
          mul_le_mul e1 l1 l0.le zero_le_one
      _ = 1 := one_mul 1

/-! ### The parameters -/

/-- The data of the single-piece step in dimension `k`. -/
structure GenParams where
  /-- The base of the cover controls. -/
  V : Real
  /-- The degree of the cover controls. -/
  D : Nat
  /-- The dimension of the step. -/
  k : Nat
  /-- The recurrence threshold constant in dimension `k`. -/
  K : Nat
  /-- The recurrence exponent constant in dimension `k`. -/
  p : Nat
  /-- The `X`-exponent of the lift density. -/
  a : Nat
  /-- The `t`-exponent of the lift density. -/
  b : Nat

namespace GenParams

variable (P : GenParams) (alpha : Real)

/-- The budget `globalBudget α (α/2) k`. -/
def B : Real := globalBudget alpha (alpha / 2) P.k
/-- The width exponent of the base cover. -/
def Ew : Real → Real := uExp P.V P.D (alpha / 2) (P.B alpha)
/-- The base slice density. -/
def baseC : Real → Real := fun s => s / 2 / uCount P.V P.D (alpha / 2) (P.B alpha) (s / 2)
/-- The lift density. -/
def C : Real → Real := genC (2 / alpha) P.a P.b (P.baseC alpha) P.k
/-- The lift width. -/
def W : Real → Nat → Nat := genW (P.Ew alpha) P.k
/-- `θ₂/2`. -/
def T2 : Real := globalTheta2 alpha (alpha / 2) P.k
/-- The nested density `ρ₁`. -/
def Rho1 : Real := nestC (fun _ => P.C alpha) (2 ^ P.k - 1) (P.T2 alpha)
/-- `δ(θ₁)`. -/
def Delta : Real := section16Delta (section16ThetaOne alpha (alpha / 2) P.k)
/-- The exponent of the spectrum-scale cover. -/
def Em : Real := uExp P.V P.D (P.Delta alpha) (P.B alpha) (P.Rho1 alpha / 2 / 2)
/-- The exponent of the nested width. -/
def NestExp : Real := genNestExp (P.Ew alpha) P.k (P.C alpha) (2 ^ P.k - 1) (P.T2 alpha)
/-- The threshold of the nested width. -/
def NestThr : Real := genNestThr (P.Ew alpha) P.k (P.C alpha) (2 ^ P.k - 1) (P.T2 alpha)
/-- The exponent of `m` in `N`. -/
def MExp : Real := P.NestExp alpha * (P.Em alpha / 2)
/-- The threshold for `m ≥ N^MExp`. -/
def MThr : Real := max (P.NestThr alpha) (64 ^ (1 / P.NestExp alpha))
/-- The worst spectrum count. -/
def QM : Nat := ⌊singlePieceGlobalQmax (fun _ => uCount P.V P.D) (P.C alpha) alpha (alpha / 2) P.k⌋₊
/-- The exponent of `m` in the spectrum cell width. -/
def Bexp : Real := familyRecExp P.k P.p (P.QM alpha) / 2
/-- The Bohr radius. -/
def Zeta : Real := section16Zeta alpha (alpha / 2) P.k
/-- The spectrum density. -/
def Rho : Real := spectrumPieceRho (fun t => t / 2) (P.Rho1 alpha)
/-- The slice density. -/
def ThS : Real := singlePieceTheta (P.Rho alpha) 1
/-- The slice control. -/
def CS : Real := singlePieceGlobalC (fun _ => uCount P.V P.D) alpha (alpha / 2) P.k (P.ThS alpha)
/-- The first slice exponent. -/
def Eth : Real := uExp P.V P.D (alpha / 2) (P.B alpha) (P.ThS alpha / 2)
/-- The second slice exponent. -/
def Ec : Real := uExp P.V P.D (alpha / 2) (P.B alpha) (P.CS alpha / 2)
/-- The exponent of the final width in `N`. -/
def F : Real := P.MExp alpha * (P.Bexp alpha * (P.Eth alpha * P.Ec alpha) / 2)
/-- The localization exponent. -/
def Eloc : Real := P.F alpha / 8
/-- How large `m` must be. -/
def MReq : Real :=
  max (familyRecThr P.k P.K P.p (P.QM alpha) : Real)
    (max ((8 / P.Zeta alpha) ^ (1 / P.Bexp alpha))
      (max ((4 / (P.Zeta alpha * P.Rho alpha ^ 3)) ^ (1 / P.Bexp alpha))
        ((16 / P.Zeta alpha) ^ (2 / P.Bexp alpha))))
/-- **The modulus threshold of the step.** -/
def Tloc : Real :=
  max (max 3 (lemma156ExplicitThreshold P.k (alpha / 2) (alpha / 2)))
    (max (P.MThr alpha)
      (max (4 ^ (1 / P.NestExp alpha))
        (max (P.MReq alpha ^ (1 / P.MExp alpha))
          (max (6 ^ (1 / P.Eloc alpha)) (8 ^ (2 / P.F alpha))))))

/-! ### Ranges -/

/-- The ranges of the parameters, for `0 < α ≤ 1/2`, `V ≥ 1`, `p > 0`. -/
theorem ranges (hV : 1 ≤ P.V) (hp : 0 < P.p) {alpha : Real} (ha : 0 < alpha)
    (haHalf : alpha ≤ 1 / 2) :
    (0 < P.B alpha ∧ P.B alpha ≤ 1) ∧ (0 < P.Delta alpha ∧ P.Delta alpha ≤ 1) ∧
    (0 < P.T2 alpha ∧ P.T2 alpha ≤ 1) ∧ (0 < P.Rho1 alpha ∧ P.Rho1 alpha ≤ 1) ∧
    (0 < P.Rho alpha ∧ P.Rho alpha ≤ 1) ∧ (0 < P.ThS alpha ∧ P.ThS alpha ≤ 1) ∧
    (0 < P.CS alpha ∧ P.CS alpha ≤ 1) ∧ (0 < P.Em alpha ∧ P.Em alpha ≤ 1) ∧
    (0 < P.Eth alpha ∧ P.Eth alpha ≤ 1) ∧ (0 < P.Ec alpha ∧ P.Ec alpha ≤ 1) ∧
    (0 < P.NestExp alpha ∧ P.NestExp alpha ≤ 1 ∧ 1 ≤ P.NestThr alpha) ∧
    (0 < P.Bexp alpha ∧ P.Bexp alpha ≤ 1) ∧ (0 < P.Zeta alpha) ∧
    (∀ s, 0 < s → s ≤ 1 → 0 < P.Ew alpha s ∧ P.Ew alpha s ≤ 1) ∧
    (∀ u, 0 < u → u ≤ 1 → 0 < P.C alpha u ∧ P.C alpha u ≤ 1) := by
  have ha1 : alpha ≤ 1 := by linarith
  have hg : 0 < alpha / 2 := half_pos ha
  have hg1 : alpha / 2 ≤ 1 := by linarith
  have hX : (1 : Real) ≤ 2 / alpha := by rw [le_div_iff₀ ha]; linarith
  obtain ⟨hθ₂, hθ₂1⟩ := section16ThetaTwo_pos_le (gamma := alpha / 2) P.k ha ha1 hg hg1
  have hB : 0 < P.B alpha ∧ P.B alpha ≤ 1 := by
    unfold B globalBudget
    have hden : (1 : Real) ≤ 2 * (2 ^ P.k + 1) := by
      have : (1 : Real) ≤ 2 ^ P.k := one_le_pow₀ (by norm_num)
      linarith
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by positivity)]
    linarith
  obtain ⟨-, -, hd0, hd1⟩ := section16_theta_delta_bounds P.k ha ha1 hg hg1
  have hT2 : 0 < P.T2 alpha ∧ P.T2 alpha ≤ 1 := by
    unfold T2 globalTheta2; exact ⟨by positivity, by linarith⟩
  have hEw : ∀ s, 0 < s → s ≤ 1 → 0 < P.Ew alpha s ∧ P.Ew alpha s ≤ 1 :=
    fun s _ _ => uExp_pos_le P.V P.D (alpha / 2) (P.B alpha) s
  have hC : ∀ u, 0 < u → u ≤ 1 → 0 < P.C alpha u ∧ P.C alpha u ≤ 1 :=
    genC_pos_le hX P.a P.b (P.baseC alpha) P.k
  have hR1 : 0 < P.Rho1 alpha ∧ P.Rho1 alpha ≤ 1 :=
    nestC_pos_le (c := fun _ => P.C alpha) (fun _ => hC) _ _ hT2.1 hT2.2
  have hR : 0 < P.Rho alpha ∧ P.Rho alpha ≤ 1 := by
    unfold Rho spectrumPieceRho
    exact ⟨by have := hR1.1; positivity,
      mul_le_one₀ (by linarith [hR1.2]) (by linarith [hR1.1]) (by linarith [hR1.2])⟩
  have hS : 0 < P.ThS alpha ∧ P.ThS alpha ≤ 1 :=
    ⟨singlePieceTheta_pos hR.1 (by norm_num),
      singlePieceTheta_le_one hR.1 hR.2 (by norm_num)⟩
  have hCS : 0 < P.CS alpha ∧ P.CS alpha ≤ 1 := by
    have hq := one_le_uCount P.V P.D (alpha / 2) (P.B alpha) (P.ThS alpha / 2)
    have hq0 := lt_of_lt_of_le zero_lt_one hq
    exact ⟨div_pos (half_pos hS.1) hq0, (div_le_one hq0).mpr (by linarith [hS.2])⟩
  have hEm : 0 < P.Em alpha ∧ P.Em alpha ≤ 1 :=
    uExp_pos_le P.V P.D (P.Delta alpha) (P.B alpha) (P.Rho1 alpha / 2 / 2)
  have hEth : 0 < P.Eth alpha ∧ P.Eth alpha ≤ 1 :=
    uExp_pos_le P.V P.D (alpha / 2) (P.B alpha) (P.ThS alpha / 2)
  have hEc : 0 < P.Ec alpha ∧ P.Ec alpha ≤ 1 :=
    uExp_pos_le P.V P.D (alpha / 2) (P.B alpha) (P.CS alpha / 2)
  obtain ⟨n0, n1, nt, -⟩ := genNest_facts hEw P.k hC (2 ^ P.k - 1) (P.T2 alpha) hT2.1 hT2.2
  have hBx : 0 < P.Bexp alpha ∧ P.Bexp alpha ≤ 1 := by
    have h0 := familyRecExp_pos P.k P.p (P.QM alpha) hp
    have h1 := familyRecExp_le_one P.k P.p (P.QM alpha) hp
    unfold Bexp
    exact ⟨by positivity, by linarith⟩
  obtain ⟨hz, -⟩ := section16Zeta_pos_le_half P.k ha ha1 hg hg1
  exact ⟨hB, ⟨hd0, hd1⟩, hT2, hR1, hR, hS, hCS, hEm, hEth, hEc, ⟨n0, n1, nt⟩, hBx, hz, hEw, hC⟩

/-- The localization exponent lies in `(0, 1/2]`. -/
theorem Eloc_pos_le (hV : 1 ≤ P.V) (hp : 0 < P.p) {alpha : Real} (ha : 0 < alpha)
    (haHalf : alpha ≤ 1 / 2) :
    0 < P.Eloc alpha ∧ P.Eloc alpha ≤ 1 / 2 ∧ 0 < P.F alpha ∧ P.F alpha ≤ 1 ∧
      0 < P.MExp alpha ∧ P.MExp alpha ≤ 1 := by
  obtain ⟨-, -, -, -, -, -, -, hEm, hEth, hEc, ⟨n0, n1, -⟩, hBx, -, -, -⟩ :=
    P.ranges hV hp ha haHalf
  simpa only [Eloc, F, MExp] using
    localization_exponents_pos_le ⟨n0, n1⟩ hEm hBx hEth hEc

/-- **The scale conditions of the step hold above `Tloc`.** -/
theorem modulus_conditions (hV : 1 ≤ P.V) (hK : 2 ≤ P.K) (hp : 0 < P.p) {alpha : Real}
    (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2)
    (N : Nat) [NeZero N] [Fact N.Prime] (hN : P.Tloc alpha ≤ N) :
    SinglePieceModulusConditions (fun _ => uCount P.V P.D) (fun _ => uExp P.V P.D) (P.C alpha)
      (P.W alpha) alpha P.k (familyRecExp P.k P.p) (familyRecThr P.k P.K P.p)
      (P.Eloc alpha) N := by
  classical
  obtain ⟨⟨hB0, hB1⟩, ⟨hd0, hd1⟩, ⟨ht2, ht21⟩, ⟨hρ1, hρ1'⟩, ⟨hρ, hρ'⟩, ⟨hthS, hthS'⟩,
    ⟨hcS, hcS'⟩, ⟨hEm, hEm'⟩, ⟨hEth, hEth'⟩, ⟨hEc, hEc'⟩, ⟨haN, haN', hNT⟩, ⟨hb, hb'⟩, hζ,
    hEw, hC⟩ := P.ranges hV hp ha haHalf
  obtain ⟨he, -, hF, -, hmE, -⟩ := P.Eloc_pos_le hV hp ha haHalf
  -- the modulus is large
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hT : ∀ X : Real, X ≤ P.Tloc alpha → X ≤ N := fun X hX => hX.trans hN
  have hN3 : (3 : Real) ≤ N := hT _ ((le_max_left _ _).trans (le_max_left _ _))
  have hN156 : lemma156ExplicitThreshold P.k (alpha / 2) (alpha / 2) ≤ N :=
    hT _ ((le_max_right _ _).trans (le_max_left _ _))
  have hNM : P.MThr alpha ≤ N :=
    hT _ ((le_max_left _ _).trans (le_max_right _ _))
  have hN4 : (4 : Real) ^ (1 / P.NestExp alpha) ≤ N :=
    hT _ ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hNR : P.MReq alpha ^ (1 / P.MExp alpha) ≤ N :=
    hT _ ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      (le_max_right _ _))))
  have hN6 : (6 : Real) ^ (1 / P.Eloc alpha) ≤ N :=
    hT _ ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))))
  have hN8 : (8 : Real) ^ (2 / P.F alpha) ≤ N :=
    hT _ ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))))
  have hprime : N.Prime := Fact.out
  have hodd : Odd N := hprime.odd_of_ne_two (by
    intro h2; rw [h2] at hN3; norm_num at hN3)
  -- the nested width and `m`
  obtain ⟨NW, hNW⟩ : ∃ NW : Nat, nestW (fun _ => P.C alpha) (fun _ => P.W alpha) (2 ^ P.k - 1)
      (globalTheta2 alpha (alpha / 2) P.k) N = NW := ⟨_, rfl⟩
  have hnest := (genNest_facts hEw P.k hC (2 ^ P.k - 1) (P.T2 alpha) ht2 ht21).2.2.2
  have hNWpow : (N : Real) ^ P.NestExp alpha ≤ NW := by
    have h : (N : Real) ^ P.NestExp alpha ≤
        ((nestW (fun _ => P.C alpha) (fun _ => P.W alpha) (2 ^ P.k - 1) (P.T2 alpha) N : Nat) : Real) :=
      hnest N (hNM.trans' (le_max_left _ _))
    have hNW' : nestW (fun _ => P.C alpha) (fun _ => P.W alpha) (2 ^ P.k - 1) (P.T2 alpha) N = NW :=
      hNW
    rw [hNW'] at h
    exact h
  have hNW4 : (4 : Real) ≤ NW :=
    (le_rpow_of_rpow_inv_le haN (by norm_num) hN4).trans hNWpow
  obtain ⟨m, hm⟩ : ∃ m : Nat, coverWidth (uExp P.V P.D (P.Delta alpha) (P.B alpha))
      (singlePieceGlobalRho1 (P.C alpha) alpha (alpha / 2) P.k / 2)
      ⌈(NW : Real) / 8⌉₊ = m := ⟨_, rfl⟩
  have hmpow : (N : Real) ^ P.MExp alpha ≤ m := by
    have hcov := coverWidth_div8_powerLB (uExp P.V P.D (P.Delta alpha) (P.B alpha))
      (P.Rho1 alpha / 2) hEm
    have hcomp := WidthPowerLB.comp hnest hcov haN (by positivity) hNT (by norm_num)
    have h := hcomp N hNM
    have hm' : coverWidth (uExp P.V P.D (P.Delta alpha) (P.B alpha)) (P.Rho1 alpha / 2)
        ⌈((nestW (fun _ => P.C alpha) (fun _ => P.W alpha) (2 ^ P.k - 1)
          (P.T2 alpha) N : Nat) : Real) / 8⌉₊ = m := by
      have hNW' : nestW (fun _ => P.C alpha) (fun _ => P.W alpha) (2 ^ P.k - 1) (P.T2 alpha) N =
          NW := hNW
      rw [hNW']; exact hm
    have h' : (N : Real) ^ P.MExp alpha ≤
        (coverWidth (uExp P.V P.D (P.Delta alpha) (P.B alpha)) (P.Rho1 alpha / 2)
          ⌈((nestW (fun _ => P.C alpha) (fun _ => P.W alpha) (2 ^ P.k - 1)
            (P.T2 alpha) N : Nat) : Real) / 8⌉₊ : Real) := h
    rw [hm'] at h'
    exact h'
  have hm1 : (1 : Real) ≤ m :=
    (Real.one_le_rpow (by linarith) hmE.le).trans hmpow
  have hmReq : P.MReq alpha ≤ m :=
    (le_rpow_of_rpow_inv_le hmE ((Nat.cast_nonneg _).trans (le_max_left _ _)) hNR).trans hmpow
  have hmb8 : 8 / P.Zeta alpha ≤ (m : Real) ^ P.Bexp alpha :=
    le_rpow_of_rpow_inv_le hb (by positivity)
      (((le_max_left _ _).trans (le_max_right _ _)).trans hmReq)
  have hmbρ : 4 / (P.Zeta alpha * P.Rho alpha ^ 3) ≤ (m : Real) ^ P.Bexp alpha :=
    le_rpow_of_rpow_inv_le hb (by positivity)
      (((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hmReq)
  have hmb16 : 16 / P.Zeta alpha ≤ (m : Real) ^ (P.Bexp alpha / 2) := by
    have h := ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hmReq
    apply le_rpow_of_rpow_inv_le (by positivity) (by positivity)
    simpa only [one_div_div] using h
  have hthr : (familyRecThr P.k P.K P.p (P.QM alpha) : Real) ≤ m := (le_max_left _ _).trans hmReq
  -- the final exponent
  have hρ1eq : singlePieceGlobalRho1 (P.C alpha) alpha (alpha / 2) P.k = P.Rho1 alpha := rfl
  have hthSeq : singlePieceTheta (spectrumPieceRho (fun t => t / 2) (P.Rho1 alpha)) 1 =
      P.ThS alpha := rfl
  have hcSeq : singlePieceGlobalC (fun _ => uCount P.V P.D) alpha (alpha / 2) P.k (P.ThS alpha) =
      P.CS alpha := rfl
  have hBudeq : globalBudget alpha (alpha / 2) P.k = P.B alpha := rfl
  have hZeq : section16Zeta alpha (alpha / 2) P.k = P.Zeta alpha := rfl
  have hDeq : section16Delta (section16ThetaOne alpha (alpha / 2) P.k) = P.Delta alpha := rfl
  have hFin : ∀ q : Nat,
      (q : Real) ≤ singlePieceGlobalQmax (fun _ => uCount P.V P.D) (P.C alpha) alpha (alpha / 2) P.k →
      (N : Real) ^ P.F alpha ≤
        coverWidth (uExp P.V P.D (alpha / 2) (P.B alpha)) (P.CS alpha)
          (coverWidth (uExp P.V P.D (alpha / 2) (P.B alpha)) (P.ThS alpha)
            ⌈spectrumCellWidth (P.Zeta alpha) m (familyRecExp P.k P.p q) / 8⌉₊) ∧
      2 * P.Bexp alpha ≤ familyRecExp P.k P.p q := by
    intro q hq
    have hqM : q ≤ P.QM alpha := Nat.le_floor hq
    have heps : 2 * P.Bexp alpha ≤ familyRecExp P.k P.p q := by
      unfold Bexp
      have := familyRecExp_antitone (k := P.k) hp hqM
      linarith
    refine ⟨?_, heps⟩
    have hSCW : (m : Real) ^ (P.Bexp alpha / 2) ≤
        spectrumCellWidth (P.Zeta alpha) m (familyRecExp P.k P.p q) / 8 :=
      spectrumCellWidth_div8_ge_rpow hζ (by exact_mod_cast hm1) heps hmb16
    let L : Nat := ⌈spectrumCellWidth (P.Zeta alpha) m (familyRecExp P.k P.p q) / 8⌉₊
    have hLge : (m : Real) ^ (P.Bexp alpha / 2) ≤ L := hSCW.trans (Nat.le_ceil _)
    have hin := coverWidth_powerLB (uExp P.V P.D (alpha / 2) (P.B alpha)) (P.ThS alpha)
      hEth.le L (by positivity)
    let X : Nat := coverWidth (uExp P.V P.D (alpha / 2) (P.B alpha)) (P.ThS alpha) L
    have hout := coverWidth_powerLB (uExp P.V P.D (alpha / 2) (P.B alpha)) (P.CS alpha)
      hEc.le X (by positivity)
    have hNL := rpow_le_comp hNpos.le (half_pos hb).le hmpow hLge
    have hNX := rpow_le_comp hNpos.le hEth.le hNL hin
    have hNY := rpow_le_comp hNpos.le hEc.le hNX hout
    have hexp : P.F alpha =
        ((P.MExp alpha * (P.Bexp alpha / 2)) * P.Eth alpha) * P.Ec alpha := by
      unfold F; ring
    rw [hexp]
    exact hNY
  unfold SinglePieceModulusConditions SinglePieceGlobalScale singlePieceGlobalWidth
  simp only [hρ1eq, hthSeq, hcSeq, hBudeq, hZeq, hDeq]
  refine ⟨hodd, hN156, ?_, m, ⟨by rw [hNW]; exact_mod_cast hNW4, by exact_mod_cast hm1,
    by rw [hNW]; exact le_of_eq hm.symm, ?_⟩, ?_⟩
  · -- `4 ≤ N^e`
    have h6 := le_rpow_of_rpow_inv_le he (by norm_num) hN6
    linarith
  · intro q hq
    obtain ⟨hFq, heps⟩ := hFin q hq
    have hqM : q ≤ P.QM alpha := Nat.le_floor hq
    have hthrq : (familyRecThr P.k P.K P.p q : Real) ≤ familyRecThr P.k P.K P.p (P.QM alpha) :=
      Nat.cast_le.mpr (familyRecThr_mono (by omega) hqM)
    have hSCWq := spectrumCellWidth_mono_exp hζ.le (by exact_mod_cast hm1) heps
    rw [spectrumCellWidth_eq] at hSCWq
    rw [show 2 * P.Bexp alpha / 2 = P.Bexp alpha by ring] at hSCWq
    refine ⟨Nat.cast_le.mp (hthrq.trans hthr), ?_, ?_, ?_⟩
    · have := mul_le_mul_of_nonneg_left hmb8 (by positivity : (0 : Real) ≤ P.Zeta alpha / 2)
      have h4 : P.Zeta alpha / 2 * (8 / P.Zeta alpha) = 4 := by field_simp; ring
      linarith
    · have := mul_le_mul_of_nonneg_left hmbρ (by positivity : (0 : Real) ≤ P.Zeta alpha / 2)
      have h2 : P.Zeta alpha / 2 * (4 / (P.Zeta alpha * P.Rho alpha ^ 3)) = 2 / P.Rho alpha ^ 3 := by
        field_simp; ring
      have hρ3 : 0 < P.Rho alpha ^ 3 := by positivity
      have hge : 2 / P.Rho alpha ^ 3 ≤
          spectrumCellWidth (P.Zeta alpha) m (familyRecExp P.k P.p q) := by linarith
      have := mul_le_mul_of_nonneg_left hge hρ3.le
      rw [mul_div_cancel₀ _ hρ3.ne'] at this
      exact this
    · have hN8' : (8 : Real) ^ (1 / (P.F alpha / 2)) ≤ N := by
        rw [show 1 / (P.F alpha / 2) = 2 / P.F alpha by field_simp]
        exact hN8
      have h8 := le_rpow_of_rpow_inv_le (by positivity : 0 < P.F alpha / 2) (by norm_num) hN8'
      have hNF : (8 : Real) ≤ (N : Real) ^ P.F alpha := by
        have h1 : (1 : Real) ≤ (N : Real) ^ (P.F alpha / 2) :=
          Real.one_le_rpow (by linarith) (by positivity)
        have hsplit : (N : Real) ^ P.F alpha =
            (N : Real) ^ (P.F alpha / 2) * (N : Real) ^ (P.F alpha / 2) := by
          rw [← Real.rpow_add hNpos]; ring_nf
        rw [hsplit]
        exact h8.trans (le_mul_of_one_le_right (by linarith) h1)
      have h2 := hNF.trans hFq
      exact (Nat.cast_le (α := Real)).mp (by rw [Nat.cast_ofNat]; linarith)
  · intro q hq
    obtain ⟨hFq, -⟩ := hFin q hq
    have h6 := le_rpow_of_rpow_inv_le he (by norm_num) hN6
    have hN8' : (8 : Real) ^ (1 / (P.F alpha / 2)) ≤ N := by
      rw [show 1 / (P.F alpha / 2) = 2 / P.F alpha by field_simp]
      exact hN8
    have h8 := le_rpow_of_rpow_inv_le (by positivity : 0 < P.F alpha / 2) (by norm_num) hN8'
    have hx4 : ((N : Real) ^ P.Eloc alpha) ^ 4 / 8 ≤ (N : Real) ^ P.F alpha := by
      have hpow4 : ((N : Real) ^ P.Eloc alpha) ^ 4 = (N : Real) ^ (P.F alpha / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; unfold Eloc; push_cast; ring_nf
      rw [hpow4]
      have hsplit : (N : Real) ^ P.F alpha =
          (N : Real) ^ (P.F alpha / 2) * (N : Real) ^ (P.F alpha / 2) := by
        rw [← Real.rpow_add hNpos]; ring_nf
      have h0 : 0 ≤ (N : Real) ^ (P.F alpha / 2) := Real.rpow_nonneg hNpos.le _
      rw [hsplit]
      have hx8 : (N : Real) ^ (P.F alpha / 2) / 8 ≤ (N : Real) ^ (P.F alpha / 2) := by
        linarith
      exact hx8.trans (le_mul_of_one_le_right h0 (by linarith))
    exact nat_sqrt_pred_pred_ge h6 (hx4.trans hFq)

end GenParams

end LeanProofs.GowersSzemeredi
