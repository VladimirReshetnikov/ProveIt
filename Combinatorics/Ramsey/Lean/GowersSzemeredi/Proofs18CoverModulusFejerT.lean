import GowersSzemeredi.Proofs18CoverExponentsFejer
import GowersSzemeredi.Proofs18TightClassesFejerT
import GowersSzemeredi.Proofs18FejerEnvelopeBaseQ
import GowersSzemeredi.Proofs18CoverTightBase

/-! **The Section 18 step at the exact class table `tDeg`** (Notes L.16k),
part 1: `GenParamsT` and the scale conditions. Generated from
`Proofs18CoverModulusFejerS`, with the covers at `uDegT l = 2^tDeg l`
(`polyCoverAt_classT`). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem uDegT_eq (l : Nat) : uDegT l = 2 ^ tDeg l := rfl

theorem uDegT_le_pow {l k : Nat} (hl : l ≤ k) : uDegT l ≤ 2 ^ tDeg k := by
  rw [uDegT_eq]; exact Nat.pow_le_pow_right (by norm_num) (tDeg_mono hl)

/-- The η side condition `3(k+4)²` sits inside the base budget. -/
theorem sq_le_fixDegQ (k : Nat) : 3 * (k + 4) ^ 2 ≤ fixDegQ k + 64 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · decide
  · rw [fixDegQ_eq hk]
    rcases Nat.lt_or_ge k 4 with h | h
    · interval_cases k <;> norm_num
    · have h1 := sq_le_two_pow_four k h
      have h2 : 2 ^ (k + 4) = 16 * 2 ^ k := two_pow_four_mul k
      omega

/-! ### The parameters -/

/-- The data of the single-piece step with the joint-cover remainder in dimension `k`. -/
structure GenParamsT where
  /-- The base of the cover controls. -/
  V : Real
  /-- The dimension of the step. -/
  k : Nat
  /-- The recurrence threshold constant in dimension `k`. -/
  K : Nat
  /-- The recurrence exponent constant in dimension `k`. -/
  p : Nat
  /-- The fixed-parameter exponent. -/
  μ0 : Nat

namespace GenParamsT

variable (P : GenParamsT) (alpha : Real)

/-- The budget `globalBudgetW θ₁′ k`. -/
def B : Real := globalBudgetW (fejerThetaOne alpha (alpha / 2) P.k) P.k
/-- The width exponent of the base cover in face dimension `l`. -/
def Ewg (l : Nat) : Real → Real := uExp P.V (uDegT l) (alpha / 2) (P.B alpha)
/-- `θ₂/2`. -/
def T2 : Real := globalTheta2W (fejerThetaOne alpha (alpha / 2) P.k)
/-- The joint-cover remainder density `ρ₁`. -/
def Rho1 : Real := coverRho1W (fun l => uCount P.V (uDegT l)) (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2) P.k
/-- `δ(θ₁)`. -/
def Delta : Real := section16Delta (fejerThetaOne alpha (alpha / 2) P.k)
/-- The exponent of the spectrum-scale cover. -/
def Em : Real := uExp P.V (uDegT P.k) (P.Delta alpha) (P.B alpha) (P.Rho1 alpha / 2 / 2)
/-- The exponent of the remainder width. -/
def NestExp : Real := coverExpW (fun l => uExp P.V (uDegT l)) (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2) P.k
/-- The exponent of `m` in `N`. -/
def MExp : Real := P.NestExp alpha * (P.Em alpha / 2)
/-- The threshold for `m ≥ N^MExp`. -/
def MThr : Real := max ((1 : Real)) (64 ^ (1 / P.NestExp alpha))
/-- The worst spectrum count. -/
def QM : Nat :=
  ⌊singlePieceGlobalQmaxF (fun l => uCount P.V (uDegT l)) alpha (alpha / 2)
    P.k⌋₊
/-- The exponent of `m` in the spectrum cell width. -/
def Bexp : Real := familyRecExp P.k P.p (P.QM alpha) / 2
/-- The Bohr radius. -/
def Zeta : Real := tightZeta (fejerThetaOne alpha (alpha / 2) P.k / 4)
/-- The spectrum density. -/
def Rho : Real := spectrumPieceRho (fun t => t / 2) (P.Rho1 alpha)
/-- The slice density. -/
def ThS : Real := singlePieceTheta (P.Rho alpha) 1
/-- The slice control. -/
def CS : Real :=
  singlePieceGlobalF (fun l => uCount P.V (uDegT l)) alpha (alpha / 2) P.k (P.ThS alpha)
/-- The first slice exponent. -/
def Eth : Real := uExp P.V (uDegT P.k) (alpha / 2) (P.B alpha) (P.ThS alpha / 2)
/-- The second slice exponent. -/
def Ec : Real := uExp P.V (uDegT P.k) (alpha / 2) (P.B alpha) (P.CS alpha / 2)
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
  max (max 3 (fejerProductThreshold P.k (alpha / 2) (alpha / 2)))
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
    (0 < P.NestExp alpha ∧ P.NestExp alpha ≤ 1 ∧ 1 ≤ (1 : Real)) ∧
    (0 < P.Bexp alpha ∧ P.Bexp alpha ≤ 1) ∧ (0 < P.Zeta alpha) ∧
    (∀ l s, 0 < s → s ≤ 1 → 0 < P.Ewg alpha l s ∧ P.Ewg alpha l s ≤ 1) := by
  have ha1 : alpha ≤ 1 := by linarith
  have hg : 0 < alpha / 2 := half_pos ha
  have hg1 : alpha / 2 ≤ 1 := by linarith
  have hX : (1 : Real) ≤ 2 / alpha := by rw [le_div_iff₀ ha]; linarith
  obtain ⟨hθ₂, hθ₂1⟩ := section16ThetaTwo_pos_le_with (fejerThetaOne_bounds P.k ha (by linarith) (half_pos ha) (by linarith)).1 (fejerThetaOne_bounds P.k ha (by linarith) (half_pos ha) (by linarith)).2
  have hB : 0 < P.B alpha ∧ P.B alpha ≤ 1 := by
    unfold B globalBudgetW
    have hden : (1 : Real) ≤ 2 * (2 ^ P.k + 1) := by
      have : (1 : Real) ≤ 2 ^ P.k := one_le_pow₀ (by norm_num)
      linarith
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by positivity)]
    linarith
  obtain ⟨-, -, hd0, hd1⟩ := section16_theta_delta_bounds_with (fejerThetaOne_bounds P.k ha (by linarith) (half_pos ha) (by linarith)).1 (fejerThetaOne_bounds P.k ha (by linarith) (half_pos ha) (by linarith)).2
  have hT2 : 0 < P.T2 alpha ∧ P.T2 alpha ≤ 1 := by
    unfold T2 globalTheta2W; exact ⟨by positivity, by linarith⟩
  have hEw : ∀ l s, 0 < s → s ≤ 1 → 0 < P.Ewg alpha l s ∧ P.Ewg alpha l s ≤ 1 :=
    fun l s hs hs1 => uExp_pos hV (uDegT l) hg hg1 hB.1 hB.2 hs hs1
  have hR1 : 0 < P.Rho1 alpha ∧ P.Rho1 alpha ≤ 1 :=
    coverRho1W_pos_le _ (fun l g t s _ _ => one_le_uCount P.V (uDegT l) g t s) (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2)
      P.k (fejerThetaOne_bounds P.k ha (by linarith) (half_pos ha) (by linarith)).1 (fejerThetaOne_bounds P.k ha (by linarith) (half_pos ha) (by linarith)).2
  have hR : 0 < P.Rho alpha ∧ P.Rho alpha ≤ 1 := by
    unfold Rho spectrumPieceRho
    refine ⟨by have := hR1.1; positivity, ?_⟩
    have : P.Rho1 alpha / 2 * (P.Rho1 alpha / 2 / 2) ≤ 1 * 1 :=
      mul_le_mul (by linarith [hR1.2]) (by linarith [hR1.2]) (by linarith [hR1.1]) zero_le_one
    linarith
  have hS : 0 < P.ThS alpha ∧ P.ThS alpha ≤ 1 := by
    unfold ThS singlePieceTheta
    refine ⟨by have := hR.1; positivity, ?_⟩
    have h3 : P.Rho alpha ^ 3 ≤ 1 := pow_le_one₀ hR.1.le hR.2
    rw [div_le_one (by positivity)]
    norm_num
    linarith
  have hCS : 0 < P.CS alpha ∧ P.CS alpha ≤ 1 := by
    have hq := uCount_pos hV (uDegT P.k) hg hg1 hB.1 hB.2 (half_pos hS.1) (by linarith [hS.2])
    have hq0 : 0 < uCount P.V (uDegT P.k) (alpha / 2) (P.B alpha) (P.ThS alpha / 2) :=
      lt_of_lt_of_le zero_lt_one hq
    have hs0 := hS.1
    have hs1 := hS.2
    show 0 < P.ThS alpha / 2 / uCount P.V (uDegT P.k) (alpha / 2) (P.B alpha) (P.ThS alpha / 2) ∧
      P.ThS alpha / 2 / uCount P.V (uDegT P.k) (alpha / 2) (P.B alpha) (P.ThS alpha / 2) ≤ 1
    exact ⟨div_pos (half_pos hs0) hq0, (div_le_one hq0).mpr (by linarith)⟩
  have hEm : 0 < P.Em alpha ∧ P.Em alpha ≤ 1 :=
    uExp_pos hV (uDegT P.k) hd0 hd1 hB.1 hB.2 (by have := hR1.1; positivity) (by linarith [hR1.2])
  have hEth : 0 < P.Eth alpha ∧ P.Eth alpha ≤ 1 :=
    uExp_pos hV (uDegT P.k) hg hg1 hB.1 hB.2 (half_pos hS.1) (by linarith [hS.2])
  have hEc : 0 < P.Ec alpha ∧ P.Ec alpha ≤ 1 :=
    uExp_pos hV (uDegT P.k) hg hg1 hB.1 hB.2 (half_pos hCS.1) (by linarith [hCS.2])
  obtain ⟨n0, n1⟩ := coverExpW_pos_le (fun l => uExp P.V (uDegT l))
    (fun l g t s => uExp_pos_le P.V (uDegT l) g t s) (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2) P.k
  have nt : (1 : Real) ≤ 1 := le_rfl
  have hBx : 0 < P.Bexp alpha ∧ P.Bexp alpha ≤ 1 := by
    have h0 := familyRecExp_pos P.k P.p (P.QM alpha) hp
    have h1 := familyRecExp_le_one P.k P.p (P.QM alpha) hp
    unfold Bexp
    exact ⟨by positivity, by linarith⟩
  obtain ⟨hz, -⟩ := tightZeta_pos_le_half (fejerThetaOne_bounds P.k ha (by linarith) (half_pos ha) (by linarith)).1 (by linarith [(fejerThetaOne_bounds P.k ha (by linarith) (half_pos ha) (by linarith)).2])
  exact ⟨hB, ⟨hd0, hd1⟩, hT2, hR1, hR, hS, hCS, hEm, hEth, hEc, ⟨n0, n1, nt⟩, hBx, hz, hEw⟩

/-- The localization exponent lies in `(0, 1/2]`. -/
theorem Eloc_pos_le (hV : 1 ≤ P.V) (hp : 0 < P.p) {alpha : Real} (ha : 0 < alpha)
    (haHalf : alpha ≤ 1 / 2) :
    0 < P.Eloc alpha ∧ P.Eloc alpha ≤ 1 / 2 ∧ 0 < P.F alpha ∧ P.F alpha ≤ 1 ∧
      0 < P.MExp alpha ∧ P.MExp alpha ≤ 1 := by
  obtain ⟨-, -, -, -, -, -, -, ⟨hEm, hEm'⟩, ⟨hEth, hEth'⟩, ⟨hEc, hEc'⟩, ⟨n0, n1, -⟩,
    ⟨hBx, hBx'⟩, -, -⟩ := P.ranges hV hp ha haHalf
  have hm : 0 < P.MExp alpha ∧ P.MExp alpha ≤ 1 := by
    unfold MExp
    refine ⟨mul_pos n0 (by positivity), ?_⟩
    calc P.NestExp alpha * (P.Em alpha / 2) ≤ 1 * 1 :=
          mul_le_mul n1 (by linarith) (by positivity) zero_le_one
      _ = 1 := one_mul 1
  have hEE : 0 < P.Eth alpha * P.Ec alpha ∧ P.Eth alpha * P.Ec alpha ≤ 1 :=
    ⟨mul_pos hEth hEc, (mul_le_mul hEth' hEc' hEc.le zero_le_one).trans (by norm_num)⟩
  have hin : 0 < P.Bexp alpha * (P.Eth alpha * P.Ec alpha) / 2 ∧
      P.Bexp alpha * (P.Eth alpha * P.Ec alpha) / 2 ≤ 1 := by
    refine ⟨div_pos (mul_pos hBx hEE.1) (by norm_num), ?_⟩
    have : P.Bexp alpha * (P.Eth alpha * P.Ec alpha) ≤ 1 * 1 :=
      mul_le_mul hBx' hEE.2 hEE.1.le zero_le_one
    linarith
  have hF : 0 < P.F alpha ∧ P.F alpha ≤ 1 := by
    unfold F
    refine ⟨mul_pos hm.1 hin.1, ?_⟩
    calc P.MExp alpha * (P.Bexp alpha * (P.Eth alpha * P.Ec alpha) / 2) ≤ 1 * 1 :=
          mul_le_mul hm.2 hin.2 hin.1.le zero_le_one
      _ = 1 := one_mul 1
  unfold Eloc
  exact ⟨by linarith [hF.1], by linarith [hF.2], hF.1, hF.2, hm.1, hm.2⟩

/-- **The scale conditions of the step hold above `Tloc`.** -/
theorem modulus_conditions (hV : 1 ≤ P.V) (hK : 2 ≤ P.K) (hp : 0 < P.p) {alpha : Real}
    (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2)
    (N : Nat) [NeZero N] [Fact N.Prime] (hN : P.Tloc alpha ≤ N) :
    SinglePieceModulusConditionsF (fun l => uCount P.V (uDegT l)) (fun l => uExp P.V (uDegT l))
      alpha P.k (familyRecExp P.k P.p) (familyRecThr P.k P.K P.p)
      (P.Eloc alpha) N := by
  classical
  obtain ⟨⟨hB0, hB1⟩, ⟨hd0, hd1⟩, ⟨ht2, ht21⟩, ⟨hρ1, hρ1'⟩, ⟨hρ, hρ'⟩, ⟨hthS, hthS'⟩,
    ⟨hcS, hcS'⟩, ⟨hEm, hEm'⟩, ⟨hEth, hEth'⟩, ⟨hEc, hEc'⟩, ⟨haN, haN', hNT⟩, ⟨hb, hb'⟩, hζ,
    hEw⟩ := P.ranges hV hp ha haHalf
  obtain ⟨he, -, hF, -, hmE, -⟩ := P.Eloc_pos_le hV hp ha haHalf
  -- the modulus is large
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hT : ∀ X : Real, X ≤ P.Tloc alpha → X ≤ N := fun X hX => hX.trans hN
  have hN3 : (3 : Real) ≤ N := hT _ ((le_max_left _ _).trans (le_max_left _ _))
  have hN156 : fejerProductThreshold P.k (alpha / 2) (alpha / 2) ≤ N :=
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
  obtain ⟨NW, hNW⟩ : ∃ NW : Nat, coverRemWidthW (fun l => uExp P.V (uDegT l)) (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2) P.k N = NW := ⟨_, rfl⟩
  have hnest := coverRemWidthW_powerLB (fun l => uExp P.V (uDegT l)) (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2) P.k
  have hNWpow : (N : Real) ^ P.NestExp alpha ≤ NW := by
    have h : (N : Real) ^ P.NestExp alpha ≤
        ((coverRemWidthW (fun l => uExp P.V (uDegT l)) (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2) P.k N : Nat) : Real) :=
      hnest N (hNM.trans' (le_max_left _ _))
    have hNW' : coverRemWidthW (fun l => uExp P.V (uDegT l)) (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2) P.k N = NW :=
      hNW
    rw [hNW'] at h
    exact h
  have hNW4 : (4 : Real) ≤ NW :=
    (le_rpow_of_rpow_inv_le haN (by norm_num) hN4).trans hNWpow
  obtain ⟨m, hm⟩ : ∃ m : Nat, coverWidth (uExp P.V (uDegT P.k) (P.Delta alpha) (P.B alpha))
      (coverRho1W (fun l => uCount P.V (uDegT l)) (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2) P.k / 2)
      ⌈(NW : Real) / 8⌉₊ = m := ⟨_, rfl⟩
  have hmpow : (N : Real) ^ P.MExp alpha ≤ m := by
    have hcov := coverWidth_div8_powerLB (uExp P.V (uDegT P.k) (P.Delta alpha) (P.B alpha))
      (P.Rho1 alpha / 2) hEm
    have hcomp := WidthPowerLB.comp hnest hcov haN (by positivity) hNT (by norm_num)
    have h := hcomp N hNM
    have hm' : coverWidth (uExp P.V (uDegT P.k) (P.Delta alpha) (P.B alpha)) (P.Rho1 alpha / 2)
        ⌈((coverRemWidthW (fun l => uExp P.V (uDegT l)) (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2) P.k N : Nat) : Real) / 8⌉₊ = m := by
      have hNW' : coverRemWidthW (fun l => uExp P.V (uDegT l)) (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2) P.k N =
          NW := hNW
      rw [hNW']; exact hm
    have h' : (N : Real) ^ P.MExp alpha ≤
        (coverWidth (uExp P.V (uDegT P.k) (P.Delta alpha) (P.B alpha)) (P.Rho1 alpha / 2)
          ⌈((coverRemWidthW (fun l => uExp P.V (uDegT l)) (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2) P.k N : Nat) : Real) / 8⌉₊ : Real) := h
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
  have hρ1eq : coverRho1W (fun l => uCount P.V (uDegT l)) (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2) P.k = P.Rho1 alpha := rfl
  have hthSeq : singlePieceTheta (spectrumPieceRho (fun t => t / 2) (P.Rho1 alpha)) 1 =
      P.ThS alpha := rfl
  have hcSeq : singlePieceGlobalF (fun l => uCount P.V (uDegT l)) alpha (alpha / 2) P.k (P.ThS alpha) =
      P.CS alpha := rfl
  have hBudeq : globalBudgetW (fejerThetaOne alpha (alpha / 2) P.k) P.k = P.B alpha := rfl
  have hZeq : tightZeta (fejerThetaOne alpha (alpha / 2) P.k / 4) = P.Zeta alpha := rfl
  have hDeq : section16Delta (fejerThetaOne alpha (alpha / 2) P.k) = P.Delta alpha := rfl
  have hFin : ∀ q : Nat,
      (q : Real) ≤ singlePieceGlobalQmaxF (fun l => uCount P.V (uDegT l)) alpha (alpha / 2) P.k →
      (N : Real) ^ P.F alpha ≤
        coverWidth (uExp P.V (uDegT P.k) (alpha / 2) (P.B alpha)) (P.CS alpha)
          (coverWidth (uExp P.V (uDegT P.k) (alpha / 2) (P.B alpha)) (P.ThS alpha)
            ⌈spectrumCellWidth (P.Zeta alpha) m (familyRecExp P.k P.p q) / 8⌉₊) ∧
      2 * P.Bexp alpha ≤ familyRecExp P.k P.p q := by
    intro q hq
    have hqM : q ≤ P.QM alpha := Nat.le_floor hq
    have heps : 2 * P.Bexp alpha ≤ familyRecExp P.k P.p q := by
      unfold Bexp
      have := familyRecExp_antitone (k := P.k) hp hqM
      linarith
    refine ⟨?_, heps⟩
    have hm0 : 0 ≤ (m : Real) ^ (P.Bexp alpha / 2) := Real.rpow_nonneg (by linarith) _
    have hSCW : (m : Real) ^ (P.Bexp alpha / 2) ≤
        spectrumCellWidth (P.Zeta alpha) m (familyRecExp P.k P.p q) / 8 := by
      have hmono := spectrumCellWidth_mono_exp hζ.le (by exact_mod_cast hm1) heps
      rw [spectrumCellWidth_eq] at hmono
      have hpow : (m : Real) ^ (2 * P.Bexp alpha / 2) =
          (m : Real) ^ (P.Bexp alpha / 2) * (m : Real) ^ (P.Bexp alpha / 2) := by
        rw [← Real.rpow_add (by linarith)]; ring_nf
      rw [hpow] at hmono
      have hk : 16 ≤ P.Zeta alpha * (m : Real) ^ (P.Bexp alpha / 2) := by
        have := mul_le_mul_of_nonneg_left hmb16 hζ.le
        have h16 : P.Zeta alpha * (16 / P.Zeta alpha) = 16 := by field_simp
        linarith
      have hprod := mul_le_mul_of_nonneg_left hk hm0
      have hxx : (m : Real) ^ (P.Bexp alpha / 2) *
          (P.Zeta alpha * (m : Real) ^ (P.Bexp alpha / 2)) =
          P.Zeta alpha / 2 *
            ((m : Real) ^ (P.Bexp alpha / 2) * (m : Real) ^ (P.Bexp alpha / 2)) * 2 := by ring
      rw [hxx] at hprod
      linarith
    obtain ⟨L, hLdef⟩ : ∃ L : Nat,
        ⌈spectrumCellWidth (P.Zeta alpha) m (familyRecExp P.k P.p q) / 8⌉₊ = L := ⟨_, rfl⟩
    rw [hLdef]
    have hLge : (m : Real) ^ (P.Bexp alpha / 2) ≤ L := by
      rw [← hLdef]; exact hSCW.trans (Nat.le_ceil _)
    have hin := coverWidth_powerLB (uExp P.V (uDegT P.k) (alpha / 2) (P.B alpha)) (P.ThS alpha)
      hEth.le L (by positivity)
    obtain ⟨X, hXdef⟩ : ∃ X : Nat,
        coverWidth (uExp P.V (uDegT P.k) (alpha / 2) (P.B alpha)) (P.ThS alpha) L = X := ⟨_, rfl⟩
    rw [hXdef] at hin
    rw [hXdef]
    have hout := coverWidth_powerLB (uExp P.V (uDegT P.k) (alpha / 2) (P.B alpha)) (P.CS alpha)
      hEc.le X (by positivity)
    refine le_trans ?_ hout
    have hstep1 : ((m : Real) ^ (P.Bexp alpha / 2)) ^ P.Eth alpha ≤ (L : Real) ^ P.Eth alpha :=
      Real.rpow_le_rpow hm0 hLge hEth.le
    have hstep2 : (((m : Real) ^ (P.Bexp alpha / 2)) ^ P.Eth alpha) ^ P.Ec alpha ≤
        (X : Real) ^ P.Ec alpha :=
      Real.rpow_le_rpow (Real.rpow_nonneg hm0 _) (hstep1.trans hin) hEc.le
    refine le_trans ?_ hstep2
    have hNm : ((N : Real) ^ P.MExp alpha) ^ (P.Bexp alpha / 2 * P.Eth alpha * P.Ec alpha) ≤
        (m : Real) ^ (P.Bexp alpha / 2 * P.Eth alpha * P.Ec alpha) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hNpos.le _) hmpow
        (mul_nonneg (mul_nonneg (by positivity) hEth.le) hEc.le)
    rw [← Real.rpow_mul (by linarith), ← Real.rpow_mul (by linarith)]
    rw [← Real.rpow_mul hNpos.le] at hNm
    have hexp1 : P.F alpha =
        P.MExp alpha * (P.Bexp alpha / 2 * (P.Eth alpha * P.Ec alpha)) := by
      unfold F; ring
    have e3 : P.Bexp alpha / 2 * P.Eth alpha * P.Ec alpha =
        P.Bexp alpha / 2 * (P.Eth alpha * P.Ec alpha) := by ring
    rw [e3] at hNm
    rw [hexp1]
    exact hNm
  unfold SinglePieceModulusConditionsF SinglePieceGlobalScaleF singlePieceGlobalWidthF
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

end GenParamsT

end LeanProofs.GowersSzemeredi
