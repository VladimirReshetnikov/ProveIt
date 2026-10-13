import GowersSzemeredi.Proofs18FinalClasses
import GowersSzemeredi.Proofs18LengthSixScale

/-! **The final route, part 2: the joint-slice step at `tDegT3`** (Notes L.16-final).

The parameters `GenParamsJT3` of one single-piece inverse step over the classes
`tDegT3`, and the bounds on their density, exponents and thresholds
(Notes L.16q/y), extracted from the step modules (`assemble_final.py`). -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

/-- **The tight Bohr radius under the Fejér `θ₁` is polynomial**:
`ζ⁻¹ ≤ exp(X^(2^(5k+21)))`. -/
theorem zeta_gen_bounds_fejer5 (k : Nat) {alpha : Real} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < tightZeta (fejerThetaOne alpha (alpha / 2) k / 4) ∧
      (tightZeta (fejerThetaOne alpha (alpha / 2) k / 4))⁻¹ ≤
        Real.exp ((2 / alpha) ^ (2 ^ (5 * k + 21))) := by
  have hX := two_div_ge_two ha ha2
  obtain ⟨h0, -, hi⟩ := tightZeta_fejer_inv_le_gen (gamma := alpha / 2) (theta := alpha) k
    (half_pos ha) (by linarith) ha (by linarith)
  refine ⟨h0, hi.trans (Real.exp_le_exp.mpr ?_)⟩
  have hval : 2 / (alpha / 2 * alpha) = (2 / alpha) ^ 2 := by field_simp
  rw [hval, ← pow_mul]
  refine pow_le_pow_right₀ (by linarith) ?_
  have hF := fejerProductExponent_le k
  have h14 : 2 ^ 14 ≤ 2 ^ (5 * k + 14) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h21 : 2 ^ (5 * k + 21) = 128 * 2 ^ (5 * k + 14) := by
    rw [show 5 * k + 21 = (5 * k + 14) + 7 by ring, pow_add]; ring
  unfold fejerStepT
  omega

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

/-- **The Fejér Lemma 15.6 threshold is polynomial**: `≤ X^(2^(5k+21))`
(`lemma156_gen_le_fejer` weakens the same estimate to `2^(k+4) + 4k + 13`). -/
theorem lemma156_gen_le_fejer5 {k : Nat} (hk : 1 ≤ k) {alpha : Real} (ha : 0 < alpha)
    (ha2 : alpha ≤ 1 / 2) :
    fejerProductThreshold k (alpha / 2) (alpha / 2) ≤ (2 / alpha) ^ (2 ^ (5 * k + 21)) := by
  have ha1 : alpha ≤ 1 := by linarith
  have hX := two_div_ge_two ha ha2
  have h := fejerProductThreshold_le_gen (gamma := alpha / 2) (theta := alpha) hk (half_pos ha)
    (by linarith) ha ha1
  have hu : 2 / (alpha / 2 * alpha) = (2 / alpha) ^ 2 := by field_simp
  rw [hu, ← pow_mul] at h
  refine h.trans (pow_le_pow_right₀ (le_trans (by norm_num) hX) ?_)
  have hP := fejerStepP_le k
  calc 2 * fejerStepP k ≤ 2 * 2 ^ (5 * k + 20) := Nat.mul_le_mul_left 2 hP
    _ = 2 ^ (5 * k + 21) := by rw [pow_succ]; ring

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

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
  have h20 : 0 < θ / 2 := half_pos hθ0
  have h21 : θ / 2 ≤ 1 := by linarith
  have h2i : (θ / 2)⁻¹ ≤ X ^ (2 ^ (m + 1)) := by
    rw [inv_div, div_eq_mul_inv]
    exact pw_mul hX (by norm_num) (inv_pos.mpr hθ0).le (hX.trans (pw_X hX _)) hθi
  obtain ⟨hc0, -, hci⟩ := GenParams.cS_step hX hc h20 h21 h2i ha0 hb0 (by omega)
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
  have hsq := pw_mul hX (inv_pos.mpr hc0).le (inv_pos.mpr hc0).le hci hci
  have hinv : (8 * (c (θ / 2) * c (θ / 2)))⁻¹ ≤ (c (θ / 2))⁻¹ * (c (θ / 2))⁻¹ := by
    rw [mul_inv, mul_inv]
    have h0 : 0 ≤ (c (θ / 2))⁻¹ * (c (θ / 2))⁻¹ := by positivity
    nlinarith
  exact pw_mono hX (hinv.trans hsq) (by omega)

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

/-- The data of the single-piece step with the joint-cover remainder in dimension `k`. -/
structure GenParamsJT3 where
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

namespace GenParamsJT3

variable (P : GenParamsJT3) (alpha : Real)

/-- The budget `globalBudgetW θ₁′ k`. -/
def B : Real := globalBudgetW (fejerThetaOne alpha (alpha / 2) P.k) P.k

/-- The width exponent of the base cover in face dimension `l`. -/
def Ewg (l : Nat) : Real → Real := uExp P.V (uDegT3 l) (alpha / 2) (P.B alpha)

/-- `θ₂/2`. -/
def T2 : Real := globalTheta2W (fejerThetaOne alpha (alpha / 2) P.k)

/-- The joint-cover remainder density `ρ₁`. -/
def Rho1 : Real := coverRho1W (fun l => uCount P.V (uDegT3 l)) (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2) P.k

/-- `δ(θ₁)`. -/
def Delta : Real := section16Delta (fejerThetaOne alpha (alpha / 2) P.k)

/-- The exponent of the spectrum-scale cover. -/
def Em : Real := uExp P.V (uDegT3 P.k) (P.Delta alpha) (P.B alpha) (P.Rho1 alpha / 2 / 2)

/-- The exponent of the remainder width. -/
def NestExp : Real := coverExpW (fun l => uExp P.V (uDegT3 l)) (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2) P.k

/-- The exponent of `m` in `N`. -/
def MExp : Real := P.NestExp alpha * (P.Em alpha / 2)

/-- The threshold for `m ≥ N^MExp`. -/
def MThr : Real := max ((1 : Real)) (64 ^ (1 / P.NestExp alpha))

/-- The worst spectrum count. -/
def QM : Nat :=
  ⌊singlePieceGlobalQmaxF (fun l => uCount P.V (uDegT3 l)) alpha (alpha / 2)
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
  singlePieceGlobalF (fun l => uCount P.V (uDegT3 l)) alpha (alpha / 2) P.k (P.ThS alpha)

/-- The slice exponent `E(θ_S/4)`; the joint-slice width has exponent `Eth²`. -/
def Eth : Real := uExp P.V (uDegT3 P.k) (alpha / 2) (P.B alpha) (P.ThS alpha / 4)

/-- The exponent of the final width in `N`. -/
def F : Real := P.MExp alpha * (P.Bexp alpha * (P.Eth alpha * P.Eth alpha) / 2)

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
      (max (P.MReq alpha ^ (1 / P.MExp alpha)) (6 ^ (1 / P.Eloc alpha))))

/-- The parameter ranges used by the localization and modulus estimates. -/
theorem ranges (hp : 0 < P.p) {alpha : Real} (ha : 0 < alpha)
    (haHalf : alpha ≤ 1 / 2) :
    0 < P.Rho alpha ∧ (0 < P.Em alpha ∧ P.Em alpha ≤ 1) ∧
    (0 < P.Eth alpha ∧ P.Eth alpha ≤ 1) ∧
    (0 < P.NestExp alpha ∧ P.NestExp alpha ≤ 1) ∧
    (0 < P.Bexp alpha ∧ P.Bexp alpha ≤ 1) ∧ 0 < P.Zeta alpha := by
  have ha1 : alpha ≤ 1 := by linarith
  have hg : 0 < alpha / 2 := half_pos ha
  have hg1 : alpha / 2 ≤ 1 := by linarith
  obtain ⟨hθ0, hθ1⟩ := fejerThetaOne_bounds P.k ha ha1 hg hg1
  have hR1 : 0 < P.Rho1 alpha ∧ P.Rho1 alpha ≤ 1 :=
    coverRho1W_pos_le _ (fun l g t s _ _ => one_le_uCount P.V (uDegT3 l) g t s) (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2)
      P.k hθ0 hθ1
  have hR : 0 < P.Rho alpha := by
    unfold Rho spectrumPieceRho
    have := hR1.1
    positivity
  have hEm : 0 < P.Em alpha ∧ P.Em alpha ≤ 1 :=
    uExp_pos_le P.V (uDegT3 P.k) (P.Delta alpha) (P.B alpha) (P.Rho1 alpha / 2 / 2)
  have hEth : 0 < P.Eth alpha ∧ P.Eth alpha ≤ 1 :=
    uExp_pos_le P.V (uDegT3 P.k) (alpha / 2) (P.B alpha) (P.ThS alpha / 4)
  obtain ⟨n0, n1⟩ := coverExpW_pos_le (fun l => uExp P.V (uDegT3 l))
    (fun l g t s => uExp_pos_le P.V (uDegT3 l) g t s) (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2) P.k
  have hBx : 0 < P.Bexp alpha ∧ P.Bexp alpha ≤ 1 := by
    have h0 := familyRecExp_pos P.k P.p (P.QM alpha) hp
    have h1 := familyRecExp_le_one P.k P.p (P.QM alpha) hp
    unfold Bexp
    exact ⟨by positivity, by linarith⟩
  obtain ⟨hz, -⟩ := tightZeta_pos_le_half hθ0 (by linarith only [hθ1])
  exact ⟨hR, hEm, hEth, ⟨n0, n1⟩, hBx, hz⟩

/-- The localization exponent lies in `(0, 1/2]`. -/
theorem Eloc_pos_le (hV : 1 ≤ P.V) (hp : 0 < P.p) {alpha : Real} (ha : 0 < alpha)
    (haHalf : alpha ≤ 1 / 2) :
    0 < P.Eloc alpha ∧ P.Eloc alpha ≤ 1 / 2 ∧ 0 < P.F alpha ∧ P.F alpha ≤ 1 ∧
      0 < P.MExp alpha ∧ P.MExp alpha ≤ 1 := by
  obtain ⟨-, hEm, hEth, hN, hBx, -⟩ := P.ranges hp ha haHalf
  simpa only [Eloc, F, MExp] using
    localization_exponents_pos_le hN hEm hBx hEth hEth

/-- **The scale conditions of the step hold above `Tloc`.** -/
theorem modulus_conditions (hV : 1 ≤ P.V) (hK : 2 ≤ P.K) (hp : 0 < P.p) {alpha : Real}
    (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2)
    (N : Nat) [NeZero N] [Fact N.Prime] (hN : P.Tloc alpha ≤ N) :
    SinglePieceModulusConditionsFJ (fun l => uCount P.V (uDegT3 l)) (fun l => uExp P.V (uDegT3 l))
      alpha P.k (familyRecExp P.k P.p) (familyRecThr P.k P.K P.p)
      (P.Eloc alpha) N := by
  classical
  obtain ⟨hρ, ⟨hEm, -⟩, ⟨hEth, -⟩, ⟨haN, -⟩, ⟨hb, -⟩, hζ⟩ :=
    P.ranges hp ha haHalf
  obtain ⟨he, -, hF, -, hmE, -⟩ := P.Eloc_pos_le hV hp ha haHalf
  -- the modulus is large
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  simp only [Tloc, max_le_iff] at hN
  obtain ⟨⟨hN3, hN156⟩, hNM, hNR, hN6⟩ := hN
  have hprime : N.Prime := Fact.out
  have hodd : Odd N := hprime.odd_of_ne_two (by
    intro h2; rw [h2] at hN3; norm_num at hN3)
  -- the nested width and `m`
  let NW : Nat := coverRemWidthW (fun l => uExp P.V (uDegT3 l))
    (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2) P.k N
  have hnest := coverRemWidthW_powerLB (fun l => uExp P.V (uDegT3 l)) (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2) P.k
  have hNWpow : (N : Real) ^ P.NestExp alpha ≤ NW :=
    hnest N (hNM.trans' (le_max_left _ _))
  have hNW4 : (4 : Real) ≤ NW :=
    (by norm_num : (4 : Real) ≤ 64).trans
      ((le_rpow_of_rpow_inv_le haN (by norm_num) ((le_max_right _ _).trans hNM)).trans hNWpow)
  let m : Nat := coverWidth (uExp P.V (uDegT3 P.k) (P.Delta alpha) (P.B alpha))
    (P.Rho1 alpha / 2) ⌈(NW : Real) / 8⌉₊
  have hmpow : (N : Real) ^ P.MExp alpha ≤ m := by
    have hcov := coverWidth_div8_powerLB (uExp P.V (uDegT3 P.k) (P.Delta alpha) (P.B alpha))
      (P.Rho1 alpha / 2) hEm
    have hcomp := WidthPowerLB.comp hnest hcov haN (by positivity) le_rfl (by norm_num)
    exact hcomp N hNM
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
  have hρ1eq : coverRho1W (fun l => uCount P.V (uDegT3 l)) (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2) P.k = P.Rho1 alpha := rfl
  have hBudeq : globalBudgetW (fejerThetaOne alpha (alpha / 2) P.k) P.k = P.B alpha := rfl
  have hZeq : tightZeta (fejerThetaOne alpha (alpha / 2) P.k / 4) = P.Zeta alpha := rfl
  have hDeq : section16Delta (fejerThetaOne alpha (alpha / 2) P.k) = P.Delta alpha := rfl
  have hFin : ∀ q : Nat,
      (q : Real) ≤ singlePieceGlobalQmaxF (fun l => uCount P.V (uDegT3 l)) alpha (alpha / 2) P.k →
      (N : Real) ^ P.F alpha ≤
        jointSliceWidth (uExp P.V (uDegT3 P.k) (alpha / 2) (P.B alpha))
          (spectrumPieceRho (fun t => t / 2) (P.Rho1 alpha)) 1
            ⌈spectrumCellWidth (P.Zeta alpha) m (familyRecExp P.k P.p q) / 8⌉₊ ∧
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
    show (N : Real) ^ P.F alpha ≤ ((⌈(L : Real) ^ (P.Eth alpha * P.Eth alpha)⌉₊ : Nat) : Real)
    have hNL := rpow_le_comp hNpos.le (half_pos hb).le hmpow hLge
    have hNY := rpow_le_comp hNpos.le (mul_nonneg hEth.le hEth.le) hNL
      (Nat.le_ceil ((L : Real) ^ (P.Eth alpha * P.Eth alpha)))
    have hexp : P.F alpha =
        (P.MExp alpha * (P.Bexp alpha / 2)) * (P.Eth alpha * P.Eth alpha) := by
      unfold F; ring
    rw [hexp]
    exact hNY
  have h6pow : (6 : Real) ≤ (N : Real) ^ P.Eloc alpha :=
    le_rpow_of_rpow_inv_le he (by norm_num) hN6
  have hloc {L : Nat} (hL : (N : Real) ^ P.F alpha ≤ L) :
      2 ≤ L ∧ (N : Real) ^ P.Eloc alpha ≤ ((Nat.sqrt (L - 1) - 1 : Nat) : Real) :=
    localization_width_bounds (by linarith only [hN3]) hF.le h6pow hL
  unfold SinglePieceModulusConditionsFJ SinglePieceGlobalScaleFJ singlePieceGlobalWidthFJ
  simp only [hρ1eq, hBudeq, hZeq, hDeq]
  refine ⟨hodd, hN156, ?_, m, ⟨by exact_mod_cast hNW4, by exact_mod_cast hm1,
    le_rfl, ?_⟩, ?_⟩
  · -- `4 ≤ N^e`
    linarith only [h6pow]
  · intro q hq
    obtain ⟨hFq, heps⟩ := hFin q hq
    have hqM : q ≤ P.QM alpha := Nat.le_floor hq
    have hthrq : (familyRecThr P.k P.K P.p q : Real) ≤ familyRecThr P.k P.K P.p (P.QM alpha) :=
      Nat.cast_le.mpr (familyRecThr_mono (by omega) hqM)
    obtain ⟨hcell4, hcellrho⟩ :=
      spectrumCellWidth_scale_bounds hζ hρ (by exact_mod_cast hm1) heps hmb8 hmbρ
    exact ⟨Nat.cast_le.mp (hthrq.trans hthr), hcell4, hcellrho, (hloc hFq).1⟩
  · intro q hq
    obtain ⟨hFq, -⟩ := hFin q hq
    exact (hloc hFq).2

end GenParamsJT3

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

/-- `3(k+4)² ≤ 2·tDegT3 k + 6k + 35`: the side condition of `eta_step_small`
at the joint-slice density degree. -/
theorem sq_le_two_tDegT3 (k : Nat) : 3 * (k + 4) ^ 2 ≤ 2 * tDegT3 k + 6 * k + 35 := by
  rcases Nat.lt_or_ge k 15 with h | h
  · interval_cases k <;> decide
  · rw [tDegT3_eq_of_ge h]; omega

variable {alpha : Real}

/-- **The common precision of the vertex covers.** -/
theorem coverPrec_gen_bounds_fejerJT3 (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
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

namespace GenParamsJT3

variable (P : GenParamsJT3) (alpha : Real)

/-- The localization parameter `η` of the step. -/
def eta : Real := singlePieceEtaFJ (fun l => uCount P.V (uDegT3 l)) alpha P.k

/-- The parameter of the lower-degree bound. -/
def yIn : Real := (P.eta alpha / 2) / (2 * (P.k + 1 + 2 : Nat) : Real) ^ (P.k + 1 + 2)

/-- **The single-piece inverse step in dimension `k`, joint-cover remainder.** -/
theorem inverse_step (hV : 1 ≤ P.V) (hK : 2 ≤ P.K) (hp : 0 < P.p) (hk : 1 ≤ P.k)
    (hcov : ∀ l, 1 ≤ l → l ≤ P.k → PolyCoverAt l (uCount P.V (uDegT3 l)) (uExp P.V (uDegT3 l)))
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
  exact single_piece_inverse_step_global_cover_fejer_joint (Qb := fun l => uCount P.V (uDegT3 l))
    (Eb := fun l => uExp P.V (uDegT3 l)) hk ha haHalf hcov
    (fun l g t s _ _ => one_le_uCount P.V (uDegT3 l) g t s)
    (fun l g t s _ _ => (uExp_pos_le P.V (uDegT3 l) g t s).1)
    (fun l g t s _ _ => (uExp_pos_le P.V (uDegT3 l) g t s).2)
    (familyRecExp P.k P.p) (familyRecThr P.k P.K P.p)
    hretile he0 he hbound hb hs hs16 (fun N _ _ hN => P.modulus_conditions hV hK hp ha haHalf N hN)

variable {alpha}

theorem rho1_pos_le (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < P.Rho1 alpha ∧ P.Rho1 alpha ≤ 1 :=
  coverRho1W_pos_le _ (fun l g t s _ _ => one_le_uCount P.V (uDegT3 l) g t s) (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2)
    P.k (fejerThetaOne_bounds P.k ha (by linarith) (half_pos ha) (by linarith)).1 (fejerThetaOne_bounds P.k ha (by linarith) (half_pos ha) (by linarith)).2

/-- **One vertex count at the common precision.** -/
theorem vertex_uCount_le {μV : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) (hV : 1 ≤ P.V)
    (hVμ : P.V ≤ 2 ^ (2 ^ μV)) (hμ0 : max μV (pDeg P.k) + 2 ≤ P.μ0) {l : Nat} (hl : l ≤ P.k) :
    uCount P.V (uDegT3 l) (alpha / 2) (globalBudgetW (fejerThetaOne alpha (alpha / 2) P.k) P.k)
        (coverPrecW (fejerThetaOne alpha (alpha / 2) P.k) P.k) ≤
      (2 / alpha) ^ (2 ^ (P.μ0 + 1 + tDegT3 P.k)) := by
  have hX := two_div_ge_two ha ha2
  obtain ⟨hB0, hB1, hBi⟩ := budget_gen_bounds_fejerW P.k ha ha2
  obtain ⟨hs0, hs1, hsi⟩ := coverPrec_gen_bounds_fejerJT3 P.k ha ha2
  have hD : uDegT3 l ≤ 2 ^ (tDegT3 P.k) := uDegT3_le_pow hl
  have h := uCount_scale_le_deg (c := pDeg P.k + 1) hX hV hVμ (seven_le_pDeg _) hμ0 (half_pos ha) (by linarith)
    (GenParams.half_inv_le_deg (pDeg P.k) ha ha2) hB0 hB1 hBi hs0 hs1 hsi hD
  have hm : max P.μ0 (pDeg P.k + 1) = P.μ0 := by
    have := le_max_right μV (pDeg P.k)
    exact max_eq_left (by omega)
  rw [hm] at h
  exact h

/-- The log-degree of the joint-cover `ρ₁`. -/
def rhoDegJT3 (k μ0 : Nat) : Nat := max (tDegT3 k + μ0 + 3) (pDeg k + 1) + k

theorem rhoDegJT3_ge (k μ0 : Nat) :
    tDegT3 k + μ0 + 3 ≤ rhoDegJT3 k μ0 ∧ pDeg k + 1 ≤ rhoDegJT3 k μ0 := by
  unfold rhoDegJT3
  have h1 := le_max_left (tDegT3 k + μ0 + 3) (pDeg k + 1)
  have h2 := le_max_right (tDegT3 k + μ0 + 3) (pDeg k + 1)
  omega

/-- **The joint-cover density**: `ρ₁⁻¹ ≤ X^(2^rhoDegJT3)`, in every dimension. -/
theorem rho1_inv_leJT3 {μV : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) (hV : 1 ≤ P.V)
    (hVμ : P.V ≤ 2 ^ (2 ^ μV)) (hμ0 : max μV (pDeg P.k) + 2 ≤ P.μ0) :
    (P.Rho1 alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ rhoDegJT3 P.k P.μ0) := by
  have hX := two_div_ge_two ha ha2
  obtain ⟨ht0, -, hti⟩ := T2_gen_bounds_fejerW P.k ha ha2
  have hf := le_max_right μV (pDeg P.k)
  have hfk : P.k + 1 ≤ pDeg P.k := by
    have := five_k_le_pDeg P.k; omega
  have hka : P.k + 2 ≤ P.μ0 + 1 + tDegT3 P.k := by omega
  -- the product of the vertex counts
  have hcc : coverCountW (fun l => uCount P.V (uDegT3 l)) (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2) P.k ≤
      (2 / alpha) ^ (2 ^ (P.μ0 + 1 + tDegT3 P.k + P.k)) := by
    unfold coverCountW
    refine prod_le_pw _ hX (fun e _ => le_trans zero_le_one (le_trans (one_le_uCount _ _ _ _ _)
      (le_max_left _ _))) (fun e he => max_le ?_ (three_pow_le_pw hX hka)) (nonTop_card_le P.k)
    exact P.vertex_uCount_le ha ha2 hV hVμ hμ0 (nonTop_card_le_k (Finset.mem_filter.mp he).2)
  have hcc0 := coverCountW_pos (fun l => uCount P.V (uDegT3 l))
    (fun l g t s _ _ => one_le_uCount P.V (uDegT3 l) g t s) (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2) P.k
  have heq : (P.Rho1 alpha)⁻¹ = 2 * (globalTheta2W (fejerThetaOne alpha (alpha / 2) P.k))⁻¹ *
      coverCountW (fun l => uCount P.V (uDegT3 l)) (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2) P.k := by
    show (coverRho1W (fun l => uCount P.V (uDegT3 l)) (fejerThetaOne alpha (alpha / 2) P.k) (alpha / 2) P.k)⁻¹ = _
    unfold coverRho1W
    field_simp
  rw [heq]
  have h2 : 2 * (globalTheta2W (fejerThetaOne alpha (alpha / 2) P.k))⁻¹ ≤ (2 / alpha) ^ (2 ^ (pDeg P.k + 1)) :=
    pw_mul hX (by norm_num) (inv_pos.mpr ht0).le (hX.trans (pw_X hX _)) hti
  have h := pw_mul' hX (by positivity) hcc0.le h2 hcc
  refine pw_mono hX h ?_
  have h1 := rhoDegJT3_ge P.k P.μ0
  have hm : max (pDeg P.k + 1) (P.μ0 + 1 + tDegT3 P.k + P.k) =
      P.μ0 + 1 + tDegT3 P.k + P.k := max_eq_right (by omega)
  rw [hm]
  unfold rhoDegJT3
  have := le_max_left (tDegT3 P.k + P.μ0 + 3) (pDeg P.k + 1)
  omega

/-- **The joint-cover width exponent.** -/
theorem nestExp_inv_leJT3 {μV : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) (hV : 1 ≤ P.V)
    (hVμ : P.V ≤ 2 ^ (2 ^ μV)) (hμ0 : max μV (pDeg P.k) + 2 ≤ P.μ0) :
    (P.NestExp alpha)⁻¹ ≤
      (2 / alpha) ^ (2 ^ (rhoDegJT3 P.k P.μ0 + tDegT3 P.k + 3 + P.k)) := by
  have hX := two_div_ge_two ha ha2
  have hf := le_max_right μV (pDeg P.k)
  have hfk : P.k + 1 ≤ pDeg P.k := by
    have := five_k_le_pDeg P.k; omega
  have hka : P.k + 3 ≤ P.μ0 + 1 + tDegT3 P.k := by omega
  refine pw_mono hX (a := P.μ0 + 1 + tDegT3 P.k + 1 + P.k) ?_ ?_
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
  · have := rhoDegJT3_ge P.k P.μ0
    omega

/-- The log-degree of the input parameter `yIn`. -/
def densDegJT3 (k μ0 : Nat) : Nat := rhoDegJT3 k μ0 + tDegT3 k + 11

/-- **The input parameter of the lower-degree bound**, joint-cover remainder. -/
theorem yIn_boundsJT3 {μV : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (hV : 1 ≤ P.V) (hVμ : P.V ≤ 2 ^ (2 ^ μV)) (hμ0 : max μV (pDeg P.k) + 2 ≤ P.μ0) :
    0 < P.eta alpha ∧ P.eta alpha ≤ alpha / 8 ∧
      (P.eta alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ (rhoDegJT3 P.k P.μ0 + tDegT3 P.k + 10)) ∧
      0 < P.yIn alpha ∧ P.yIn alpha ≤ alpha ∧
      (P.yIn alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ densDegJT3 P.k P.μ0) := by
  have hX := two_div_ge_two ha ha2
  have hri := P.rho1_inv_leJT3 ha ha2 hV hVμ hμ0
  set k := P.k with hkdef
  set μD := tDegT3 k with hμDdef
  have hρ1 : μD + P.μ0 + 3 ≤ rhoDegJT3 k P.μ0 := (rhoDegJT3_ge k P.μ0).1
  have hρ2 : pDeg k + 1 ≤ rhoDegJT3 k P.μ0 := (rhoDegJT3_ge k P.μ0).2
  have hbase := baseCFW_recipPowerLB (D := uDegT3 k) (k := k) ha ha2 hV hVμ hμ0
  have hD : uDegT3 k ≤ 2 ^ μD := le_rfl
  have ha0 : uDegT3 k * 2 ^ P.μ0 + 1 ≤ 2 ^ (μD + P.μ0 + 1) := by
    have h1 : uDegT3 k * 2 ^ P.μ0 ≤ 2 ^ μD * 2 ^ P.μ0 := Nat.mul_le_mul_right _ hD
    have h2 : 2 ^ (μD + P.μ0 + 1) = 2 * (2 ^ μD * 2 ^ P.μ0) := by rw [pow_add, pow_add]; ring
    have h3 : 1 ≤ 2 ^ μD * 2 ^ P.μ0 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hb0 : uDegT3 k + 1 ≤ 2 ^ (μD + 1) := by
    have : 2 ^ (μD + 1) = 2 * 2 ^ μD := by rw [pow_succ]; ring
    have := Nat.one_le_two_pow (n := μD)
    omega
  -- `ρ₁`
  obtain ⟨hr0, hr1⟩ := P.rho1_pos_le ha ha2
  -- `ρ`, `θ_S`, the density
  obtain ⟨hR0, hR1, hRi⟩ := GenParams.rho_step hX hr0 hr1 hri (by omega)
  obtain ⟨hS0, hS1, hSi⟩ := GenParams.thetaS_step hX hR0 hR1 hRi
  obtain ⟨hd0, hd1, hdi⟩ := GenParams.joint_dens_step hX hbase
    (Q := uCount P.V (uDegT3 k) (alpha / 2) (globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k))
    (fun _ => rfl) (fun _ _ _ => one_le_uCount _ _ _ _ _) hS0 hS1 hSi ha0 hb0 (by omega)
  -- `η`, `yIn`
  -- the polynomial side condition of `eta_step_small`, from the class degree
  have hm : 3 * (k + 4) ^ 2 ≤ rhoDegJT3 k P.μ0 + 2 + 3 + (μD + 1) + 3 := by
    have h1 := sq_le_two_tDegT3 k
    have h6 : tDegT3 k + P.μ0 + 3 + k ≤ rhoDegJT3 k P.μ0 := by
      unfold rhoDegJT3; have := le_max_left (tDegT3 k + P.μ0 + 3) (pDeg k + 1); omega
    have h2 := le_max_right μV (pDeg k)
    have h3 : μD = tDegT3 k := hμDdef
    have h5 : pDeg k = 5 * k + 21 := rfl
    omega
  obtain ⟨he0, he8, hei⟩ := GenParams.eta_step_small (k := k) ha ha2 hd0 hd1 hdi hm
  obtain ⟨hy0, hyle, hyi⟩ := GenParams.yIn_step_small (k := k) ha ha2 he0 he8 hei (by omega)
  have e1 : rhoDegJT3 k P.μ0 + 2 + 3 + (μD + 1) + 3 + 1 = rhoDegJT3 k P.μ0 + μD + 10 := by
    ring
  have e2 : rhoDegJT3 k P.μ0 + 2 + 3 + (μD + 1) + 3 + 1 + 1 = densDegJT3 k P.μ0 := by
    unfold densDegJT3; ring
  rw [e1] at hei
  rw [e2] at hyi
  exact ⟨he0, he8, hei, hy0, hyle, hyi⟩

end GenParamsJT3

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

namespace GenParamsJT3

/-- The standing hypotheses on the parameters (no bound on `k`). -/
structure CHyp (P : GenParamsJT3) (μV μK : Nat) : Prop where
  hV : 1 ≤ P.V
  hVμ : P.V ≤ 2 ^ (2 ^ μV)
  hμ0 : max μV (pDeg P.k) + 2 ≤ P.μ0
  hk0 : P.k ≤ 2 ^ P.μ0
  hK : 2 ≤ P.K
  hKμ : P.K ≤ 2 ^ 2 ^ μK
  hp : 0 < P.p
  hpμ : P.p ≤ 2 ^ (2 ^ μK)

variable (P : GenParamsJT3) {alpha : Real}

/-- The log-degree of the width exponents. -/
def expDegJT3 (k μ0 μK : Nat) : Nat :=
  max (rhoDegJT3 k μ0 + tDegT3 k + 9) (max (rhoDegJT3 k μ0 + tDegT3 k + k + 7) (μK + 2))

/-- **`Em`, `QM` and `Bexp`**. -/
theorem spectrum_exps_inv_leJT3 {μV μK : Nat} (H : CHyp P μV μK) (ha : 0 < alpha)
    (ha2 : alpha ≤ 1 / 2) :
    (P.Em alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ (rhoDegJT3 P.k P.μ0 + tDegT3 P.k + 2)) ∧
      (P.QM alpha : Real) + 1 ≤ (2 / alpha) ^ (2 ^ (rhoDegJT3 P.k P.μ0 + tDegT3 P.k + 3)) ∧
      (P.Bexp alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ expDegJT3 P.k P.μ0 μK) := by
  have hX := two_div_ge_two ha ha2
  have hX1 : (1 : Real) ≤ 2 / alpha := by linarith
  have hri := P.rho1_inv_leJT3 ha ha2 H.hV H.hVμ H.hμ0
  set k := P.k with hkdef
  set ρ := rhoDegJT3 k P.μ0 with hρdef
  set μD := tDegT3 k with hμDdef
  have hρ1 : μD + P.μ0 + 3 ≤ ρ := (rhoDegJT3_ge k P.μ0).1
  have hM2 : ρ + μD + k + 7 ≤ expDegJT3 k P.μ0 μK := by
    unfold expDegJT3; exact (le_max_left _ _).trans (le_max_right _ _)
  have hM3 : μK + 2 ≤ expDegJT3 k P.μ0 μK := by
    unfold expDegJT3; exact (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨hB0, hB1, hBi⟩ := budget_gen_bounds_fejerW k ha ha2
  obtain ⟨hd0, hd1, hdi⟩ := delta_gen_bounds_fejerW k ha ha2
  obtain ⟨ht0, ht1, -⟩ := T2_gen_bounds_fejerW k ha ha2
  obtain ⟨hr0, hr1⟩ : 0 < P.Rho1 alpha ∧ P.Rho1 alpha ≤ 1 := P.rho1_pos_le ha ha2
  have hq0 : 0 < P.Rho1 alpha / 2 / 2 := by linarith
  have hq1 : P.Rho1 alpha / 2 / 2 ≤ 1 := by linarith
  have hqi : (P.Rho1 alpha / 2 / 2)⁻¹ ≤ (2 / alpha) ^ (2 ^ (ρ + 1)) := by
    rw [show (P.Rho1 alpha / 2 / 2)⁻¹ = 4 * (P.Rho1 alpha)⁻¹ by field_simp; ring]
    have h4 : (4 : Real) ≤ (2 / alpha) ^ (2 ^ ρ) :=
      pw_mono hX (pw_const hX (a := 1) (by norm_num)) (by omega)
    exact pw_mul hX (by norm_num) (inv_pos.mpr hr0).le h4 hri
  have hQ := uCount_scale_le_deg (c := ρ + 1) (D := uDegT3 k) (μD := μD) hX H.hV H.hVμ (seven_le_pDeg _) H.hμ0 hd0 hd1 hdi
    hB0 hB1 hBi hq0 hq1 hqi le_rfl
  rw [max_eq_right (show P.μ0 ≤ ρ + 1 by omega)] at hQ
  have hQv : singlePieceGlobalQmaxF (fun l => uCount P.V (uDegT3 l)) alpha
      (alpha / 2) k ≤ (2 / alpha) ^ (2 ^ (ρ + 1 + 1 + μD)) := hQ
  have hQv1 : 1 ≤ singlePieceGlobalQmaxF (fun l => uCount P.V (uDegT3 l))
      alpha (alpha / 2) k := one_le_uCount _ _ _ _ _
  have hQM := GenParams.floor_succ_le_pw hX hQv1 hQv
  have hQM' : (P.QM alpha : Real) + 1 ≤ (2 / alpha) ^ (2 ^ (ρ + μD + 3)) :=
    hQM.trans (pw_natpow hX (Nat.pow_le_pow_right (by norm_num) (by omega)))
  refine ⟨?_, hQM', ?_⟩
  · show (uCount P.V (uDegT3 k) _ _ _)⁻¹⁻¹ ≤ _
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
    have h1 := pw_mul' hX (Nat.cast_nonneg _) hpq0 hp' hpow
    have h2 := pw_mul' hX (by norm_num) (mul_nonneg (Nat.cast_nonneg _) hpq0) h4 h1
    refine pw_mono hX h2 ?_
    have : max μK (ρ + μD + 3 + (k + 2)) + 1 ≤ expDegJT3 k P.μ0 μK - 1 := by omega
    omega

/-- **The slice exponent `Eth`**. -/
theorem slice_exps_inv_leJT3 {μV μK : Nat} (H : CHyp P μV μK) (ha : 0 < alpha)
    (ha2 : alpha ≤ 1 / 2) :
    (P.Eth alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ (rhoDegJT3 P.k P.μ0 + tDegT3 P.k + 9)) := by
  have hX := two_div_ge_two ha ha2
  have hri := P.rho1_inv_leJT3 ha ha2 H.hV H.hVμ H.hμ0
  set k := P.k with hkdef
  set ρ := rhoDegJT3 k P.μ0 with hρdef
  set μD := tDegT3 k with hμDdef
  have hρ1 : μD + P.μ0 + 3 ≤ ρ := (rhoDegJT3_ge k P.μ0).1
  obtain ⟨hB0, hB1, hBi⟩ := budget_gen_bounds_fejerW k ha ha2
  obtain ⟨hr0, hr1⟩ : 0 < P.Rho1 alpha ∧ P.Rho1 alpha ≤ 1 := P.rho1_pos_le ha ha2
  obtain ⟨hR0, hR1, hRi⟩ := GenParams.rho_step hX hr0 hr1 hri (by omega)
  obtain ⟨hS0, hS1, hSi⟩ := GenParams.thetaS_step hX hR0 hR1 hRi
  have hThS : P.ThS alpha =
      singlePieceTheta ((P.Rho1 alpha) / 2 * ((P.Rho1 alpha) / 2 / 2)) 1 := rfl
  rw [← hThS] at hS0 hS1 hSi
  have hslice : ∀ {s : Real} {m : Nat}, 0 < s → s ≤ 1 → s⁻¹ ≤ (2 / alpha) ^ (2 ^ m) →
      P.μ0 ≤ m + 1 → (uExp P.V (uDegT3 k) (alpha / 2) (globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k) (s / 2))⁻¹ ≤
        (2 / alpha) ^ (2 ^ (m + 1 + 1 + μD)) := by
    intro s m hs0 hs1 hsi hm
    have hs20 : 0 < s / 2 := half_pos hs0
    have hs2i : (s / 2)⁻¹ ≤ (2 / alpha) ^ (2 ^ (m + 1)) := by
      rw [inv_div, div_eq_mul_inv]
      exact pw_mul hX (by norm_num) (inv_pos.mpr hs0).le (hX.trans (pw_X hX _)) hsi
    have h := uCount_scale_le_deg (c := m + 1) (D := uDegT3 k) (μD := μD) hX H.hV H.hVμ (seven_le_pDeg _) H.hμ0
      (half_pos ha) (by linarith) (GenParams.half_inv_le_deg (pDeg k) ha ha2) hB0 hB1 hBi hs20 (by linarith)
      hs2i le_rfl
    rw [max_eq_right hm] at h
    show (uCount P.V (uDegT3 k) _ _ _)⁻¹⁻¹ ≤ _
    rw [inv_inv]; exact h
  have hS2 : 0 < P.ThS alpha / 2 := half_pos hS0
  have hS21 : P.ThS alpha / 2 ≤ 1 := by linarith
  have hS2i : (P.ThS alpha / 2)⁻¹ ≤ (2 / alpha) ^ (2 ^ (ρ + 2 + 3 + 1)) := by
    rw [inv_div, div_eq_mul_inv]
    exact pw_mul hX (by norm_num) (inv_pos.mpr hS0).le (hX.trans (pw_X hX _)) hSi
  have hE := hslice hS2 hS21 hS2i (by omega)
  rw [show P.ThS alpha / 2 / 2 = P.ThS alpha / 4 by ring] at hE
  exact pw_mono hX hE (by omega)

/-- **The localization exponent is polynomially small.** -/
theorem Eloc_inv_leJT3 {μV μK : Nat} (H : CHyp P μV μK) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < P.Eloc alpha ∧ (P.Eloc alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ (expDegJT3 P.k P.μ0 μK + 3)) := by
  have hX := two_div_ge_two ha ha2
  set M := expDegJT3 P.k P.μ0 μK with hMdef
  have hM1 : rhoDegJT3 P.k P.μ0 + tDegT3 P.k + 9 ≤ M := by
    rw [hMdef]; unfold expDegJT3; exact le_max_left _ _
  have hM2 : rhoDegJT3 P.k P.μ0 + tDegT3 P.k + P.k + 7 ≤ M := by
    rw [hMdef]; unfold expDegJT3; exact (le_max_left _ _).trans (le_max_right _ _)
  obtain ⟨hE0, -, -, -, -, -⟩ := P.Eloc_pos_le H.hV H.hp ha ha2
  obtain ⟨-, ⟨hEm0, -⟩, ⟨hEth0, -⟩, ⟨hN0, -⟩, ⟨hBx0, -⟩, -⟩ :=
    P.ranges H.hp ha ha2
  have hNE := P.nestExp_inv_leJT3 ha ha2 H.hV H.hVμ H.hμ0
  obtain ⟨hEm, -, hBx⟩ := P.spectrum_exps_inv_leJT3 H ha ha2
  have hEth := P.slice_exps_inv_leJT3 H ha ha2
  refine ⟨hE0, ?_⟩
  have hval : (P.Eloc alpha)⁻¹ =
      32 * ((P.NestExp alpha)⁻¹ * (P.Em alpha)⁻¹) *
      ((P.Bexp alpha)⁻¹ * ((P.Eth alpha)⁻¹ * (P.Eth alpha)⁻¹)) := by
    show ((P.NestExp alpha * (P.Em alpha / 2)) *
      (P.Bexp alpha * (P.Eth alpha * P.Eth alpha) / 2) / 8)⁻¹ = _
    field_simp
    ring
  rw [hval]
  have hNE' := pw_mono hX hNE (show rhoDegJT3 P.k P.μ0 + tDegT3 P.k + 3 + P.k ≤ M by omega)
  have hEm' := pw_mono hX hEm (show rhoDegJT3 P.k P.μ0 + tDegT3 P.k + 2 ≤ M by omega)
  have hEth' := pw_mono hX hEth hM1
  have h32 : (32 : Real) ≤ (2 / alpha) ^ (2 ^ (M + 1)) :=
    pw_mono hX (pw_const hX (a := 3) (by norm_num)) (by omega)
  have p1 := pw_mul hX (inv_pos.mpr hN0).le (inv_pos.mpr hEm0).le hNE' hEm'
  have p2 := pw_mul hX (inv_pos.mpr hEth0).le (inv_pos.mpr hEth0).le hEth' hEth'
  have hEE0 : 0 ≤ (P.Eth alpha)⁻¹ * (P.Eth alpha)⁻¹ :=
    mul_nonneg (inv_pos.mpr hEth0).le (inv_pos.mpr hEth0).le
  have hNE0 : 0 ≤ (P.NestExp alpha)⁻¹ * (P.Em alpha)⁻¹ :=
    mul_nonneg (inv_pos.mpr hN0).le (inv_pos.mpr hEm0).le
  have p3 := pw_mul' hX (inv_pos.mpr hBx0).le hEE0 hBx p2
  have p4 := pw_mul hX (by norm_num) hNE0 h32 p1
  have p5 := pw_mul' hX (mul_nonneg (by norm_num) hNE0) (mul_nonneg (inv_pos.mpr hBx0).le hEE0) p4 p3
  exact pw_mono hX p5 (by omega)

/-- The threshold degree of the step. -/
def threshDegJT3 (k μ0 μK : Nat) : Nat := max (expDegJT3 k μ0 μK + 4) (5 * k + 30)

/-- **The requirement on `m`**. -/
theorem MReq_le_expJT3 {μV μK : Nat} (H : CHyp P μV μK) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    1 ≤ P.MReq alpha ∧
      P.MReq alpha ≤ Real.exp ((2 / alpha) ^ (2 ^ max (expDegJT3 P.k P.μ0 μK + 3) (5 * P.k + 24))) := by
  have hX := two_div_ge_two ha ha2
  obtain ⟨-, hQM, hBx⟩ := P.spectrum_exps_inv_leJT3 H ha ha2
  have hri := P.rho1_inv_leJT3 ha ha2 H.hV H.hVμ H.hμ0
  set k := P.k with hkdef
  set E := expDegJT3 k P.μ0 μK with hEdef
  set Z := 5 * k + 21 with hZdef
  have hZ2 : 2 ≤ Z := by rw [hZdef]; omega
  have hρE : rhoDegJT3 k P.μ0 + tDegT3 k + k + 7 ≤ E := by
    rw [hEdef]; unfold expDegJT3; exact (le_max_left _ _).trans (le_max_right _ _)
  have hKE : μK + 2 ≤ E := by
    rw [hEdef]; unfold expDegJT3; exact (le_max_right _ _).trans (le_max_right _ _)
  -- the recurrence threshold
  have hthr := familyRecThr_le_exp (k := k) hX (by have := H.hK; omega) H.hKμ H.hpμ hQM
  have hthr' : (familyRecThr k P.K P.p (P.QM alpha) : Real) ≤
      Real.exp ((2 / alpha) ^ (2 ^ (E + 3))) := ex_mono hX hthr (by omega)
  have hthr1 : (1 : Real) ≤ (familyRecThr k P.K P.p (P.QM alpha) : Real) :=
    Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr
      (familyRecThr_pos (k := k) (p := P.p) (by have := H.hK; omega) _).ne')
  -- the Bohr radius and `ρ`
  obtain ⟨hz0, hzi⟩ := zeta_gen_bounds_fejer5 k ha ha2
  have hzeq : P.Zeta alpha = tightZeta (fejerThetaOne alpha (alpha / 2) k / 4) := rfl
  obtain ⟨hr0, hr1⟩ : 0 < P.Rho1 alpha ∧ P.Rho1 alpha ≤ 1 := P.rho1_pos_le ha ha2
  have hρ1 : 1 ≤ rhoDegJT3 k P.μ0 := by have := (rhoDegJT3_ge k P.μ0).1; omega
  obtain ⟨hR0, -, hRi⟩ := GenParams.rho_step hX hr0 hr1 hri hρ1
  have hReq : P.Rho alpha = P.Rho1 alpha / 2 * (P.Rho1 alpha / 2 / 2) := rfl
  rw [← hReq] at hR0 hRi
  have hBpos : 0 < P.Bexp alpha := by
    have := familyRecExp_pos k P.p (P.QM alpha) H.hp
    show 0 < familyRecExp k P.p _ / 2; exact half_pos this
  set z := P.Zeta alpha with hzdef
  set R := P.Rho alpha with hRdef
  set B := P.Bexp alpha with hBdef
  rw [← hzeq] at hz0 hzi
  have hcz (c : Real) (hc : c ≤ 16) :
      c / z ≤ Real.exp ((2 / alpha) ^ (2 ^ (Z + 1))) := by
    rw [div_eq_mul_inv]
    exact ex_mono hX (ex_mul' hX (inv_pos.mpr hz0).le
      (ex_of_pw (pw_const hX (a := 2) (by norm_num; exact hc))) hzi) (by omega)
  have hR3 : (R ^ 3)⁻¹ ≤ (2 / alpha) ^ (2 ^ (rhoDegJT3 k P.μ0 + 2 + 2)) := by
    rw [← inv_pow]; exact pw_pow hX (inv_pos.mpr hR0).le hRi (by norm_num)
  have h4zr : 4 / (z * R ^ 3) ≤
      Real.exp ((2 / alpha) ^ (2 ^ (max (Z + 1) (rhoDegJT3 k P.μ0 + 4) + 1))) := by
    rw [div_eq_mul_inv, mul_inv, ← mul_assoc]
    have h4z := hcz 4 (by norm_num)
    rw [div_eq_mul_inv] at h4z
    exact ex_mul' hX (inv_pos.mpr (pow_pos hR0 3)).le h4z (ex_of_pw hR3)
  have hBe : 1 / B ≤ (2 / alpha) ^ (2 ^ E) := by rw [one_div]; exact hBx
  have hBe2 : 2 / B ≤ (2 / alpha) ^ (2 ^ (E + 1)) := by
    rw [div_eq_mul_inv]
    exact pw_mul hX (by norm_num) (inv_pos.mpr hBpos).le (hX.trans (pw_X hX _)) hBx
  have e1 := ex_rpow_of_nonneg hX (by positivity) (hcz 8 (by norm_num)) (div_nonneg zero_le_one hBpos.le) hBe
  have e2 := ex_rpow_of_nonneg hX (by positivity) h4zr (div_nonneg zero_le_one hBpos.le) hBe
  have e3 := ex_rpow_of_nonneg hX (by positivity) (hcz 16 le_rfl) (div_nonneg zero_le_two hBpos.le) hBe2
  refine ⟨hthr1.trans (le_max_left _ _), ?_⟩
  show max (familyRecThr k P.K P.p (P.QM alpha) : Real)
    (max ((8 / z) ^ (1 / B)) (max ((4 / (z * R ^ 3)) ^ (1 / B)) ((16 / z) ^ (2 / B)))) ≤ _
  refine max_le (ex_mono hX hthr' (le_max_left _ _)) (max_le ?_ (max_le ?_ ?_))
  · exact ex_mono hX e1 (by rw [hZdef]; omega)
  · exact ex_mono hX e2 (by rw [hZdef]; omega)
  · exact ex_mono hX e3 (by rw [hZdef]; omega)

/-- **The modulus threshold of the step is single exponential.** -/
theorem Tloc_le_expJT3 {μV μK : Nat} (H : CHyp P μV μK) (hk : 1 ≤ P.k) (ha : 0 < alpha)
    (ha2 : alpha ≤ 1 / 2) :
    P.Tloc alpha ≤ Real.exp ((2 / alpha) ^ (2 ^ threshDegJT3 P.k P.μ0 μK)) := by
  have hX := two_div_ge_two ha ha2
  have hX1 : (1 : Real) ≤ 2 / alpha := by linarith
  obtain ⟨hEl0, hEli⟩ := P.Eloc_inv_leJT3 H ha ha2
  obtain ⟨hEm, -, -⟩ := P.spectrum_exps_inv_leJT3 H ha ha2
  have hNE := P.nestExp_inv_leJT3 ha ha2 H.hV H.hVμ H.hμ0
  obtain ⟨-, ⟨hEm0, -⟩, -, ⟨hN0, -⟩, -, -⟩ := P.ranges H.hp ha ha2
  obtain ⟨hR1, hR⟩ := P.MReq_le_expJT3 H ha ha2
  have hL := lemma156_gen_le_fejer5 hk ha ha2
  set k := P.k with hkdef
  set E := expDegJT3 k P.μ0 μK with hEdef
  set T := threshDegJT3 k P.μ0 μK with hTdef
  set μD := tDegT3 k with hμDdef
  have hET : E + 4 ≤ T := by rw [hTdef]; unfold threshDegJT3; exact le_max_left _ _
  have hZT : 5 * k + 30 ≤ T := by rw [hTdef]; unfold threshDegJT3; exact le_max_right _ _
  have hρE : rhoDegJT3 k P.μ0 + μD + k + 7 ≤ E := by
    rw [hEdef]; unfold expDegJT3; exact (le_max_left _ _).trans (le_max_right _ _)
  obtain ⟨hρ0, hρ2⟩ := rhoDegJT3_ge k P.μ0
  have hNE' : (P.NestExp alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ E) := pw_mono hX hNE (by omega)
  have hEm' : (P.Em alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ E) := pw_mono hX hEm (by omega)
  have hMx : (P.MExp alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ (E + 2)) := by
    show (P.NestExp alpha * (P.Em alpha / 2))⁻¹ ≤ _
    rw [show (P.NestExp alpha * (P.Em alpha / 2))⁻¹ =
      2 * ((P.NestExp alpha)⁻¹ * (P.Em alpha)⁻¹) by field_simp]
    have p1 := pw_mul hX (inv_pos.mpr hN0).le (inv_pos.mpr hEm0).le hNE' hEm'
    exact pw_mul hX (by norm_num) (mul_nonneg (inv_pos.mpr hN0).le (inv_pos.mpr hEm0).le)
      (hX.trans (pw_X hX _)) p1
  have hMx0 : 0 < P.MExp alpha := by
    show 0 < P.NestExp alpha * (P.Em alpha / 2)
    exact mul_pos hN0 (half_pos hEm0)
  -- the roots
  have h64 : (64 : Real) ^ (1 / P.NestExp alpha) ≤ Real.exp ((2 / alpha) ^ (2 ^ T)) :=
    ex_mono hX (ex_root (j := 3) hX (by norm_num) (by norm_num) hN0 hNE') (by omega)
  have h6 : (6 : Real) ^ (1 / P.Eloc alpha) ≤ Real.exp ((2 / alpha) ^ (2 ^ T)) :=
    ex_mono hX (ex_root (j := 2) hX (by norm_num) (by norm_num) hEl0 hEli) (by omega)
  -- the requirement on `m`
  have hMR : P.MReq alpha ^ (1 / P.MExp alpha) ≤ Real.exp ((2 / alpha) ^ (2 ^ T)) := by
    rw [one_div]
    refine ex_mono hX (ex_rpow hX hR1 hR (inv_pos.mpr hMx0).le hMx) ?_
    have := hET; have := hZT; have := Nat.two_pow_pos (k + 4)
    simp only [max_def]; split_ifs <;> omega
  have hMT : P.MThr alpha ≤ Real.exp ((2 / alpha) ^ (2 ^ T)) :=
    max_le (Real.one_le_exp (pow_nonneg (by linarith) _)) h64
  -- Lemma 15.6
  have hL' : fejerProductThreshold k (alpha / 2) (alpha / 2) ≤
      Real.exp ((2 / alpha) ^ (2 ^ T)) := by
    refine ex_of_pw (pw_mono hX hL ?_)
    have : 5 * k + 21 ≤ 5 * k + 30 := by omega
    omega
  have h3 : (3 : Real) ≤ Real.exp ((2 / alpha) ^ (2 ^ T)) :=
    ex_of_pw (pw_mono hX (pw_const hX (a := 1) (by norm_num)) (by omega))
  show max (max 3 (fejerProductThreshold k (alpha / 2) (alpha / 2)))
    (max (P.MThr alpha)
      (max (P.MReq alpha ^ (1 / P.MExp alpha)) (6 ^ (1 / P.Eloc alpha)))) ≤ _
  exact max_le (max_le h3 hL') (max_le hMT (max_le hMR h6))

end GenParamsJT3

end LeanProofs.GowersSzemeredi
