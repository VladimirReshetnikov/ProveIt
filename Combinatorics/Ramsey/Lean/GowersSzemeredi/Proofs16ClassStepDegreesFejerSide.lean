import GowersSzemeredi.Proofs16ClassStepDegreesFejer
import GowersSzemeredi.Proofs16ClassStepDegreesSide

/-! Declarations of `Proofs16ClassStepDegreesFejer` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

section
open BaseCase

/-- The count degree of the next class. -/
def fejerStepCountDeg (k D : Nat) : Nat := stepCountDegW (fejerStepP k) k D

/-- The width-exponent degree of the next class. -/
def fejerStepExpDeg (k D : Nat) : Nat := stepExpDegW (fejerStepP k) (fejerStepT k) k D

/-! ### The count -/

/-- **The count of the next class.** -/
theorem step_count_le_fejer {k D : Nat} (hD : 1 ≤ D) {V V' : Real} (hV : 1 ≤ V) (hVV : V ≤ V')
    {theta gamma rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat) :
    max (famPieceGraphBound (classQr V D k (n * classPiecesFejer gamma theta k) (classBudgetW (fejerThetaOne theta gamma k) k) gamma)
        (classPb V D (n * classPiecesFejer gamma theta k) (classBudgetW (fejerThetaOne theta gamma k) k) gamma)
        (n * classPiecesFejer gamma theta k) rho)
      (((3 ^ (k + 1) * (n * classPiecesFejer gamma theta k)) : Nat) : Real) ≤
      uniformBase V' n theta gamma rho ^ fejerStepCountDeg k D :=
  step_count_le_W hD hV hVV hg hg1 ht ht1 hr hr1 n (P := fejerStepP k)
    (classBudgetW_pos_le k (fejerThetaOne_bounds k ht ht1 hg hg1).1
      (fejerThetaOne_bounds k ht ht1 hg hg1).2).1
    (classPiecesFejer_le_gen k hg hg1 ht ht1) (twoDiv_gamma_le_fejer k hg hg1 ht ht1)
    (by have := fejerStepP_ge k; omega)

/-! ### The width exponent -/

/-- **The width exponent of the next class.** -/
theorem step_exp_inv_le_fejer {k D : Nat} (hD : 1 ≤ D) {V V' : Real} (hV : 1 ≤ V) (hVV : V ≤ V')
    {K p : Nat} (hK : 1 ≤ K) (hp : 0 < p) (hKV : (K : Real) ≤ V') (hpV : (p : Real) ≤ V')
    {theta gamma rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat) :
    let M := n * classPiecesFejer gamma theta k
    let tS := classBudgetW (fejerThetaOne theta gamma k) k
    let gS := section16Delta (fejerThetaOne theta gamma k)
    let e := section16CappedWidthExponent
        (pieceLineExponent (familyWidthDivisor k p) (classQb V D M tS gS) (classEb V D M tS gS)
            (classEr V D k M tS gamma) rho *
          famPieceSliceExponent (classQr V D k M tS gamma) (classEs V D M tS gamma) M rho / 4)
        (section16RoundedPowerThreshold
          (pieceWidthScale (familyWidthPrefactor K) (classQb V D M tS gS) (tightZeta (fejerThetaOne theta gamma k / 4)) rho)
          (pieceLineExponent (familyWidthDivisor k p) (classQb V D M tS gS) (classEb V D M tS gS)
            (classEr V D k M tS gamma) rho)
          (famPieceSliceExponent (classQr V D k M tS gamma) (classEs V D M tS gamma) M rho))
    0 < e ∧ e⁻¹ ≤ uniformBase V' n theta gamma rho ^ fejerStepExpDeg k D :=
  have hf := fejerThetaOne_bounds k ht ht1 hg hg1
  have hb := classBudgetW_pos_le k hf.1 hf.2
  have hd := section16_theta_delta_bounds_with hf.1 hf.2
  step_exp_inv_le_W hD hV hVV hK hp hKV hpV hg hg1 ht ht1 hr hr1 n (P := fejerStepP k)
    (T := fejerStepT k) hb.1 hb.2 hd.2.2.1 hd.2.2.2 (tightZeta_fejer_inv_le_gen k hg hg1 ht ht1)
    (classPiecesFejer_le_gen k hg hg1 ht ht1) (twoDiv_gamma_le_fejer k hg hg1 ht ht1)
    (twoDiv_delta_le_fejer k hg hg1 ht ht1) (by have := fejerStepP_ge k; omega)

/-! ### The step -/

/-- **The step of route (II).** A uniform class of dimension `k ≥ 1` at one
degree `D`, with the family Lemma 16.6 at dimension `k`, gives a uniform class
of dimension `k+1`. -/
theorem powerUniformClass_succ_fejer {k : Nat} (hk : 1 ≤ k) {V : Real} (hV : 1 ≤ V) {D : Nat}
    (hD : 1 ≤ D) (C : PowerUniformClass k V D D D) {K p : Nat} (hK : 1 ≤ K) (hp : 0 < p)
    (hlemma6 : AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor K) (familyWidthDivisor k p)))
    {V' : Real} (hVV : V ≤ V') (hKV : (K : Real) ≤ V') (hpV : (p : Real) ≤ V') :
    Nonempty (PowerUniformClass (k + 1) V' (fejerStepCountDeg k D) (fejerStepExpDeg k D) (fejerStepThrDeg k D)) := by
  refine ⟨{
    U := fun N _ theta gamma Gamma =>
      ∃ P : Fin (classPiecesFejer gamma theta k) → StepPieceFejer C N theta gamma,
        Gamma ⊆ stepPieceFejerGraphs C P
    mono := fun N _ theta gamma Gamma Gamma' hsub ⟨P, hP⟩ => ⟨P, hsub.trans hP⟩
    empty := fun N _ theta gamma =>
      ⟨fun _ => ClassPiece.empty C _ _ _ _ _ _, Finset.empty_subset _⟩
    decomp := ?_
    cover := ?_ }⟩
  · intro theta gamma ht ht1 hg hg1 N _ _ hN Gamma hsize hprod
    have hN' : classStepThresholdFejer V D theta gamma k ≤ N :=
      (step_thr_le_fejer hk hV hVV hg hg1 ht ht1).trans hN
    obtain ⟨J, hJ, P, hP⟩ := class_step_decomp_fejer C hk ht ht1 hg hg1 hN' Gamma hsize hprod
    exact ⟨J, hJ, P, hP⟩
  · intro theta gamma ht ht1 hg hg1 N _ _ n Gamma hU
    choose P hP using hU
    have h := class_step_cover_fejer C hk hV (familyWidthPrefactor_pos hK) (familyWidthDivisor_pos hp)
      hlemma6 ht ht1 hg hg1 Gamma P hP
    refine h.weaken ?_ ?_ ?_
    · intro rho hr hr1
      exact step_count_le_fejer hD hV hVV hg hg1 ht ht1 hr hr1 n
    · intro rho hr hr1
      have h2 := uniformBase_two_le (hV.trans hVV) n ht ht1 hg hg1 hr hr1
      positivity
    · intro rho hr hr1
      obtain ⟨he0, hei⟩ := step_exp_inv_le_fejer hD hV hVV hK hp hKV hpV hg hg1 ht ht1 hr hr1 n
      have := inv_anti₀ (inv_pos.mpr he0) hei
      rwa [inv_inv] at this

end

end LeanProofs.GowersSzemeredi
