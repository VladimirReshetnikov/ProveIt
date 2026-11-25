import IPRADerivations.Analysis.GaussianGammaZetaMellinCompact
import IPRADerivations.Analysis.GaussianGammaCompactCutoffAlignment
import IPRADerivations.Analysis.GaussianGammaEulerShiftLimit
import IPRADerivations.Analysis.GaussianCompactNamedAdditivity

/-!
# Nested powered cutoff windows for the original Mellin sampler

Use the existing powered left endpoint and integer right endpoint.
The earlier physical interval is exactly the middle panel after
rescaling to the later denominator and changing the mesh budgets.
-/

set_option autoImplicit false
set_option maxHeartbeats 1050000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinCutoffWindows

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCompactRiemannName (data)
open GaussianGammaCompactQuadratureBoundary (width exact_right_endpoint)
open GaussianGammaCompactCutoffGeometry
  (ratio ratio_positive lowerWidth lower_endpoint lower_positive middleWidth middle_endpoint middle_positive
    upperWidth upper_positive eta_den_refinement widths_total top_monotone)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaIntegralCutoffs (etaDen top eta_den_positive top_positive)
open GaussianGammaZetaMellinCompact (gain compact_input)
open GaussianGammaZetaMellinGrid (evaluatorF fixedData)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalHorner (positive_product)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "nameF" => GaussianGammaZetaMellinCompact.nameF
local notation "P" => GaussianGammaZetaMellinCompact.source
local notation "S" => GaussianEulerLowerPowerCoefficients.source

def datum (z R B A p : PTm n) : PTm n :=
  let E := etaDen p A R
  let T := top p A R
  data one (width p A R) E (gain (R+one) E T) T (fixedData (shifted z B) B)

@[simp] theorem subst_datum {m : ℕ} (σ : Fin n → PTm m) (z R B A p : PTm n) :
    Syn.subst σ (datum z R B A p) =
      datum (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ p) := by
  simp [datum,etaDen,top,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient,
    Products.fact,one,two]

theorem panel_source (z R B A a W E T : PTm n)
    (hz : Γ ⊢[PRAAx] S z R B A)
    (ha : Γ ⊢[PRAAx] le one a) (he : Γ ⊢[PRAAx] le one E)
    (hT : Γ ⊢[PRAAx] le (a+W) (T*E)) :
    Γ ⊢[PRAAx] P (shifted z B) (R+one) B a W E E T := by
  have low : Γ ⊢[PRAAx] le E (E*a) :=
    le_congr (one_mul E) (mul_comm _ _) (mul_le_mul_right E ha)
  have disk := GaussianGammaEulerShiftLimit.shifted_bound z R B hz.andE₂.andE₁.andE₂
  exact .andI (.andI hz.andE₂.andE₁.andE₁ (.andI he disk))
    (.andI (.andI ha he) (.andI low hT))

theorem cutoff_source (z R B A p : PTm n) (hz : Γ ⊢[PRAAx] S z R B A) :
    Γ ⊢[PRAAx] P (shifted z B) (R+one) B one (width p A R) (etaDen p A R) (etaDen p A R) (top p A R) :=
  panel_source z R B A _ _ _ _ hz (le_refl one) (eta_den_positive p A R)
    (le_congr (exact_right_endpoint p A R).eqSymm (mul_comm _ _) (le_refl _))

theorem regular (z R B A p : PTm n) (hz : Γ ⊢[PRAAx] S z R B A) :
    Γ ⊢[PRAAx] pointCN nameF (datum z R B A p) :=
  GaussianGammaZetaMellinCompact.regular _ _ _ _ _ _ _ _ (cutoff_source z R B A p hz)

theorem data_congr (a a' W W' E E' L T x : PTm n)
    (ha : Γ ⊢[PRAAx] a ≐ a') (hW : Γ ⊢[PRAAx] W ≐ W') (hE : Γ ⊢[PRAAx] E ≐ E') :
    Γ ⊢[PRAAx] data a W E L T x ≐ data a' W' E' L T x := by
  have e := Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
    (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6)
    (σ := ![a,W,E,L,T,x]) (σ' := ![a',W',E',L,T,x]) (fun i => by
      fin_cases i
      · exact ha
      · exact hW
      · exact hE
      · exact .eqRefl _
      · exact .eqRefl _
      · exact .eqRefl _)
  simpa only [GaussianCompactRiemannName.subst_data,Syn.subst_var,Matrix.cons_val] using e

theorem middle_alignment (z R B A p q : PTm n) (hz : Γ ⊢[PRAAx] S z R B A)
    (hpq : Γ ⊢[PRAAx] le p q) :
    let E := etaDen q A R
    let T := top q A R
    Γ ⊢[PRAAx] crossEquivalent nameF nameF (datum z R B A p)
      (data (one+lowerWidth p q A) (middleWidth p q A R) E (gain (R+one) E T) T (fixedData (shifted z B) B)) := by
  let E₀ := etaDen p A R
  let T₀ := top p A R
  let W := width p A R
  let E := etaDen q A R
  let T := top q A R
  let L := gain (R+one) E T
  let L₀ := gain (R+one) E₀ T₀
  let K := ratio p q A
  let x := fixedData (shifted z B) B
  have old := compact_input _ _ _ _ _ _ _ _ (cutoff_source z R B A p hz)
  have upper : Γ ⊢[PRAAx] le (one+W) (T*E₀) :=
    le_congr ((mul_comm T₀ E₀).eqTrans (exact_right_endpoint p A R).eqSymm) (.eqRefl _)
      (mul_le_mul_right E₀ (top_monotone p q A R hpq))
  have fresh := compact_input _ _ _ _ _ _ _ _
    (panel_source z R B A one W E₀ T hz (le_refl one) (eta_den_positive p A R) upper)
  have changed := GaussianCompactMeshIndependence.name_independence evaluatorF one W E₀ L₀ T₀
    (gain (R+one) E₀ T) T x (.andI old fresh)
  let V := gain (R+one) E₀ T
  have scaleInput : Γ ⊢[PRAAx] GaussianCompactIntervalRescaling.input evaluatorF K one W E₀ V T x :=
    .andI (ratio_positive p q A) fresh
  have scale := GaussianCompactIntervalRescaling.name_rescaling evaluatorF K one W E₀ V T x scaleInput
  have aEq : Γ ⊢[PRAAx] K*one ≐ one+lowerWidth p q A :=
    ((mul_comm _ _).eqTrans (one_mul _)).eqTrans (lower_endpoint p q A).eqSymm
  have dEq := data_congr (K*one) (one+lowerWidth p q A) (K*W) (middleWidth p q A R) (K*E₀) E V T x
    aEq (.eqRefl _) (eta_den_refinement p q A R hpq).eqSymm
  have adjusted := GaussianGammaCompactCutoffAlignment.cross_data_congr nameF nameF _ _ _ _
    (.eqRefl _) dEq scale
  have newUpper : Γ ⊢[PRAAx] le ((one+lowerWidth p q A)+middleWidth p q A R) (T*E) :=
    le_congr ((mul_comm T₀ E).eqTrans
      ((congrAdd (lower_endpoint p q A) (.eqRefl _)).eqTrans (middle_endpoint p q A R hpq)).eqSymm)
      (.eqRefl _) (mul_le_mul_right E (top_monotone p q A R hpq))
  have target := compact_input _ _ _ _ _ _ _ _
    (panel_source z R B A (one+lowerWidth p q A) (middleWidth p q A R) E T hz (le_add_right _ _)
      (eta_den_positive q A R) newUpper)
  have rescaled := GaussianCompactIntervalRescaling.scaled_input evaluatorF K one W E₀ V T x scaleInput
  have aligned : Γ ⊢[PRAAx] GaussianCompactRiemannName.input evaluatorF
      (one+lowerWidth p q A) (middleWidth p q A R) E V T x := by
    have eq := Prf.eqSubst (Ax := PRAAx) (Γ := Γ)
      (GaussianCompactRiemannName.input evaluatorF (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : Fm PTm 6)
      ![K*one,K*W,K*E₀,V,T,x] ![one+lowerWidth p q A,middleWidth p q A R,E,V,T,x]
      (fun i => by fin_cases i; exact aEq; exact .eqRefl _; exact (eta_den_refinement p q A R hpq).eqSymm
                   exact .eqRefl _; exact .eqRefl _; exact .eqRefl _)
      (by simpa [Matrix.cons_val] using rescaled)
    simpa [Matrix.cons_val] using eq
  have reset := GaussianCompactMeshIndependence.name_independence evaluatorF (one+lowerWidth p q A)
    (middleWidth p q A R) E V T L T x (.andI aligned target)
  exact cross_trans _ _ _ _ _ _ changed (cross_trans _ _ _ _ _ _ adjusted reset)

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinCutoffWindows
