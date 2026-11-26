import IPRADerivations.Analysis.Gamma.Zeta.GaussianGammaZetaMellinCutoffWindows
import IPRADerivations.Analysis.Gamma.Zeta.GaussianGammaZetaMellinLowerRooted
import IPRADerivations.Analysis.Gamma.Zeta.GaussianGammaZetaMellinCompactUpperTail
import IPRADerivations.DiophantineNumberTheory.AperyMultibound

/-!
# Cauchy comparison on nested original Mellin windows

The two exterior compact panels provide separate lower and upper
budgets. Exact alignment identifies the middle panel with the
earlier original cutoff at independent compact observations.
-/

set_option autoImplicit false
set_option maxHeartbeats 1300000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinNestedBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianCompactRiemannName (data)
open GaussianGammaCompactQuadratureBoundary (width exact_right_endpoint)
open GaussianGammaCompactCutoffGeometry
  (lowerWidth middleWidth upperWidth lower_endpoint middle_endpoint widths_total top_monotone
    lower_positive middle_positive upper_positive three_endpoint)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaIntegralCutoffs (etaDen top height eta_den_positive top_positive)
open GaussianGammaZetaMellinCompact (gain compact_input nameF)
open GaussianGammaZetaMellinCutoffWindows (datum panel_source data_congr middle_alignment)
open GaussianGammaZetaMellinGrid (evaluatorF fixedData)
open GaussianGammaZetaMellinUpperPoint (coefficientBound)
open GaussianNameEquivalence (cross_at cross_symm)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (qadd qzero canonical positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalSyntheticDivision (qadd_congr qzero_add)
open ConciseIPRA.PTm (succ zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "S" => GaussianEulerLowerPowerCoefficients.source
local notation "P" => GaussianGammaZetaMellinCompact.source

private theorem split_input (z R B a C D E T : PTm n)
    (h : Γ ⊢[PRAAx] P z R B a (C+D) E E T)
    (hc : Γ ⊢[PRAAx] le one C) (hd : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] GaussianCompactNamedAdditivity.input evaluatorF a C D E (gain R E T) T (fixedData z B) := by
  have raw := compact_input _ _ _ _ _ _ _ _ h
  exact .andI raw.andE₁ (.andI raw.andE₂.andE₁ (.andI hc (.andI hd raw.andE₂.andE₂)))

private theorem split_at (r a C D E L T x : PTm n)
    (h : Γ ⊢[PRAAx] GaussianCompactNamedAdditivity.input evaluatorF a C D E L T x) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF r (data a (C+D) E L T x))
      (qadd (ap2 nameF r (data a C E L T x)) (ap2 nameF r (data (a+C) D E L T x)))
      (num 11) (unit (r+num 6)) :=
  distance_congr (GaussianCompactRiemannName.name_at evaluatorF r a (C+D) E L T x).eqSymm
    (qadd_congr (GaussianCompactRiemannName.name_at evaluatorF r a C E L T x).eqSymm
      (GaussianCompactRiemannName.name_at evaluatorF r (a+C) D E L T x).eqSymm)
    (.eqRefl _) (.eqRefl _) (GaussianCompactNamedAdditivity.sample_additivity evaluatorF r a C D E L T x h)

private theorem two_splits (r z R B j p q : PTm n)
    (hz : Γ ⊢[PRAAx] S z R B (succ j)) (hpq : Γ ⊢[PRAAx] lt p q) :
    let A := succ j
    let E := etaDen q A R
    let T := top q A R
    let L := gain (R+one) E T
    let x := fixedData (shifted z B) B
    let C₁ := lowerWidth p q A
    let C₂ := middleWidth p q A R
    let C₃ := upperWidth p q A R
    let l := ap2 nameF r (data one C₁ E L T x)
    let m := ap2 nameF r (data (one+C₁) C₂ E L T x)
    let h := ap2 nameF r (data (one+(C₁+C₂)) C₃ E L T x)
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF r (datum z R B A q)) (qadd (qadd l m) h) one (unit r) := by
  intro A E T L x C₁ C₂ C₃ l m h
  let s := ap2 nameF r (data one (C₁+C₂) E L T x)
  let u := ap2 nameF r (data one (C₁+C₂+C₃) E L T x)
  let U := unit r
  let V := unit (r+num 6)
  have hE := eta_den_positive (Γ := Γ) q A R
  have c₁ := lower_positive p q A (zero_lt_succ j) hpq
  have c₂ := middle_positive (Γ := Γ) p q A R
  have c₃ := upper_positive p q A R hpq
  have endpoint : Γ ⊢[PRAAx] one+(C₁+C₂+C₃) ≐ T*E :=
    (three_endpoint p q A R (le_of_lt hpq)).eqTrans (mul_comm _ _)
  have full : Γ ⊢[PRAAx] P (shifted z B) (R+one) B one (C₁+C₂+C₃) E E T :=
    panel_source z R B A _ _ _ _ hz (le_refl one) hE (le_congr endpoint.eqSymm (.eqRefl _) (le_refl _))
  have firstTwo : Γ ⊢[PRAAx] P (shifted z B) (R+one) B one (C₁+C₂) E E T :=
    panel_source z R B A _ _ _ _ hz (le_refl one) hE
      (le_trans (le_congr (by ipra_ring) (add_comm _ _) (add_le_add_right one (le_add_right (C₁+C₂) C₃)))
        full.andE₂.andE₂.andE₂)
  have first : Γ ⊢[PRAAx] distanceBounded u (qadd s h) (num 11) V :=
    split_at r one (C₁+C₂) C₃ E L T x
      (split_input _ _ _ _ _ _ _ _ full (le_trans c₁ (le_add_right _ _)) c₃)
  have next : Γ ⊢[PRAAx] distanceBounded s (qadd l m) (num 11) V :=
    split_at r one C₁ C₂ E L T x (split_input _ _ _ _ _ _ _ _ firstTwo c₁ c₂)
  have hV := unit_positive (Γ := Γ) (r+num 6)
  have add := GaussianNameArithmetic.sum_distance s (qadd l m) h h (num 11) zero V hV next
    (GaussianRationalPowerDifference.distance_refl_zero h V hV)
  have both := distance_triangle_same _ _ _ _ _ _ hV first add
  have same : Γ ⊢[PRAAx] ap2 nameF r (datum z R B A q) ≐ u :=
    congrAp2 nameF (.eqRefl _) (data_congr one one _ _ E E L T x (.eqRefl _)
      (widths_total p q A R (le_of_lt hpq)).eqSymm (.eqRefl _))
  have scale : Γ ⊢[PRAAx] V ≐ U*num 64 :=
    (pw_add two r (num 6)).eqTrans
      (congrMul (.eqRefl _) (LeanProofs.IPRA.DiophantineNumberTheory.AperyMultibound.pw_num 2 6))
  have room : Γ ⊢[PRAAx] le ((num 11+(num 11+zero))*U) (one*V) :=
    le_congr (.eqRefl _) ((one_mul V).eqTrans scale).eqSymm (by ipra_le 42*𝔞(U))
  exact distance_congr same.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ hV (unit_positive r) room both)

theorem ordered_observation_bound (r v z R B j p q : PTm n)
    (hz : Γ ⊢[PRAAx] S z R B (succ j)) (hpq : Γ ⊢[PRAAx] lt p q)
    (leftBudget : Γ ⊢[PRAAx] le ((two*succ j)*unit v) (unit (height p (succ j) R)))
    (rightBudget : Γ ⊢[PRAAx] le ((two*coefficientBound (R+one))*unit v) (top p (succ j) R)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF r (datum z R B (succ j) q)) (ap2 nameF r (datum z R B (succ j) p))
      (two*unit r+num 7*unit v) (unit v*unit r) := by
  let A := succ j
  let E := etaDen q A R
  let T := top q A R
  let T₀ := top p A R
  let L := gain (R+one) E T
  let y := fixedData (shifted z B) B
  let C₁ := lowerWidth p q A
  let C₂ := middleWidth p q A R
  let C₃ := upperWidth p q A R
  let b := one+(C₁+C₂)
  let x := data (one+C₁) C₂ E L T y
  let l := ap2 nameF r (data one C₁ E L T y)
  let m := ap2 nameF r x
  let h := ap2 nameF r (data b C₃ E L T y)
  let f := ap2 nameF r (datum z R B A q)
  let g := ap2 nameF r (datum z R B A p)
  let K := two*coefficientBound (R+one)
  let H := unit (height p A R)
  let U := unit r
  let V := unit v
  let D := V*U
  have hU := unit_positive (Γ := Γ) r
  have hV := unit_positive (Γ := Γ) v
  have hD := positive_product _ _ hV hU
  have hE := eta_den_positive (Γ := Γ) q A R
  have hH := unit_positive (Γ := Γ) (height p A R)
  have edge : Γ ⊢[PRAAx] b ≐ E*T₀ :=
    (by dsimp only [b]; ipra_ring : Γ ⊢[PRAAx] b ≐ (one+C₁)+C₂).eqTrans
      ((congrAdd (lower_endpoint p q A) (.eqRefl _)).eqTrans (middle_endpoint p q A R (le_of_lt hpq)))
  have fullEnd : Γ ⊢[PRAAx] b+C₃ ≐ T*E :=
    (by dsimp only [b]; ipra_ring : Γ ⊢[PRAAx] b+C₃ ≐ one+(C₁+C₂+C₃)).eqTrans
      ((three_endpoint p q A R (le_of_lt hpq)).eqTrans (mul_comm _ _))
  have lower : Γ ⊢[PRAAx] P (shifted z B) (R+one) B one C₁ E E T :=
    panel_source z R B A _ _ _ _ hz (le_refl one) hE
      (le_trans (le_add_right _ (C₂+C₃))
        (le_congr (by dsimp only [b]; ipra_ring) fullEnd (le_refl _)))
  have higher : Γ ⊢[PRAAx] P (shifted z B) (R+one) B b C₃ E E T :=
    panel_source z R B A _ _ _ _ hz (le_add_right _ _) hE
      (le_congr fullEnd.eqSymm (.eqRefl _) (le_refl _))
  have rawL : Γ ⊢[PRAAx] bounded l ((two*A)*U+H) (H*U) :=
    GaussianGammaZetaMellinLowerRooted.original_observation_bound r p q j z R B L T hz hpq
      (compact_input _ _ _ _ _ _ _ _ lower)
  have atLeast : Γ ⊢[PRAAx] le E b :=
    le_congr (one_mul E) ((mul_comm T₀ E).eqTrans edge.eqSymm) (mul_le_mul_right E (top_positive p A R))
  have rawH : Γ ⊢[PRAAx] bounded h ((K*E)*U+num 3*b) (b*U) :=
    GaussianGammaZetaMellinCompactUpperTail.observation_bound r (shifted z B) (R+one) B
      b C₃ E E T higher atLeast (upper_positive p q A R hpq)
  have paidH : Γ ⊢[PRAAx] le ((K*E)*V) b :=
    le_congr (by dsimp only [K,V]; ipra_ring) ((mul_comm _ _).eqTrans edge.eqSymm) (mul_le_mul_right E rightBudget)
  have paidL : Γ ⊢[PRAAx] le ((two*A)*V) H := leftBudget
  have smallL : Γ ⊢[PRAAx] distanceBounded l qzero (U+V) D :=
    (GaussianReconstructionRoots.distance_zero_iff _ _ _ hD).iffMpr
      (bounded_radius_mono _ _ _ _ _ (positive_product _ _ hH hU) hD
        (by change Γ ⊢[PRAAx] le ((((two*A)*U+H)*(V*U))) ((U+V)*(H*U))
            ipra_le 𝔞(U*U)*sl paidL) rawL)
  have smallH : Γ ⊢[PRAAx] distanceBounded h qzero (U+num 3*V) D :=
    (GaussianReconstructionRoots.distance_zero_iff _ _ _ hD).iffMpr
      (bounded_radius_mono _ _ _ _ _ (positive_product _ _ (le_trans hE atLeast) hU) hD
        (by change Γ ⊢[PRAAx] le (((K*E)*U+num 3*b)*(V*U)) ((U+num 3*V)*(b*U))
            ipra_le 𝔞(U*U)*sl paidH) rawH)
  have cm : Γ ⊢[PRAAx] canonical m := by
    exact GaussianRationalHorner.canonical_congr
      (GaussianCompactRiemannName.name_at evaluatorF r (one+C₁) C₂ E L T y)
      (GaussianCompactRiemannName.sample_canonical evaluatorF r (one+C₁) C₂ E L T y)
  have removeL : Γ ⊢[PRAAx] distanceBounded (qadd l m) m (U+V) D :=
    distance_congr (.eqRefl _) (qzero_add _ cm) (add_zero _) (.eqRefl _)
      (GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ hD smallL
        (GaussianRationalPowerDifference.distance_refl_zero m D hD))
  have removeBoth := distance_congr (.eqRefl _) (GaussianRationalLinearProduct.qadd_zero_right m cm)
    (.eqRefl _) (.eqRefl D) (GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ hD removeL smallH)
  have split : Γ ⊢[PRAAx] distanceBounded f (qadd (qadd l m) h) V D :=
    distance_radius_mono _ _ _ _ _ _ hU hD (le_of_eq_add (d := zero) (by dsimp only [D,U]; ipra_ring))
      (two_splits r z R B j p q hz hpq)
  have eq := middle_alignment z R B A p q hz (le_of_lt hpq)
  have rawM := cross_at nameF nameF x (datum z R B A p) r r (cross_symm _ _ _ _ eq)
  have aligned : Γ ⊢[PRAAx] distanceBounded m g (two*V) D :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hU hU) hD
      (le_of_eq_add (d := zero) (by dsimp only [D,U]; ipra_ring)) rawM
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hD (distance_triangle_same _ _ _ _ _ _ hD split removeBoth) aligned)

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinNestedBound
