import IPRADerivations.Analysis.Gamma.Zeta.GaussianGammaZetaMellinFiniteNested
import IPRADerivations.DiophantineNumberTheory.AperyMultibound

/-!
# Removing both exterior pieces of the actual finite damped window

Keep the actual finite count and read clock on every panel, including
the rescaled middle panel. Only the two exterior norms are estimates.
-/

set_option autoImplicit false
set_option maxHeartbeats 1250000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinFiniteNestedBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (data)
open GaussianGammaCompactCutoffGeometry
  (lowerWidth middleWidth upperWidth lower_positive middle_positive upper_positive widths_total three_endpoint)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaIntegralCutoffs (etaDen top eta_den_positive)
open GaussianGammaZetaMellinFiniteNested (datum interval_source compact_input middle_alignment)
open GaussianGammaZetaMellinFiniteDampedEvaluator (evaluatorF)
open GaussianGammaZetaMellinFiniteDampedModulus (lipschitz)
open GaussianNameEquivalence (cross_at cross_symm)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (qadd qzero canonical positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalSyntheticDivision (qadd_congr qzero_add)
open LeanProofs.IPRA.PTm (num)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "S" => GaussianEulerLowerPowerCoefficients.source
local notation "F" => GaussianCompactRiemannName.nameF evaluatorF
local notation "fd" => GaussianGammaZetaMellinFiniteDampedEvaluator.data
local notation "I" => GaussianEulerCompactAdditivity.intervalSource

private theorem split_at (r a C D E L T x : PTm n)
    (h : Γ ⊢[PRAAx] GaussianCompactNamedAdditivity.input evaluatorF a C D E L T x) :
    Γ ⊢[PRAAx] distanceBounded (ap2 F r (data a (C+D) E L T x))
      (qadd (ap2 F r (data a C E L T x)) (ap2 F r (data (a+C) D E L T x)))
      (num 11) (unit (r+num 6)) :=
  distance_congr (GaussianCompactRiemannName.name_at evaluatorF r a (C+D) E L T x).eqSymm
    (qadd_congr (GaussianCompactRiemannName.name_at evaluatorF r a C E L T x).eqSymm
      (GaussianCompactRiemannName.name_at evaluatorF r (a+C) D E L T x).eqSymm)
    (.eqRefl _) (.eqRefl _) (GaussianCompactNamedAdditivity.sample_additivity evaluatorF r a C D E L T x h)

private theorem split_input (z R B N Q a C D E T : PTm n)
    (h : Γ ⊢[PRAAx] I z R B a (C+D) E T) (hQ : Γ ⊢[PRAAx] le N Q)
    (hc : Γ ⊢[PRAAx] le one C) (hd : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] GaussianCompactNamedAdditivity.input evaluatorF a C D E (lipschitz N R E T) T (fd z B N Q) := by
  have raw := compact_input _ _ _ _ _ _ _ _ _ h hQ
  exact .andI raw.andE₁ (.andI raw.andE₂.andE₁ (.andI hc (.andI hd raw.andE₂.andE₂)))

theorem split_windows_at (r z R B A N Q p q : PTm n)
    (hz : Γ ⊢[PRAAx] S z R B A) (hQ : Γ ⊢[PRAAx] le N Q) (hpq : Γ ⊢[PRAAx] lt p q) :
    let E := etaDen q A R
    let T := top q A R
    let L := lipschitz N (R+one) E T
    let x := fd (shifted z B) B N Q
    let C₁ := lowerWidth p q A
    let C₂ := middleWidth p q A R
    let C₃ := upperWidth p q A R
    let l := ap2 F r (data one C₁ E L T x)
    let m := ap2 F r (data (one+C₁) C₂ E L T x)
    let h := ap2 F r (data (one+(C₁+C₂)) C₃ E L T x)
    Γ ⊢[PRAAx] distanceBounded (ap2 F r (datum z R B N Q A q)) (qadd (qadd l m) h) one (unit r) := by
  intro E T L x C₁ C₂ C₃ l m h
  let s := ap2 F r (data one (C₁+C₂) E L T x)
  let u := ap2 F r (data one (C₁+C₂+C₃) E L T x)
  let U := unit r
  let V := unit (r+num 6)
  have hE := eta_den_positive (Γ := Γ) q A R
  have c₁ := lower_positive p q A hz.andE₁ hpq
  have c₂ := middle_positive (Γ := Γ) p q A R
  have c₃ := upper_positive p q A R hpq
  have endpoint : Γ ⊢[PRAAx] one+(C₁+C₂+C₃) ≐ E*T := three_endpoint p q A R (le_of_lt hpq)
  have full : Γ ⊢[PRAAx] I (shifted z B) (R+one) B one (C₁+C₂+C₃) E T :=
    interval_source z R B A _ _ _ _ hz (le_refl one) hE (le_congr endpoint.eqSymm (.eqRefl _) (le_refl _))
  have firstTwo : Γ ⊢[PRAAx] I (shifted z B) (R+one) B one (C₁+C₂) E T :=
    interval_source z R B A _ _ _ _ hz (le_refl one) hE
      (le_trans (le_congr (by ipra_ring) (add_comm _ _) (add_le_add_right one (le_add_right (C₁+C₂) C₃))) full.andE₂.andE₂)
  have first : Γ ⊢[PRAAx] distanceBounded u (qadd s h) (num 11) V :=
    split_at r one (C₁+C₂) C₃ E L T x
      (split_input _ _ _ _ _ _ _ _ _ _ full hQ (le_trans c₁ (le_add_right _ _)) c₃)
  have next : Γ ⊢[PRAAx] distanceBounded s (qadd l m) (num 11) V :=
    split_at r one C₁ C₂ E L T x (split_input _ _ _ _ _ _ _ _ _ _ firstTwo hQ c₁ c₂)
  have hV := unit_positive (Γ := Γ) (r+num 6)
  have add := GaussianNameArithmetic.sum_distance s (qadd l m) h h (num 11) zero V hV next
    (GaussianRationalPowerDifference.distance_refl_zero h V hV)
  have both := distance_triangle_same _ _ _ _ _ _ hV first add
  have same : Γ ⊢[PRAAx] ap2 F r (datum z R B N Q A q) ≐ u :=
    congrAp2 F (.eqRefl _) (GaussianGammaZetaMellinCutoffWindows.data_congr one one _ _ E E L T x (.eqRefl _)
      (widths_total p q A R (le_of_lt hpq)).eqSymm (.eqRefl _))
  have scale : Γ ⊢[PRAAx] V ≐ U*num 64 :=
    (pw_add two r (num 6)).eqTrans
      (congrMul (.eqRefl _) (LeanProofs.IPRA.DiophantineNumberTheory.AperyMultibound.pw_num 2 6))
  have room : Γ ⊢[PRAAx] le ((num 11+(num 11+zero))*U) (one*V) :=
    le_congr (.eqRefl _) ((one_mul V).eqTrans scale).eqSymm (by ipra_le 42*𝔞(U))
  exact distance_congr same.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ hV (unit_positive r) room both)

theorem comparison_from_tails (r z R B A N Q p q V X Y : PTm n)
    (hz : Γ ⊢[PRAAx] S z R B A) (hQ : Γ ⊢[PRAAx] le N Q) (hpq : Γ ⊢[PRAAx] lt p q)
    (hV : Γ ⊢[PRAAx] le one V)
    (lower : Γ ⊢[PRAAx] bounded (ap2 F r (GaussianGammaZetaMellinFiniteNested.data
      (shifted z B) (R+one) B N Q one (lowerWidth p q A) (etaDen q A R) (top q A R))) X (V*unit r))
    (upper : Γ ⊢[PRAAx] bounded (ap2 F r (GaussianGammaZetaMellinFiniteNested.data (shifted z B) (R+one) B N Q
      (one+(lowerWidth p q A+middleWidth p q A R)) (upperWidth p q A R) (etaDen q A R) (top q A R))) Y (V*unit r)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 F r (datum z R B N Q A q)) (ap2 F r (datum z R B N Q A p))
      (X+Y+num 3*V) (V*unit r) := by
  let E := etaDen q A R
  let T := top q A R
  let L := lipschitz N (R+one) E T
  let x := fd (shifted z B) B N Q
  let C₁ := lowerWidth p q A
  let C₂ := middleWidth p q A R
  let C₃ := upperWidth p q A R
  let d := data (one+C₁) C₂ E L T x
  let l := ap2 F r (data one C₁ E L T x)
  let m := ap2 F r d
  let h := ap2 F r (data (one+(C₁+C₂)) C₃ E L T x)
  let f := ap2 F r (datum z R B N Q A q)
  let g := ap2 F r (datum z R B N Q A p)
  let U := unit r
  let D := V*U
  have hU := unit_positive (Γ := Γ) r
  have hD := positive_product _ _ hV hU
  have lo : Γ ⊢[PRAAx] distanceBounded l qzero X D :=
    (GaussianReconstructionRoots.distance_zero_iff _ _ _ hD).iffMpr lower
  have hi : Γ ⊢[PRAAx] distanceBounded h qzero Y D :=
    (GaussianReconstructionRoots.distance_zero_iff _ _ _ hD).iffMpr upper
  have cm : Γ ⊢[PRAAx] canonical m :=
    GaussianRationalHorner.canonical_congr (GaussianCompactRiemannName.name_at evaluatorF r (one+C₁) C₂ E L T x)
      (GaussianCompactRiemannName.sample_canonical evaluatorF r (one+C₁) C₂ E L T x)
  have removeL : Γ ⊢[PRAAx] distanceBounded (qadd l m) m X D :=
    distance_congr (.eqRefl _) (qzero_add _ cm) (add_zero _) (.eqRefl _)
      (GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ hD lo
        (GaussianRationalPowerDifference.distance_refl_zero m D hD))
  have removeBoth := distance_congr (.eqRefl _) (GaussianRationalLinearProduct.qadd_zero_right m cm)
    (.eqRefl _) (.eqRefl D) (GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ hD removeL hi)
  have split : Γ ⊢[PRAAx] distanceBounded f (qadd (qadd l m) h) V D :=
    distance_radius_mono _ _ _ _ _ _ hU hD (le_of_eq_add (d := zero) (by dsimp only [D,U]; ipra_ring))
      (split_windows_at r z R B A N Q p q hz hQ hpq)
  have eq := middle_alignment z R B N Q A p q hz hQ (le_of_lt hpq)
  have raw := cross_at F F d (datum z R B N Q A p) r r (cross_symm _ _ _ _ eq)
  have aligned : Γ ⊢[PRAAx] distanceBounded m g (two*V) D :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hU hU) hD
      (le_of_eq_add (d := zero) (by dsimp only [D,U]; ipra_ring)) raw
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hD (distance_triangle_same _ _ _ _ _ _ hD split removeBoth) aligned)

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinFiniteNestedBound
