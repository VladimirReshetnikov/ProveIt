import IPRADerivations.Analysis.Gamma.Digamma.Bernoulli.FirstTerm.GaussianDigammaFirstBernoulliEndpoints
import IPRADerivations.Analysis.Gamma.Digamma.Bernoulli.FirstTerm.GaussianDigammaFirstBernoulliMassError
import IPRADerivations.Analysis.Stirling.AllOrders.FirstPanel.GaussianStirlingAllOrderFirstPanelCommonMesh

/-!
# The original weighted digamma panel against its harmonic logarithm

On any positive mesh Q the first weighted Bernoulli panel approximates
the trapezoid endpoint term minus the harmonic interval. The same
finite error transfers to the named logarithm at a dyadic observation.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianDigammaFirstBernoulliLocal

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianDigammaFirstBernoulliEndpoints (trapezoid exact_correction)
open GaussianDigammaFirstBernoulliMassError (integral power_mass_error harmonic_mass_error)
open GaussianDigammaFirstBernoulliPanelSum (squareCoeff cubeCoeff actual_first_panel)
open GaussianEuclideanDistanceName (fraction fraction_order pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNamedDifference (difference_distance sample_error)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same distance_radius_mono_den)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (qsub bounded distanceBounded)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr)
open GaussianStirlingAllOrderDiscreteParts (sub)
open GaussianStirlingAllOrderPanelPartsRecurrence (panelMass)
open GaussianStirlingAllOrderPanelPartsRows (scalar_order_bound)
open GaussianStirlingAllOrderPanelTail (panel)
open GaussianStirlingAllOrderReciprocalWeightError (power)
open RationalAlgebra (add_associative add_commutative add_congr)
open RationalArithmetic (multiply negative)
open RationalGaussianEmbedding (embed embed_add embed_negative embed_multiply)
open RationalGaussianRealPart (embed_congr)
open RationalHarmonicInterval (interval)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "hd" => GaussianHarmonicLogarithmName.data

def reference (U B Q : PTm n) : PTm n := sub (trapezoid U B) (interval (U+B) U Q)

def coefficient (U B : PTm n) : PTm n := (two*U+B)*power 2 B+one+U*(U+B)*power 3 B

def nameF : PR 2 := GaussianNamedDifference.nameF constantF H
def nameData (U B : PTm n) : PTm n := GaussianNamedDifference.data (embed (trapezoid U B)) (hd (U+B) U)

theorem embed_sub (a b : PTm n) : Γ ⊢[PRAAx] embed (sub a b) ≐ qsub (embed a) (embed b) :=
  (embed_add a (negative b)).eqTrans (qadd_congr (.eqRefl _) (embed_negative b))

private theorem coefficient_bound (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] bounded (embed (fraction a b)) a one := by
  apply scalar_order_bound _ _ _ (le_refl one)
  · exact fraction_order _ _ _ _ (le_refl one) hb (by ipra_le 𝔞 a)
  · exact fraction_order _ _ _ _ hb (le_refl one) (by ipra_le 𝔞 a*sl hb)

private theorem weighted_distance (c x y M A Q : PTm n) (hQ : Γ ⊢[PRAAx] le one Q)
    (hc : Γ ⊢[PRAAx] bounded c M one) (h : Γ ⊢[PRAAx] distanceBounded x y A Q) :
    Γ ⊢[PRAAx] distanceBounded (qmul c x) (qmul c y) (M*A) Q :=
  GaussianRationalReciprocal.bound_congr (GaussianRationalRoundedPower.multiplication_difference c x y).eqSymm
    (.eqRefl _) (one_mul _) (GaussianRationalReciprocal.bounded_product c (qsub x y) M one A Q (le_refl one) hQ hc h)

private theorem sub_rotate (x y z : PTm n) : Γ ⊢[PRAAx] sub (sub x y) z ≐ sub (sub x z) y :=
  (add_associative x (negative y) (negative z)).eqTrans
    ((add_congr (.eqRefl _) (add_commutative _ _)).eqTrans (add_associative x _ _).eqSymm)

private theorem embed_split (c a b d e : PTm n) :
    Γ ⊢[PRAAx] embed (sub (sub (multiply c a) b) (multiply d e)) ≐
      qsub (qsub (qmul (embed c) (embed a)) (embed b)) (qmul (embed d) (embed e)) :=
  (embed_sub _ _).eqTrans (qsub_congr ((embed_sub _ _).eqTrans (qsub_congr (embed_multiply _ _) (.eqRefl _)))
    (embed_multiply _ _))

theorem finite_error (U B Q : PTm n) (hU : Γ ⊢[PRAAx] le one U) (hB : Γ ⊢[PRAAx] le one B)
    (hQ : Γ ⊢[PRAAx] le one Q) :
    Γ ⊢[PRAAx] distanceBounded (embed (panel 0 two U B (B*Q) zero)) (embed (reference U B Q)) (coefficient U B) Q := by
  let M := B*Q
  let s := squareCoeff U B
  let t := cubeCoeff U B
  let a := panelMass 2 U B M
  let b := panelMass 1 U B M
  let c := panelMass 3 U B M
  let x := integral 2 U B
  let y := interval (U+B) U Q
  let z := integral 3 U B
  have hM : Γ ⊢[PRAAx] le one M := positive_product _ _ hB hQ
  have hQM : Γ ⊢[PRAAx] le Q M := by unfold M; ipra_le 𝔞 Q*sl hB
  have widen (f g C : PTm n) (eq : Γ ⊢[PRAAx] distanceBounded f g C M) :
      Γ ⊢[PRAAx] distanceBounded f g C Q :=
    distance_radius_mono_den hQ hQM eq
  have p2 := widen _ _ _ (power_mass_error 2 (by omega) U B M hU hM)
  have p3 := widen _ _ _ (power_mass_error 3 (by omega) U B M hU hM)
  have p1 := harmonic_mass_error U B Q hU hB hQ
  have hs : Γ ⊢[PRAAx] bounded (embed s) (two*U+B) one := coefficient_bound _ _ hB
  have ht : Γ ⊢[PRAAx] bounded (embed t) (U*(U+B)) one :=
    coefficient_bound _ _ (positive_product _ _ hB hB)
  have d2 := weighted_distance (embed s) (embed a) (embed x) (two*U+B) _ _ hQ hs p2
  have d3 := weighted_distance (embed t) (embed c) (embed z) (U*(U+B)) _ _ hQ ht p3
  have total := difference_distance _ _ _ _ _ _ _ hQ (difference_distance _ _ _ _ _ _ _ hQ d2 p1) d3
  have left := (embed_congr (actual_first_panel U B M hU hB hM)).eqTrans (embed_split s a b t c)
  have e : Γ ⊢[PRAAx] sub (sub (multiply s x) y) (multiply t z) ≐ reference U B Q :=
    (sub_rotate _ _ _).eqTrans (add_congr (exact_correction U B hU hB) (.eqRefl _))
  have right := (embed_split (Γ := Γ) s x y t z).eqSymm.eqTrans (embed_congr e)
  exact distance_congr left.eqSymm right (.eqRefl _) (.eqRefl _) total

theorem name_regular (U B : PTm n) (hU : Γ ⊢[PRAAx] le one U) :
    Γ ⊢[PRAAx] pointCN nameF (nameData U B) :=
  GaussianNamedDifference.name_regular _ _ _ _ (constant_regular _)
    (GaussianHarmonicLogarithmName.name_regular (U+B) U (.andI (le_trans hU (le_add_right _ _)) hU))

theorem named_error (p U B Q : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (hB : Γ ⊢[PRAAx] le one B) (hQ : Γ ⊢[PRAAx] le (unit p) Q) :
    Γ ⊢[PRAAx] distanceBounded (embed (panel 0 two U B (B*Q) zero))
      (ap2 nameF p (nameData U B)) (coefficient U B+num 8) (unit p) := by
  let a := U+B
  let t := embed (trapezoid U B)
  let R := GaussianHarmonicLogarithmProduct.mesh p
  have ha : Γ ⊢[PRAAx] le one a := le_trans hU (le_add_right _ _)
  have hp := unit_positive (Γ := Γ) p
  have hQ' := le_trans hp hQ
  have h0 := finite_error U B Q hU hB hQ'
  have left := distance_radius_mono _ _ _ _ _ _ hQ' hp (le_mul_mono (le_refl _) hQ) h0
  have obs := GaussianStirlingAllOrderFirstPanelCommonMesh.harmonic_observations a U Q R p ha hU hQ
    (GaussianHarmonicLogarithmProduct.mesh_later p)
  have ch := distance_congr (.eqRefl _) (GaussianHarmonicLogarithmName.sample_at p a U).eqSymm (.eqRefl _) (.eqRefl _) obs
  have diff := difference_distance t t _ _ zero two _ hp (distance_refl_zero _ _ hp) ch
  have middle := distance_congr (embed_sub (trapezoid U B) (interval a U Q)).eqSymm (.eqRefl _)
    (zero_add two) (.eqRefl _) diff
  have tail := distance_congr (.eqRefl _) (qsub_congr (constant_at p t) (.eqRefl _)) (.eqRefl _) (.eqRefl _)
    (sample_error constantF H t (hd a U) p (constant_regular _) (GaussianHarmonicLogarithmName.name_regular a U (.andI ha hU)))
  have e := distance_triangle_same _ _ _ _ _ _ hp left middle
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp e (distance_symmetric _ _ _ _ hp tail))

theorem actual_first_digamma_Bernoulli_named_panel_error_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (le one (var 1) ⟶ le one (var 2) ⟶ le (unit (var 0)) (var 3) ⟶
        distanceBounded (embed (panel 0 two (var 1) (var 2) ((var 2)*(var 3)) zero))
          (ap2 nameF (var 0) (nameData (var 1) (var 2))) (coefficient (var 1) (var 2)+num 8) (unit (var 0))) :=
  closeUniv 4 (.impI (.impI (.impI (named_error _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianDigammaFirstBernoulliLocal
