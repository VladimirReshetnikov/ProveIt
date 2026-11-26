import IPRADerivations.Analysis.Gamma.Digamma.GaussianLogGammaEulerDigammaFractionsCofinal
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.GaussianLogGammaEulerLinearSlope
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.GaussianLogGammaEulerPositiveAxis
import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaSeries
import IPRADerivations.Analysis.Beta.GaussianEulerBetaProductPascal
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedAddRate

/-!
# The two digamma series on the positive rational axis

The complex C27 reciprocal rows agree with the native C28 rows at positive
rational inputs. At the same final reciprocal row, the two finite
corrections differ by one terminal reciprocal.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerDigammaPositiveAxis

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale oneCode normSq normSq_scale normSq_one)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF harmonicPoint)
open GaussianGammaDerivativeAtOne (negativeGammaF negativeGammaData negativeGamma_regular)
open GaussianGammaDigammaFiniteSum (reciprocal_entry)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerRepresentation (subst_argument)
open GaussianLogGammaEulerReciprocalSlope (shiftedPoint rowBody reciprocalSum row_at)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianLogGammaEulerResidualRadius (radius)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at denominator_positive)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalFiniteSum (termsEqual)
open GaussianRationalHorner
  (ofGaussian_canonical ofGaussian_represents canonical_unique positive_product qadd qmul)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalReciprocal (qone qone_represents_scaled reciprocal reciprocal_canonical reciprocal_identity)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr qone_canonical)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "realSource" => GaussianStirlingGammaLogarithm.source
local notation "realBody" => GaussianGammaDigammaFiniteSum.reciprocalBody
local notation "realSum" => GaussianGammaDigammaFiniteSum.reciprocalSum
local notation "realPart" => GaussianGammaDigammaSeries.partialValue
local notation "complexPart" => GaussianLogGammaEulerDigammaFractions.correction
local notation "finiteF" => GaussianLogGammaEulerDigammaFractions.nameF
local notation "finiteData" => GaussianLogGammaEulerDigammaFractions.data
local notation "realFiniteF" => GaussianGammaDigammaSeries.nameF
local notation "realFiniteData" => GaussianGammaDigammaSeries.data
local notation "realF" => GaussianGammaDigammaNative.nameF
local notation "realData" => GaussianGammaDigammaNative.data
local notation "slopeF" => GaussianLogGammaEulerReciprocalSlopeCofinal.nameF
local notation "slopeData" => GaussianLogGammaEulerReciprocalSlopeCofinal.canonicalData
local notation "complexF" => GaussianLogGammaEulerDigammaFractionsCofinal.nameF
local notation "complexData" => GaussianLogGammaEulerDigammaFractionsCofinal.data

private theorem half_plane (A D : PTm n) (h : Γ ⊢[PRAAx] realSource A D) :
    Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source A D zero :=
  .andI (.andI h.andE₁ (.orI₁ (.eqRefl _))) h.andE₂

private theorem argument_axis (A D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] argument A zero D zero ≐ fraction A D :=
  GaussianGammaFiniteValueProperness.fraction_equal (native A zero zero) (scale A oneCode) D hD
    (GaussianLogGammaEulerPositiveAxis.native_axis_equal A zero (.orI₁ (.eqRefl _)))

private theorem fraction_reciprocal (A D : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx] reciprocal (fraction A D) ≐ fraction D A := by
  let z := fraction A D
  let v := fraction D A
  let a := scale A oneCode
  have hDD := positive_product _ _ hD hD
  have nn : Γ ⊢[PRAAx] normSq a ≐ A*A :=
    (normSq_scale A oneCode).eqTrans ((congrMul (.eqRefl _) normSq_one).eqTrans (by ipra_ring))
  have low : Γ ⊢[PRAAx] GaussianNameReciprocal.lower z D := by
    apply GaussianRationalMetric.comparison_of_cleared _ _ (one*one) (normSq a) (D*D) (D*D) hDD hDD
      (GaussianRationalMetric.squared_tolerance_represents one D hD)
      (GaussianRationalMetric.qnormSq_represents z a D hD (ofGaussian_represents a D hD))
    exact le_congr (by ipra_ring) (congrMul nn (.eqRefl _)).eqSymm
      (mul_le_mul_right (D*D) (positive_product _ _ hA hA))
  have hp := GaussianNameReciprocal.lower_norm_positive z D hD low
  have prod : Γ ⊢[PRAAx] qmul z v ≐ qone :=
    (GaussianEulerDampedTimeRate.fraction_product A D D A hD hA).eqTrans
      ((GaussianCompactRiemannName.fraction_congr _ _ _ _ (mul_comm A D) (.eqRefl _)).eqTrans
        (canonical_unique _ _ _ (D*A) (ofGaussian_canonical _ _ (positive_product _ _ hD hA)) qone_canonical
          (positive_product _ _ hD hA) (ofGaussian_represents _ _ (positive_product _ _ hD hA)) (qone_represents_scaled _)))
  exact GaussianEulerBetaProductPascal.inverse_unique z (reciprocal z) v (reciprocal_canonical z)
    (ofGaussian_canonical _ _ hA) (reciprocal_identity z hp) prod

theorem row_agrees (A D k : PTm n) (h : Γ ⊢[PRAAx] realSource A D) :
    Γ ⊢[PRAAx] inst2 rowBody k (argument A zero D zero) ≐ inst2 realBody k (pairT A D) := by
  have ha := le_trans h.andE₁ (le_add_right A (k*D))
  have x := (GaussianLogGammaEulerLinearSlope.shifted_point A zero D zero k h.andE₂).eqTrans
    (argument_axis (A+k*D) D h.andE₂)
  exact (row_at (argument A zero D zero) k).eqTrans
    ((GaussianNameReciprocal.reciprocal_congr x).eqTrans
      ((fraction_reciprocal (A+k*D) D ha h.andE₂).eqTrans (reciprocal_entry A D k).eqSymm))

theorem reciprocal_sum_agrees (A D N : PTm n) (h : Γ ⊢[PRAAx] realSource A D) :
    Γ ⊢[PRAAx] reciprocalSum A zero D zero N ≐ realSum A D N := by
  apply GaussianRationalFiniteSum.sum_congr_bounded rowBody realBody N (argument A zero D zero) (pairT A D)
  refine .allI (.impI ?_)
  let s (x : PTm n) := Syn.shift x
  have hs : Γ.map Fm.shift ⊢[PRAAx] realSource (s A) (s D) := by
    simpa [s,Fm.shift,Syn.shift,GaussianStirlingGammaLogarithm.source] using h.shift
  simpa only [termsEqual,s,Syn.shift,subst_argument,subst_pairT,ConciseIPRA.PTm.subst_zero] using
    row_agrees (s A) (s D) (var 0) hs.wk

theorem correction_endpoint (A D N : PTm n) (h : Γ ⊢[PRAAx] realSource A D) :
    Γ ⊢[PRAAx] complexPart A zero D zero N ≐
      qsub (realPart A D N) (reciprocal (shiftedPoint (argument A zero D zero) N)) := by
  let z := argument A zero D zero
  let w := reciprocal (shiftedPoint z N)
  have e : Γ ⊢[PRAAx] reciprocalSum A zero D zero (succ N) ≐ qadd (realSum A D N) w :=
    (GaussianRationalFiniteSum.sum_succ rowBody N z).eqTrans
      (qadd_congr (reciprocal_sum_agrees A D N h) (row_at z N))
  exact (GaussianLogGammaEulerDigammaFractions.correction_value A zero D zero N h.andE₂).eqTrans
    ((qsub_congr (.eqRefl _) e).eqTrans
      (GaussianRationalInverseQuadraticAlgebra.subtract_sum (harmonicPoint N) (realSum A D N) w).eqSymm)

theorem correction_distance (A D N : PTm n) (h : Γ ⊢[PRAAx] realSource A D)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] distanceBounded (complexPart A zero D zero N) (realPart A D N) one N := by
  let c := complexPart A zero D zero N
  let x := realPart A D N
  let z := shiftedPoint (argument A zero D zero) N
  let w := reciprocal z
  have hx := GaussianRationalMetric.qsub_canonical (Γ := Γ) (harmonicPoint N) (realSum A D N)
  have recover : Γ ⊢[PRAAx] qsub x c ≐ w :=
    (qsub_congr (.eqRefl x) (correction_endpoint A D N h)).eqTrans
      ((qsub_congr (GaussianRationalLinearProduct.add_sub_right w x hx).eqSymm (.eqRefl _)).eqTrans
        (GaussianReciprocalHorner.qsub_add_cancel w (qsub x w) (reciprocal_canonical z)))
  have bound := GaussianRationalReciprocal.inverse_bound z N hN
    (GaussianLogGammaEulerReciprocalSlope.shifted_lower A zero D zero N (half_plane A D h))
  exact distance_symmetric x c one N hN
    (GaussianRationalReciprocal.bound_congr recover.eqSymm (.eqRefl _) (.eqRefl _) bound)

theorem finite_observations (A D N p q : PTm n) (h : Γ ⊢[PRAAx] realSource A D)
    (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 finiteF p (finiteData A zero D zero N)) (ap2 realFiniteF q (realFiniteData A D N))
      (rateNumerator one N p q) (rateDenominator N p q) := by
  let C := complexPart A zero D zero N
  let R := realPart A D N
  have move := GaussianNamedAddRate.constant_rate C R one N hN (correction_distance A D N h hN)
  have common := GaussianNamedAddRate.self_rate (Γ := Γ) negativeGammaF negativeGammaData negativeGamma_regular
  have raw := GaussianNamedAddRate.independent_at negativeGammaF constantF negativeGammaF constantF
    negativeGammaData C negativeGammaData R zero one one N p q (.andI (.andI (le_refl one) hN) (.andI common move))
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by unfold rateNumerator GaussianNamedRateComposition.leadingNumerator GaussianNamedRateComposition.leadingDenominator; ipra_ring)
    (by unfold rateDenominator GaussianNamedRateComposition.leadingDenominator; ipra_ring) raw

private theorem slope_observations (A D p q : PTm n) (h : Γ ⊢[PRAAx] realSource A D) :
    Γ ⊢[PRAAx] distanceBounded (ap2 slopeF p (slopeData A zero D zero)) (ap2 realF q (realData A D))
      (unit p+unit q) (unit p*unit q) := by
  let X := ap2 slopeF p (slopeData A zero D zero)
  let Y := ap2 realF q (realData A D)
  let P := unit p
  let Q := unit q
  let L := radius A zero + two
  let C := L + A + num 5
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have hpq := positive_product _ _ hp hq
  apply GaussianRationalSlackRemoval.slack_removal_at (qsub X Y) (P+Q) (P*Q) C hpq
  let t := GaussianRationalSlackRemoval.precision (qsub X Y) (P+Q) (P*Q) C
  let N := unit t
  let W := (P*Q)*N
  have ht := unit_positive (Γ := Γ) t
  have hw := positive_product _ _ hpq ht
  have a₀ := GaussianLogGammaEulerDigammaFractionsRate.canonical_fraction_rate A zero D zero N (half_plane A D h) ht
  have a₁ := rate_at slopeF finiteF (slopeData A zero D zero) (finiteData A zero D zero N) L N p t a₀
  have a := distance_radius_mono _ _ _ _ ((L+one)*(P*Q)+Q*N) W (denominator_positive N p t ht) hw
    (le_of_eq_add (d := zero) (by dsimp only [rateNumerator,rateDenominator,W,P,Q,N]; ipra_ring)) a₁
  have b₀ := finite_observations A D N t t h ht
  have b := distance_radius_mono _ _ _ _ (num 3*(P*Q)) W (denominator_positive N t t ht) hw
    (le_of_eq_add (d := zero) (by dsimp only [rateNumerator,rateDenominator,W,P,Q,N]; ipra_ring)) b₀
  have c₀ := GaussianGammaDigammaSeries.original_rate A D N h ht
  have c₁ := rate_at realF realFiniteF (realData A D) (realFiniteData A D N) A N q t c₀
  have c := distance_radius_mono _ _ _ _ ((A+one)*(P*Q)+P*N) W (denominator_positive N q t ht) hw
    (le_of_eq_add (d := zero) (by dsimp only [rateNumerator,rateDenominator,W,P,Q,N]; ipra_ring))
    (distance_symmetric _ _ _ _ (denominator_positive N q t ht) c₁)
  change Γ ⊢[PRAAx] distanceBounded X Y ((P+Q)*N+C*(P*Q)) W
  exact distance_congr (.eqRefl X) (.eqRefl Y) (by dsimp only [C]; ipra_ring) (.eqRefl W)
    (distance_triangle_same _ _ _ _ _ _ hw (distance_triangle_same _ _ _ _ _ _ hw a b) c)

theorem original_gamma_derivative_over_gamma (A D : PTm n) (h : Γ ⊢[PRAAx] realSource A D) :
    Γ ⊢[PRAAx] crossEquivalent complexF realF (complexData A zero D zero) (realData A D) := by
  have direct : Γ ⊢[PRAAx] crossEquivalent slopeF realF (slopeData A zero D zero) (realData A D) := by
    refine .allI (.allI ?_)
    let Δ := (Γ.map Fm.shift).map Fm.shift
    let s (v : PTm n) := Syn.shift (Syn.shift v)
    have hs : Δ ⊢[PRAAx] realSource (s A) (s D) := by
      simpa [Δ,s,Fm.shift,Syn.shift,GaussianStirlingGammaLogarithm.source] using h.shift.shift
    simpa only [crossEquivalent,Δ,s,Syn.shift,GaussianLogGammaEulerReciprocalSlopeCofinal.canonicalData,
      GaussianLogGammaEulerReciprocalSlopeCofinal.subst_data,GaussianLogGammaEulerResidualRadius.subst_radius,
      GaussianGammaDigammaNative.subst_data,ConciseIPRA.PTm.subst_zero] using slope_observations (s A) (s D) (var 1) (var 0) hs
  have literal := GaussianLogGammaEulerDigammaFractionsCofinal.cofinal_equivalent A zero D zero (half_plane A D h)
  exact cross_trans complexF slopeF realF _ _ _ (cross_symm slopeF complexF _ _ literal) direct

theorem actual_complex_digamma_positive_axis_is_original_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (realSource (var 0) (var 1) ⟶ crossEquivalent complexF realF
        (complexData (var 0) zero (var 1) zero) (realData (var 0) (var 1))) :=
  closeUniv 2 (.impI (original_gamma_derivative_over_gamma _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerDigammaPositiveAxis
