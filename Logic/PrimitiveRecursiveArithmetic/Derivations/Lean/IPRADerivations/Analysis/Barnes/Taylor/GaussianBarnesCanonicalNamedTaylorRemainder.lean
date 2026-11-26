import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalDerivativeBinding
import IPRADerivations.Analysis.Gamma.Ratios.GaussianGammaRationalRatioBinding

/-!
# Exact named Taylor remainder of a Barnes logarithm row

The residual of the original named increment after subtracting its
linear term equals the scaled original relative cubic logarithm plus
the rational quadratic correction. Both names stay within the same
summable radius, with only their intrinsic observation errors.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedTaylorRemainder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalDerivativeAlgebra (linearTerm)
open GaussianBarnesCanonicalDerivativeBinding
  (remainderF remainderData boundNumerator boundDenominator finiteRemainder logClock denominator_positive natScale_at_radius)
open GaussianBarnesCanonicalRelativeStep (source numerator denominator radius local_admission)
open GaussianBarnesCanonicalRelativeTaylor (quadraticError)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianDominantPairAlgebra (radiusPoint radius_bounded)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (addF addData add_fast sum_distance)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qzero qmul qadd_canonical)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSyntheticDivision (qadd_congr qadd_sub_cancel qsub_congr qmul_congr)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Cubic" => GaussianBarnesCanonicalCubicName.nameF
local notation "Scale" => GaussianNamedNaturalScale.nameF
local notation "sd" => GaussianNamedNaturalScale.data
local notation "ld" => GaussianLocalLogarithmName.data
local notation "I" => GaussianBarnesCanonicalDerivativeBinding.nameF
local notation "id" => GaussianBarnesCanonicalDerivativeBinding.data

abbrev nameF : PR 2 := addF (Scale Cubic) constantF

def data (z h B k H : PTm n) : PTm n :=
  addData (sd k k (ld (numerator z h B k) (radius H B k) (denominator z B k))) (quadraticError z h B k)

def sampleCost (k : PTm n) : PTm n := num 6+GaussianBarnesCanonicalDerivativeBinding.sampleCost k

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z h B k H : PTm n) :
    Syn.subst σ (data z h B k H) =
      data (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ k) (Syn.subst σ H) := by simp [data]

@[simp] theorem subst_sampleCost {m : ℕ} (σ : Fin n → PTm m) (k : PTm n) :
    Syn.subst σ (sampleCost k) = sampleCost (Syn.subst σ k) := by simp [sampleCost]

theorem regular (z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H) :
    Γ ⊢[PRAAx] pointCN nameF (data z h B k H) := by
  let x := ld (numerator z h B k) (radius H B k) (denominator z B k)
  have hc := GaussianBarnesCanonicalCubicName.regular _ _ _ (local_admission z h R B k H hs)
  have hl := GaussianGammaFiniteApproximantName.exponential_input Cubic x hc
  exact add_fast _ _ _ _
    (GaussianNamedNaturalScale.name_regular Cubic k k _ x hl (le_refl k)) (constant_regular _)

theorem remainder_regular (z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H) :
    Γ ⊢[PRAAx] pointCN remainderF (remainderData z h R B k) :=
  GaussianNamedDifference.name_regular I constantF _ _
    (GaussianBarnesCanonicalDerivativeBinding.regular z h R B k H hs) (constant_regular _)

theorem analytic_finite_error (p z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data z h B k H)) (finiteRemainder p z h B k) k (unit p) := by
  let a := numerator z h B k
  let E := denominator z B k
  let T := radius H B k
  let s := GaussianFastValueCut.exponent two p
  let t := logClock p k
  let x := ld a T E
  let C := quadraticError z h B k
  let A := radiusPoint k one
  let u := unit t
  let w := GaussianBarnesCanonicalLogRow.roundedCubic t a T E
  have hs' := local_admission z h R B k H hs
  have record : Γ ⊢[PRAAx] ap2 (Scale Cubic) s (sd k k x) ≐ qmul A w := by
    have read := GaussianNamedNaturalScale.sample_at (Γ := Γ) Cubic s k k x
    exact read.eqTrans ((natScale_at_radius k (ap2 Cubic t x)).eqTrans
      (qmul_congr (.eqRefl _) (GaussianBarnesCanonicalCubicName.sample_at t a T E)))
  have read := (GaussianExponentialReference.add_sample (Γ := Γ) (Scale Cubic) constantF (sd k k x) C p).eqTrans
    (qadd_congr record (constant_at s C))
  have raw := GaussianBarnesCanonicalLogRow.rounding_distance t a T E hs'.andE₁
  have budget : Γ ⊢[PRAAx] le (two*u) (one*DyadicComplexLogarithm.unit t) := by
    have grow : Γ ⊢[PRAAx] le (two*u) (u*num 16) := le_of_eq_add (d := num 14*u) (by ipra_ring)
    exact le_congr (.eqRefl _) ((GaussianLocalLogarithmName.unit_factor t).eqSymm.eqTrans (one_mul _).eqSymm) grow
  have close := distance_radius_mono _ _ _ _ one u (GaussianLocalLogarithmName.unit_positive t) (unit_positive t) budget raw
  have scaled := GaussianNamedDifferenceQuotient.scale_distance A _ _ k one u (unit_positive t)
    (radius_bounded k one (le_refl one)) close
  have later : Γ ⊢[PRAAx] le p t := le_trans (le_add_right p _) (GaussianNamedNaturalScale.clock_later s k)
  have weak := GaussianExponentialReference.dyadic_weaken _ _ _ p t later scaled
  have near := sum_distance _ _ _ _ _ _ _ (unit_positive p) weak (distance_refl_zero C (unit p) (unit_positive p))
  exact distance_congr read.eqSymm (.eqRefl _) (by ipra_ring) (.eqRefl _) near

theorem remainder_finite_error (p z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H) :
    Γ ⊢[PRAAx] distanceBounded (ap2 remainderF p (remainderData z h R B k))
      (finiteRemainder p z h B k) (sampleCost k) (unit p) := by
  let x := id z h R B k
  let a := linearTerm z h B k
  let b := finiteRemainder p z h B k
  let U := unit p
  have hU := unit_positive (Γ := Γ) p
  have point := GaussianBarnesCanonicalDerivativeBinding.regular z h R B k H hs
  have first := GaussianNamedDifference.sample_error I constantF x a p point (constant_regular a)
  have raw := GaussianBarnesCanonicalDerivativeBinding.sample_finite_error p z h R B k H hs
  have second := GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hU raw (distance_refl_zero a U hU)
  have aligned := distance_congr (.eqRefl _) (qadd_sub_cancel a b (qadd_canonical _ _))
    (add_zero _) (.eqRefl _) second
  exact distance_triangle_same _ _ _ _ _ _ hU
    (distance_congr (.eqRefl _) (qsub_congr (.eqRefl _) (constant_at p a)) (.eqRefl _) (.eqRefl _) first) aligned

theorem remainder_cross (z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H) :
    Γ ⊢[PRAAx] crossEquivalent remainderF nameF (remainderData z h R B k) (data z h B k H) := by
  apply GaussianNameRingLaws.equivalent_of_envelope remainderF nameF (remainderData z h R B k) (data z h B k H)
    (sampleCost k+k) (remainder_regular z h R B k H hs) (regular z h R B k H hs)
  refine .allI ?_
  let sh (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  have h' : Δ ⊢[PRAAx] source (sh z) (sh h) (sh R) (sh B) (sh k) (sh H) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hs.shift
  have near := remainder_finite_error p (sh z) (sh h) (sh R) (sh B) (sh k) (sh H) h'
  have other := analytic_finite_error p (sh z) (sh h) (sh R) (sh B) (sh k) (sh H) h'
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,sh,p,subst_data,subst_sampleCost,
    GaussianBarnesCanonicalDerivativeBinding.subst_remainderData,PTm.subst_add] using
    distance_triangle_same _ _ _ _ _ _ (unit_positive p) near (distance_symmetric _ _ _ _ (unit_positive p) other)

theorem increment_decomposition (z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H) :
    Γ ⊢[PRAAx] crossEquivalent I (addF constantF nameF) (id z h R B k)
      (addData (linearTerm z h B k) (data z h B k H)) := by
  let x := id z h R B k
  let a := linearTerm z h B k
  let c := remainderData z h R B k
  let y := data z h B k H
  have hx := GaussianBarnesCanonicalDerivativeBinding.regular z h R B k H hs
  have ha := constant_regular (Γ := Γ) a
  have hc := remainder_regular z h R B k H hs
  have hy := regular z h R B k H hs
  have first := GaussianGammaRationalRatioBinding.difference_add_recover I constantF x a hx ha
  have second := GaussianNamedGammaHalfShift.add_cross remainderF nameF constantF constantF c y a a hc hy ha ha
    (remainder_cross z h R B k H hs) (cross_refl constantF a ha)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ first)
    (cross_trans _ _ _ _ _ _ second (GaussianNameRingLaws.add_commutative nameF constantF y a hy ha))

private theorem remainder_slack (z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H)
    (hH : Γ ⊢[PRAAx] le H B) :
    Γ ⊢[PRAAx] GaussianNamedConstantRateFromSlack.sampleSlack remainderF (remainderData z h R B k) qzero
      (boundNumerator R H) (boundDenominator B k) (sampleCost k) := by
  refine .allI ?_
  let sh (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  let nameSample := ap2 remainderF p (remainderData (sh z) (sh h) (sh R) (sh B) (sh k))
  let finite := finiteRemainder p (sh z) (sh h) (sh B) (sh k)
  let A := boundNumerator (sh R) (sh H)
  let D := boundDenominator (sh B) (sh k)
  have h' : Δ ⊢[PRAAx] source (sh z) (sh h) (sh R) (sh B) (sh k) (sh H) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hs.shift
  have hH' : Δ ⊢[PRAAx] le (sh H) (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hH.shift
  have first := remainder_finite_error p (sh z) (sh h) (sh R) (sh B) (sh k) (sh H) h'
  have second : Δ ⊢[PRAAx] distanceBounded finite qzero A D :=
    bound_congr (GaussianRationalReconstruction.qsub_zero_right finite (qadd_canonical _ _)).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianBarnesCanonicalDerivativeBinding.finite_remainder_bound p (sh z) (sh h) (sh R) (sh B) (sh k) (sh H) h' hH')
  have joined : Δ ⊢[PRAAx] distanceBounded nameSample qzero (sampleCost (sh k)*D+A*unit p) (unit p*D) :=
    GaussianRationalPanelTailDistance.triangle _ _ _ _ _ _ _ (unit_positive p)
      (denominator_positive (sh z) (sh h) (sh R) (sh B) (sh k) (sh H) h') first second
  simpa only [GaussianNamedConstantRateFromSlack.sampleSlack,GaussianRationalSlackRemoval.slack,
    distanceBounded,unit,p,nameSample,A,D,sh,Syn.shift,GaussianRationalHorner.subst_qzero,
    GaussianBarnesCanonicalDerivativeBinding.subst_remainderData,
    GaussianBarnesCanonicalDerivativeBinding.subst_boundNumerator,
    GaussianBarnesCanonicalDerivativeBinding.subst_boundDenominator,subst_sampleCost] using
    distance_congr (.eqRefl _) (.eqRefl _) (add_comm _ _) (mul_comm _ _) joined

theorem remainder_observation_bound (p z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H)
    (hH : Γ ⊢[PRAAx] le H B) :
    Γ ⊢[PRAAx] bounded (ap2 remainderF p (remainderData z h R B k))
      (boundNumerator R H*unit p+boundDenominator B k) (boundDenominator B k*unit p) := by
  have b := GaussianNamedConstantRateFromSlack.observation_bound remainderF (remainderData z h R B k) qzero
    (boundNumerator R H) (boundDenominator B k) (sampleCost k) p
    (remainder_regular z h R B k H hs) (denominator_positive z h R B k H hs) (remainder_slack z h R B k H hs hH)
  have canonical := GaussianNameArithmetic.add_canonical (Γ := Γ) I (GaussianNameRingLaws.negativeF constantF)
    (id z h R B k) (GaussianNameRingLaws.negativeData (linearTerm z h B k)) p
  exact bound_congr (GaussianRationalReconstruction.qsub_zero_right _ canonical) (.eqRefl _) (.eqRefl _) b

theorem remainder_rate (z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H) (hH : Γ ⊢[PRAAx] le H B) :
    Γ ⊢[PRAAx] independentRate remainderF constantF (remainderData z h R B k) qzero (boundNumerator R H) (boundDenominator B k) :=
  GaussianNamedConstantRateFromSlack.independent_rate remainderF (remainderData z h R B k) qzero
    (boundNumerator R H) (boundDenominator B k) (sampleCost k)
    (remainder_regular z h R B k H hs) (denominator_positive z h R B k H hs) (remainder_slack z h R B k H hs hH)

theorem actual_Barnes_named_logarithm_row_decomposition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     let k := var 4
     let H := var 5
     source z h R B k H ⟶ crossEquivalent I (addF constantF nameF) (id z h R B k)
       (addData (linearTerm z h B k) (data z h B k H))) :=
  closeUniv 6 (.impI (increment_decomposition _ _ _ _ _ _ Prf.hyp0))

theorem actual_Barnes_named_Taylor_remainder_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     let k := var 4
     let H := var 5
     source z h R B k H ⋏ le H B ⟶
       (crossEquivalent remainderF nameF (remainderData z h R B k) (data z h B k H) ⋏
         independentRate remainderF constantF (remainderData z h R B k) qzero (boundNumerator R H) (boundDenominator B k))) :=
  closeUniv 6 (.impI (.andI (remainder_cross _ _ _ _ _ _ Prf.hyp0.andE₁)
    (remainder_rate _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedTaylorRemainder
