import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalDerivativeAlgebra
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalLogFactor
import IPRADerivations.Analysis.Names.Rates.GaussianNamedConstantRateFromSlack

/-!
# First-order comparison for the original named Barnes logarithm row

The actual cubic-logarithm increment differs from the rational slope
times the step by at most `(3R+342)*H²/(B*k)²`. The finite calculation
uses the original logarithm and correction samplers. Removing the
auxiliary precision slack leaves the intrinsic name errors at independent
requested clocks.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDerivativeBinding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalDerivativeAlgebra (linearTerm localQuadratic correctionDifference cancellation)
open GaussianBarnesCanonicalRelativeStep (source numerator denominator radius local_admission logarithm_increment)
open GaussianBarnesCanonicalRelativeTaylor (quadraticError cubicError quadratic_bound finite_cubic_bound)
open GaussianBarnesCanonicalLogRow (local_source)
open GaussianBarnesCanonicalLogFactor (correctedF correctedData fullF)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianDominantPairAlgebra (radiusPoint radiusNumerator radius_bounded radius_represents)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (sum_difference sum_distance)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalCoefficientScaling (qmul_add)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open GaussianRationalHorner (qzero qadd qmul qadd_canonical canonical_unique represents_congr ofGaussian_canonical positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub qsub_canonical)
open GaussianRationalNaturalScale (natScale naturalPoint natScale_as_product natural_point_represents)
open GaussianRationalPowerDifference (bounded_sum_same distance_refl_zero)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr qadd_sub_cancel)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianReciprocalHorner (qadd_commutative)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Q" => GaussianBarnesCanonicalLogFactor.nameF
local notation "qd" => GaussianBarnesCanonicalLogFactor.data
local notation "L" => GaussianLocalLogarithmName.pointF
local notation "ld" => GaussianLocalLogarithmName.data
local notation "DF" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data
local notation "corr" => GaussianBarnesCanonicalFactor.correction

abbrev nameF : PR 2 := DF Q Q

def data (z h R B k : PTm n) : PTm n := dd (qd (add z h) R B k) (qd z R B k)

abbrev remainderF : PR 2 := DF nameF constantF

def remainderData (z h R B k : PTm n) : PTm n := dd (data z h R B k) (linearTerm z h B k)

def boundNumerator (R H : PTm n) : PTm n := (num 3*R+num 342)*H*H
def boundDenominator (B k : PTm n) : PTm n := (B*k)*(B*k)
def sampleCost (k : PTm n) : PTm n := num 12+num 9*k

def logClock (p k : PTm n) : PTm n :=
  GaussianNamedNaturalScale.clock (GaussianFastValueCut.exponent two p) k

def finiteRemainder (p z h B k : PTm n) : PTm n :=
  qadd (cubicError z h B k (DyadicComplexLogarithm.precision (logClock p k))) (quadraticError z h B k)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z h R B k : PTm n) :
    Syn.subst σ (data z h R B k) =
      data (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ k) := by simp [data]

@[simp] theorem subst_remainderData {m : ℕ} (σ : Fin n → PTm m) (z h R B k : PTm n) :
    Syn.subst σ (remainderData z h R B k) =
      remainderData (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ k) :=
  by simp [remainderData]

@[simp] theorem subst_boundNumerator {m : ℕ} (σ : Fin n → PTm m) (R H : PTm n) :
    Syn.subst σ (boundNumerator R H) = boundNumerator (Syn.subst σ R) (Syn.subst σ H) := by simp [boundNumerator]

@[simp] theorem subst_boundDenominator {m : ℕ} (σ : Fin n → PTm m) (B k : PTm n) :
    Syn.subst σ (boundDenominator B k) = boundDenominator (Syn.subst σ B) (Syn.subst σ k) := by simp [boundDenominator]

@[simp] theorem subst_sampleCost {m : ℕ} (σ : Fin n → PTm m) (k : PTm n) :
    Syn.subst σ (sampleCost k) = sampleCost (Syn.subst σ k) := by simp [sampleCost]

theorem denominator_positive (z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H) :
    Γ ⊢[PRAAx] le one (boundDenominator B k) := by
  have d := positive_product B k hs.andE₁.andE₁ hs.andE₁.andE₂.andE₁
  exact positive_product _ _ d d

theorem regular (z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H) :
    Γ ⊢[PRAAx] pointCN nameF (data z h R B k) :=
  GaussianNamedDifference.name_regular Q Q _ _
    (GaussianBarnesCanonicalLogFactor.regular (add z h) R B k hs.andE₂.andE₁)
    (GaussianBarnesCanonicalLogFactor.regular z R B k hs.andE₁)

theorem natScale_at_radius (k v : PTm n) :
    Γ ⊢[PRAAx] natScale k v ≐ qmul (radiusPoint k one) v := by
  let x := ComplexLogarithmRemainder.scale k ComplexLogarithmRemainder.oneCode
  have e : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (radiusNumerator k) x := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [x,radiusNumerator,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
        GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one,ComplexLogarithmRemainder.eval_re_code,
        ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat] <;> (try ipra_simps) <;> ring
  have cp : Γ ⊢[PRAAx] naturalPoint k ≐ radiusPoint k one :=
    canonical_unique _ _ x one (ofGaussian_canonical _ _ (le_refl one)) (ofGaussian_canonical _ _ (le_refl one))
      (le_refl one) (natural_point_represents k) (represents_congr (.eqRefl _) e (.eqRefl _) (radius_represents k one (le_refl one)))
  exact (natScale_as_product k v).eqTrans (qmul_congr cp (.eqRefl v))

private theorem corrected_at (p z R B k : PTm n) :
    Γ ⊢[PRAAx] ap2 correctedF p (correctedData z R B k) ≐
      qadd (qmul (radiusPoint k one) (ap2 L (logClock p k) (ld z (R*B) (B*k)))) (corr z B k) := by
  let s := GaussianFastValueCut.exponent two p
  let x := ld z (R*B) (B*k)
  let e := corr z B k
  have r : Γ ⊢[PRAAx] ap2 fullF s (qd z R B k) ≐ natScale k (ap2 L (logClock p k) x) :=
    GaussianNamedNaturalScale.sample_at L s k k x
  exact (GaussianExponentialReference.add_sample fullF constantF (qd z R B k) e p).eqTrans
    (qadd_congr (r.eqTrans (natScale_at_radius _ _)) (constant_at s e))

private theorem corrected_increment_at (p z h R B k : PTm n) :
    Γ ⊢[PRAAx] qsub (ap2 correctedF p (correctedData (add z h) R B k)) (ap2 correctedF p (correctedData z R B k)) ≐
      qadd (qmul (radiusPoint k one) (qsub (ap2 L (logClock p k) (ld (add z h) (R*B) (B*k)))
        (ap2 L (logClock p k) (ld z (R*B) (B*k))))) (correctionDifference z h B k) := by
  let A := radiusPoint k one
  let u := ap2 L (logClock p k) (ld (add z h) (R*B) (B*k))
  let v := ap2 L (logClock p k) (ld z (R*B) (B*k))
  let a := corr (add z h) B k
  let b := corr z B k
  exact (qsub_congr (corrected_at p (add z h) R B k) (corrected_at p z R B k)).eqTrans
    ((sum_difference (qmul A u) (qmul A v) a b).eqTrans
      (qadd_congr (GaussianRationalRoundedPower.multiplication_difference A u v) (.eqRefl _)))

private theorem relative_finite_error (t z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H) :
    Γ ⊢[PRAAx] distanceBounded (qsub (ap2 L t (ld (add z h) (R*B) (B*k))) (ap2 L t (ld z (R*B) (B*k))))
      (GaussianFiniteLogarithmSampler.sample (numerator z h B k) (denominator z B k)
        (DyadicComplexLogarithm.precision t)) (num 9) (unit t) := by
  let x := ld (add z h) (R*B) (B*k)
  let y := ld z (R*B) (B*k)
  let a := numerator z h B k
  let M := radius H B k
  let E := denominator z B k
  let w := ld a M E
  let u := unit t
  have hu := unit_positive (Γ := Γ) t
  have hD := positive_product _ _ hu hu
  have hx := GaussianLocalLogarithmName.name_regular _ _ _ (local_source (add z h) R B k hs.andE₂.andE₁)
  have hy := GaussianLocalLogarithmName.name_regular _ _ _ (local_source z R B k hs.andE₁)
  have raw := distance_symmetric _ _ _ _ hu (GaussianNamedDifference.sample_error L L x y t hx hy)
  have equivalent := GaussianNameEquivalence.cross_at (DF L L) L (dd x y) w t t (logarithm_increment z h R B k H hs)
  have same : Γ ⊢[PRAAx] distanceBounded (ap2 (DF L L) t (dd x y)) (ap2 L t w) two u :=
    distance_radius_mono _ _ _ _ _ _ hD hu (le_of_eq_add (d := zero) (by ipra_ring)) equivalent
  have hE := (local_admission z h R B k H hs).andE₁
  have rounded := GaussianLocalLogarithmName.point_rounding_distance t a M E hE
  have budget : Γ ⊢[PRAAx] le (num 4*u) (one*DyadicComplexLogarithm.unit t) := by
    have scale := GaussianLocalLogarithmName.unit_factor (Γ := Γ) t
    have grow : Γ ⊢[PRAAx] le (num 4*u) (u*num 16) := le_of_eq_add (d := num 12*u) (by ipra_ring)
    exact le_congr (.eqRefl _) (scale.eqSymm.eqTrans (one_mul _).eqSymm) grow
  have last := distance_radius_mono _ _ _ _ one u (GaussianLocalLogarithmName.unit_positive t) hu budget rounded
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hu (distance_triangle_same _ _ _ _ _ _ hu raw same) last)

private theorem finite_cancellation (p z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H) :
    Γ ⊢[PRAAx] qadd (qmul (radiusPoint k one)
        (GaussianFiniteLogarithmSampler.sample (numerator z h B k) (denominator z B k)
          (DyadicComplexLogarithm.precision (logClock p k)))) (correctionDifference z h B k) ≐
      qadd (linearTerm z h B k) (finiteRemainder p z h B k) := by
  let a := numerator z h B k
  let E := denominator z B k
  let M := DyadicComplexLogarithm.precision (logClock p k)
  let c := GaussianBarnesCanonicalLogRow.cubic a E M
  let b := GaussianBarnesCanonicalCubicName.base a E
  let r := radiusPoint k one
  let C := cubicError z h B k M
  let v := localQuadratic z h B k
  let g := correctionDifference z h B k
  let m := linearTerm z h B k
  let t := quadraticError z h B k
  have e := GaussianBarnesCanonicalCubicName.finite_split a E M (local_admission z h R B k H hs).andE₁
  have split : Γ ⊢[PRAAx] qmul r (GaussianFiniteLogarithmSampler.sample a E M) ≐ qadd C v :=
    (qmul_congr (.eqRefl _) e.eqSymm).eqTrans (qmul_add r c b)
  have swap : Γ ⊢[PRAAx] qadd C (qadd m t) ≐ qadd m (qadd C t) :=
    (qadd_associative C m t).eqSymm.eqTrans
      ((qadd_congr (qadd_commutative C m) (.eqRefl _)).eqTrans (qadd_associative m C t))
  exact (qadd_congr split (.eqRefl _)).eqTrans ((qadd_associative C v g).eqTrans
    ((qadd_congr (.eqRefl _) (cancellation z h R B k H hs)).eqTrans swap))

theorem raw_finite_error (p z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H) :
    Γ ⊢[PRAAx] distanceBounded
      (qsub (ap2 Q p (qd (add z h) R B k)) (ap2 Q p (qd z R B k)))
      (qadd (linearTerm z h B k) (finiteRemainder p z h B k)) (num 6+num 9*k) (unit p) := by
  let t := logClock p k
  let a := radiusPoint k one
  let c := correctionDifference z h B k
  let U := unit p
  let V := unit t
  have hU := unit_positive (Γ := Γ) p
  have hV := unit_positive (Γ := Γ) t
  have first := GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hU
    (distance_symmetric _ _ _ _ hU (GaussianBarnesCanonicalLogFactor.corrected_observation p (add z h) R B k hs.andE₂.andE₁))
    (distance_symmetric _ _ _ _ hU (GaussianBarnesCanonicalLogFactor.corrected_observation p z R B k hs.andE₁))
  have scaled := GaussianNamedDifferenceQuotient.scale_distance a _ _ k (num 9) V hV
    (radius_bounded k one (le_refl one)) (relative_finite_error t z h R B k H hs)
  have later : Γ ⊢[PRAAx] le p t :=
    le_trans (le_add_right p _) (GaussianNamedNaturalScale.clock_later _ k)
  have weak := GaussianExponentialReference.dyadic_weaken _ _ _ p t later scaled
  have near := sum_distance _ _ _ _ _ _ _ hU weak (distance_refl_zero c U hU)
  have tracked := distance_congr (corrected_increment_at p z h R B k).eqSymm
    (finite_cancellation p z h R B k H hs) (add_zero (k*num 9)) (.eqRefl _) near
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hU first tracked)

theorem sample_finite_error (p z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data z h R B k))
      (qadd (linearTerm z h B k) (finiteRemainder p z h B k)) (sampleCost k) (unit p) := by
  have hU := unit_positive (Γ := Γ) p
  have first := GaussianNamedDifference.sample_error Q Q _ _ p
    (GaussianBarnesCanonicalLogFactor.regular (add z h) R B k hs.andE₂.andE₁)
    (GaussianBarnesCanonicalLogFactor.regular z R B k hs.andE₁)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold sampleCost; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hU first (raw_finite_error p z h R B k H hs))

theorem finite_remainder_bound (p z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H)
    (hH : Γ ⊢[PRAAx] le H B) :
    Γ ⊢[PRAAx] bounded (finiteRemainder p z h B k) (boundNumerator R H) (boundDenominator B k) :=
  bound_congr (.eqRefl _) (by unfold boundNumerator; ipra_ring) (.eqRefl _)
    (bounded_sum_same _ _ _ _ _ (denominator_positive z h R B k H hs)
      (finite_cubic_bound z h R B k H _ hs hH) (quadratic_bound z h R B k H hs))

theorem sample_error (p z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H)
    (hH : Γ ⊢[PRAAx] le H B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data z h R B k)) (linearTerm z h B k)
      (boundNumerator R H*unit p+sampleCost k*boundDenominator B k) (boundDenominator B k*unit p) := by
  let a := linearTerm z h B k
  let b := finiteRemainder p z h B k
  let U := unit p
  let D := boundDenominator B k
  have second : Γ ⊢[PRAAx] distanceBounded (qadd a b) a (boundNumerator R H) D :=
    bound_congr (qadd_sub_cancel a b (qadd_canonical _ _)).eqSymm (.eqRefl _) (.eqRefl _)
      (finite_remainder_bound p z h R B k H hs hH)
  have joined := GaussianRationalPanelTailDistance.triangle _ _ _ _ _ _ _ (unit_positive p)
    (denominator_positive z h R B k H hs) (sample_finite_error p z h R B k H hs) second
  exact distance_congr (.eqRefl _) (.eqRefl _) (add_comm _ _) (mul_comm _ _) joined

theorem sample_slack (z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H)
    (hH : Γ ⊢[PRAAx] le H B) :
    Γ ⊢[PRAAx] GaussianNamedConstantRateFromSlack.sampleSlack nameF (data z h R B k) (linearTerm z h B k)
      (boundNumerator R H) (boundDenominator B k) (sampleCost k) := by
  refine .allI ?_
  let sh (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have h' : Δ ⊢[PRAAx] source (sh z) (sh h) (sh R) (sh B) (sh k) (sh H) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hs.shift
  have hH' : Δ ⊢[PRAAx] le (sh H) (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hH.shift
  simpa only [GaussianNamedConstantRateFromSlack.sampleSlack,GaussianRationalSlackRemoval.slack,
    distanceBounded,unit,sh,Syn.shift,subst_data,GaussianBarnesCanonicalDerivativeAlgebra.subst_linearTerm,
    subst_boundNumerator,subst_boundDenominator,subst_sampleCost] using
    sample_error (var 0) (sh z) (sh h) (sh R) (sh B) (sh k) (sh H) h' hH'

theorem independent_rate (z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H)
    (hH : Γ ⊢[PRAAx] le H B) :
    Γ ⊢[PRAAx] independentRate nameF constantF (data z h R B k) (linearTerm z h B k)
      (boundNumerator R H) (boundDenominator B k) :=
  GaussianNamedConstantRateFromSlack.independent_rate nameF (data z h R B k) (linearTerm z h B k)
    (boundNumerator R H) (boundDenominator B k) (sampleCost k)
    (regular z h R B k H hs) (denominator_positive z h R B k H hs) (sample_slack z h R B k H hs hH)

theorem actual_Barnes_named_logarithm_row_first_order_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (let z := var 0
       let h := var 1
       let R := var 2
       let B := var 3
       let k := var 4
       let H := var 5
       source z h R B k H ⋏ le H B ⟶ independentRate nameF constantF (data z h R B k) (linearTerm z h B k)
         (boundNumerator R H) (boundDenominator B k)) :=
  closeUniv 6 (.impI (independent_rate _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDerivativeBinding
