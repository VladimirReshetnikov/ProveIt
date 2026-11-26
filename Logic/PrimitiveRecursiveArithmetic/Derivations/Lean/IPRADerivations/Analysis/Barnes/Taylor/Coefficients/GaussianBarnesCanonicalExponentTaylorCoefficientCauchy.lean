import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalExponentTaylorBuffer
import IPRADerivations.Analysis.Barnes.Prefactors.GaussianBarnesCanonicalPrefactorLipschitz

/-!
# Finite-cutoff convergence of the stored Barnes exponent coefficients

The coefficient at a retained exponent comes from the actual descending
Taylor buffer. Comparing two cutoffs through their common finite sum
pays two reciprocal-index bounds. The frozen prefactor constants add
their own independent observation errors in degrees one and two.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalExponentTaylorCoefficientCauchy

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open GaussianBarnesCanonicalExponentTaylorBuffer
  (buffer entry_at buffer_zero coefficient_one coefficient_two coefficient_high
    linearCoefficient quadraticCoefficient highCoefficient prefactorLinear prefactorQuadratic)
open GaussianBarnesCanonicalHigherRows (previous degree coefficientGain)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogCofinalRate (initial_source)
open GaussianBarnesCanonicalLogSchedule (initial initial_positive)
open GaussianBarnesCanonicalPrefactor
  (negativeHalf quadraticCoefficientF quadraticCoefficientData quadratic_coefficient_regular)
open GaussianBarnesCanonicalPrefactorLipschitz (halfGain)
open GaussianBarnesCanonicalPrefactorExponentDerivative (twicePoint)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianDominantPairAlgebra (radiusPoint radius_bounded)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNameBounds (sample_bound)
open GaussianNameEquivalence (point_at)
open GaussianNameRingLaws (sum_left_error sum_right_error)
open GaussianNamedDifferenceQuotient (scale_distance)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalHorner (ofGaussian qadd qmul qzero positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalPowerDifference (distance_refl_zero)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "S" => GaussianStirlingConstant.nameF
local notation "sd" => GaussianStirlingConstant.nameData
local notation "Q" => quadraticCoefficientF
local notation "qd" => quadraticCoefficientData
local notation "F" => GaussianBarnesCanonicalDerivativeTail.value
local notation "G" => GaussianBarnesCanonicalSecondDerivativeTail.value
local notation "J" => GaussianBarnesCanonicalHigherTail.value
local notation "D₁" => GaussianBarnesCanonicalDerivativeRow.boundNumerator
local notation "D₂" => GaussianBarnesCanonicalSecondDerivativeRow.boundNumerator

def stored (q z R B r M e : PTm n) : PTm n :=
  entry (buffer q z R B r M) (LeanProofs.IPRA.PTm.monus (previous M) e)

def cutoffNumerator (R r s A : PTm n) : PTm n := A*(initial R+s)+A*(initial R+r)
def cutoffDenominator (R r s : PTm n) : PTm n := (initial R+r)*(initial R+s)

def clockNumerator (q t A : PTm n) : PTm n := A*(unit q+unit t)
def clockDenominator (q t : PTm n) : PTm n := unit q*unit t

def gapNumerator (q t R r s A K : PTm n) : PTm n :=
  clockNumerator q t K*cutoffDenominator R r s+cutoffNumerator R r s A*clockDenominator q t
def gapDenominator (q t R r s : PTm n) : PTm n :=
  clockDenominator q t*cutoffDenominator R r s

def linearGain (R : PTm n) : PTm n := one+halfGain*(R+R)

theorem cutoff_positive (R r : PTm n) : Γ ⊢[PRAAx] le one (initial R+r) :=
  le_trans (initial_positive R) (le_add_right _ _)

theorem cutoff_denominator_positive (R r s : PTm n) : Γ ⊢[PRAAx] le one (cutoffDenominator R r s) :=
  positive_product _ _ (cutoff_positive R r) (cutoff_positive R s)

private theorem common_cutoff (x y u v R r s A : PTm n) (e : Γ ⊢[PRAAx] u ≐ v)
    (hx : Γ ⊢[PRAAx] distanceBounded u x A (initial R+r))
    (hy : Γ ⊢[PRAAx] distanceBounded v y A (initial R+s)) :
    Γ ⊢[PRAAx] distanceBounded x y (cutoffNumerator R r s A) (cutoffDenominator R r s) :=
  GaussianRationalPanelTailDistance.triangle x u y A (initial R+r) A (initial R+s)
    (cutoff_positive R r) (cutoff_positive R s)
    (distance_symmetric _ _ _ _ (cutoff_positive R r) hx)
    (distance_congr e.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) hy)

private theorem cutoff_congr (body : PTm 2) (r s x : PTm n) :
    Γ ⊢[PRAAx] GaussianRationalFiniteSum.sum body (r+s) x ≐ GaussianRationalFiniteSum.sum body (s+r) x :=
  GaussianRationalFiniteSum.sum_index_congr body (add_comm r s) (.eqRefl x)

theorem higher_value_gap (z R B j r s : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] distanceBounded (highCoefficient z R B r j) (highCoefficient z R B s j)
      (cutoffNumerator R r s (coefficientGain j)) (cutoffDenominator R r s) := by
  let N := initial R
  have gate := initial_source z R B h
  exact common_cutoff _ _ (J z B N j (r+s)) (J z B N j (s+r)) R r s (coefficientGain j)
    (cutoff_congr GaussianBarnesCanonicalHigherTail.body r s (GaussianBarnesCanonicalHigherTail.data z B N j))
    (GaussianBarnesCanonicalHigherTail.finite_gap z R B N j r s gate)
    (GaussianBarnesCanonicalHigherTail.finite_gap z R B N j s r gate)

theorem higher_entry_gap (q t z R B j r s M L : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hm : Γ ⊢[PRAAx] le (degree j) (previous M)) (hl : Γ ⊢[PRAAx] le (degree j) (previous L)) :
    Γ ⊢[PRAAx] distanceBounded (stored q z R B r M (degree j)) (stored t z R B s L (degree j))
      (cutoffNumerator R r s (coefficientGain j)) (cutoffDenominator R r s) :=
  distance_congr ((entry_at q z R B r M (degree j) hm).eqTrans (coefficient_high q z R B r j)).eqSymm
    ((entry_at t z R B s L (degree j) hl).eqTrans (coefficient_high t z R B s j)).eqSymm
    (.eqRefl _) (.eqRefl _) (higher_value_gap z R B j r s h)

theorem constant_entry_gap (q t z R B r s M L : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (stored q z R B r M zero) (stored t z R B s L zero) zero one :=
  distance_congr ((entry_at q z R B r M zero (zero_le _)).eqTrans
    (GaussianBarnesCanonicalExponentTaylorBuffer.coefficient_zero q z R B r)).eqSymm
    ((entry_at t z R B s L zero (zero_le _)).eqTrans
      (GaussianBarnesCanonicalExponentTaylorBuffer.coefficient_zero t z R B s)).eqSymm
    (.eqRefl _) (.eqRefl _) (distance_refl_zero qzero one (le_refl one))

private theorem first_tail_gap (z R B r s : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] distanceBounded (F z B (initial R) r) (F z B (initial R) s)
      (cutoffNumerator R r s (D₁ R)) (cutoffDenominator R r s) := by
  let N := initial R
  have gate := initial_source z R B h
  exact common_cutoff _ _ (F z B N (r+s)) (F z B N (s+r)) R r s (D₁ R)
    (cutoff_congr GaussianBarnesCanonicalDerivativeTail.body r s (GaussianBarnesCanonicalDerivativeTail.data z B N))
    (GaussianBarnesCanonicalDerivativeTail.finite_gap z R B N r s gate)
    (GaussianBarnesCanonicalDerivativeTail.finite_gap z R B N s r gate)

private theorem second_tail_gap (z R B r s : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] distanceBounded (G z B (initial R) r) (G z B (initial R) s)
      (cutoffNumerator R r s (D₂ R)) (cutoffDenominator R r s) := by
  let N := initial R
  have gate := initial_source z R B h
  exact common_cutoff _ _ (G z B N (r+s)) (G z B N (s+r)) R r s (D₂ R)
    (cutoff_congr GaussianBarnesCanonicalSecondDerivativeTail.body r s (GaussianBarnesCanonicalSecondDerivativeTail.data z B N))
    (GaussianBarnesCanonicalSecondDerivativeTail.finite_gap z R B N r s gate)
    (GaussianBarnesCanonicalSecondDerivativeTail.finite_gap z R B N s r gate)

private theorem prefactor_half_bound : Γ ⊢[PRAAx] bounded (negativeHalf : PTm n) halfGain one :=
  bound_congr (constant_at zero negativeHalf) (.eqRefl _) (.eqRefl _)
    (sample_bound constantF negativeHalf zero (GaussianGammaCanonicalExponent.constant_regular negativeHalf))

private theorem prefactor_linear_gap (q t z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] distanceBounded (prefactorLinear q z B) (prefactorLinear t z B)
      (clockNumerator q t (linearGain R)) (clockDenominator q t) := by
  let D := clockDenominator q t
  let A := unit q+unit t
  let zq := ofGaussian z B
  let c := twicePoint z B
  have dpos : Γ ⊢[PRAAx] le one D := positive_product _ _ (unit_positive q) (unit_positive t)
  have hz := GaussianGammaEulerHead.fraction_disk z R B h.andE₁ h.andE₂
  have hc : Γ ⊢[PRAAx] bounded c (R+R) one :=
    GaussianRationalPowerDifference.bounded_sum_same zq zq R R one (le_refl one) hz hz
  have fs := point_at S (sd zero) q t (GaussianStirlingConstant.name_regular (Γ := Γ) zero)
  have fg := point_at Q qd q t (quadratic_coefficient_regular (Γ := Γ))
  have mul := scale_distance c (ap2 Q q qd) (ap2 Q t qd) (R+R) A D dpos hc fg
  have sum := sum_right_error GaussianRationalSyntheticDivision.qone _ _ _ _ dpos mul
  have pref := scale_distance negativeHalf _ _ halfGain ((R+R)*A) D dpos prefactor_half_bound sum
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold clockNumerator linearGain A; ipra_ring) (.eqRefl _)
    (GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ dpos fs pref)

private theorem combine_clock_and_cutoff (x y u v q t R r s A K : PTm n)
    (hf : Γ ⊢[PRAAx] distanceBounded x y (clockNumerator q t K) (clockDenominator q t))
    (hg : Γ ⊢[PRAAx] distanceBounded u v (cutoffNumerator R r s A) (cutoffDenominator R r s)) :
    Γ ⊢[PRAAx] distanceBounded (qadd x u) (qadd y v) (gapNumerator q t R r s A K) (gapDenominator q t R r s) := by
  have hc : Γ ⊢[PRAAx] le one (clockDenominator q t) :=
    positive_product _ _ (unit_positive q) (unit_positive t)
  have hd := cutoff_denominator_positive (Γ := Γ) R r s
  exact GaussianRationalPanelTailDistance.triangle (qadd x u) (qadd y u) (qadd y v) _ _ _ _ hc hd
    (sum_left_error x y u _ _ hc hf) (sum_right_error y u v _ _ hd hg)

theorem linear_value_gap (q t z R B r s : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] distanceBounded (linearCoefficient q z R B r) (linearCoefficient t z R B s)
      (gapNumerator q t R r s (D₁ R) (linearGain R)) (gapDenominator q t R r s) := by
  have hc : Γ ⊢[PRAAx] le one (clockDenominator q t) :=
    positive_product _ _ (unit_positive q) (unit_positive t)
  have withHead := sum_left_error (prefactorLinear q z B) (prefactorLinear t z B)
    (GaussianBarnesCanonicalHeadCorrectionDerivative.slope z B (initial R)) _ _ hc (prefactor_linear_gap q t z R B h)
  exact combine_clock_and_cutoff _ _ _ _ q t R r s (D₁ R) (linearGain R) withHead (first_tail_gap z R B r s h)

theorem quadratic_value_gap (q t z R B r s : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] distanceBounded (quadraticCoefficient q z R B r) (quadraticCoefficient t z R B s)
      (gapNumerator q t R r s (D₂ R) halfGain) (gapDenominator q t R r s) := by
  let N := initial R
  let D := clockDenominator q t
  let E := cutoffDenominator R r s
  let a := radiusPoint one (two : PTm n)
  have hc : Γ ⊢[PRAAx] le one D := positive_product _ _ (unit_positive q) (unit_positive t)
  have hd : Γ ⊢[PRAAx] le one E := cutoff_denominator_positive R r s
  have hp : Γ ⊢[PRAAx] distanceBounded (prefactorQuadratic q) (prefactorQuadratic t) (clockNumerator q t halfGain) D :=
    scale_distance negativeHalf (ap2 Q q qd) (ap2 Q t qd) halfGain (unit q+unit t) D hc prefactor_half_bound
      (point_at Q qd q t quadratic_coefficient_regular)
  have withHead := sum_left_error (prefactorQuadratic q) (prefactorQuadratic t)
    (qmul a (GaussianGammaCanonicalExponent.harmonicPoint N)) _ _ hc hp
  have fit : Γ ⊢[PRAAx] le (one*one) (one*two) :=
    le_congr (one_mul one).eqSymm (one_mul two).eqSymm (le_succ_self one)
  have half : Γ ⊢[PRAAx] bounded a one one :=
    GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (le_succ_self one) (le_refl one)
      fit (radius_bounded one two (le_succ_self one))
  have raw := scale_distance a (G z B N r) (G z B N s) one (cutoffNumerator R r s (D₂ R)) E hd half (second_tail_gap z R B r s h)
  have scaled := distance_congr (.eqRefl _) (.eqRefl _) (one_mul _) (.eqRefl _) raw
  exact combine_clock_and_cutoff _ _ _ _ q t R r s (D₂ R) halfGain withHead scaled

theorem linear_entry_gap (q t z R B r s M L : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] distanceBounded (stored q z R B r M one) (stored t z R B s L one)
      (gapNumerator q t R r s (D₁ R) (linearGain R)) (gapDenominator q t R r s) :=
  distance_congr ((entry_at q z R B r M one (zero_lt_succ _)).eqTrans (coefficient_one q z R B r)).eqSymm
    ((entry_at t z R B s L one (zero_lt_succ _)).eqTrans (coefficient_one t z R B s)).eqSymm
    (.eqRefl _) (.eqRefl _) (linear_value_gap q t z R B r s h)

theorem quadratic_entry_gap (q t z R B r s M L : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] distanceBounded (stored q z R B r M two) (stored t z R B s L two)
      (gapNumerator q t R r s (D₂ R) halfGain) (gapDenominator q t R r s) :=
  distance_congr ((entry_at q z R B r M two (LeanProofs.IPRA.Common.succ_le_succ (zero_lt_succ M))).eqTrans
    (coefficient_two q z R B r)).eqSymm
    ((entry_at t z R B s L two (LeanProofs.IPRA.Common.succ_le_succ (zero_lt_succ L))).eqTrans
      (coefficient_two t z R B s)).eqSymm
    (.eqRefl _) (.eqRefl _) (quadratic_value_gap q t z R B r s h)

theorem actual_Barnes_retained_higher_exponent_coefficient_gap_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (let q := var 0
     let t := var 1
     let z := var 2
     let R := var 3
     let B := var 4
     let j := var 5
     let r := var 6
     let s := var 7
     let M := var 8
     let L := var 9
     (source z R B ⋏ (le (degree j) (previous M) ⋏ le (degree j) (previous L))) ⟶
       distanceBounded (stored q z R B r M (degree j)) (stored t z R B s L (degree j))
         (cutoffNumerator R r s (coefficientGain j)) (cutoffDenominator R r s)) :=
  closeUniv 10 (.impI (higher_entry_gap _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalExponentTaylorCoefficientCauchy
