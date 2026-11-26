import IPRADerivations.Analysis.Gamma.Zeta.GaussianGammaZetaMellinGeometric
import IPRADerivations.Analysis.Euler.Integration.GaussianEulerIncompleteFactorialDenominator
import IPRADerivations.Analysis.Exponential.GaussianExponentialInverseSamples
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedProductObservationBound

/-!
# Original Euler decay rows of the Gamma–zeta geometric prefix

Each exact power of the ratio at the Mellin reciprocal clock agrees
to explicit precision with the original exponential at the corresponding
negative integer multiple of the rational time.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinDecayRows

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBoundedIntegerExponentialStages (scaledF stageData radius)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianDominantPairAlgebra (radiusPoint)
open GaussianEulerIntegrandName (decayF decayData decayPoint)
open GaussianExponentialInverseSamples (height negative negativeRadius negative_power)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaZetaMellinGeometric (ratio prefix_term)
open GaussianGammaZetaMellinIntegrand (exponentialF exponentialData denominatorClock reciprocalClock)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_to_diagonal diagonal_at)
open GaussianNameRingLaws (negativeF negativeData negative_equivalent)
open GaussianRationalDistanceOrder (distance_symmetric distance_triangle_same)
open GaussianRationalLowerBounds (lower lower_congr inverse_bound)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalPolynomialExponential (scalarSum scalarBody)
open GaussianRationalReciprocal (power reciprocal)
open GaussianRationalNaturalScale (natScale_congr)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Input" => GaussianRadiusExponentialName.input
local notation "Exp" => GaussianRadiusExponentialName.nameF
local notation "expData" => GaussianRadiusExponentialName.data
local notation "Scale" => scaledF constantF

def clock (p b : PTm n) : PTm n := denominatorClock (reciprocalClock p b)
def baseRadius (a b : PTm n) : PTm n := GaussianNameBounds.U constantF (radiusPoint a b)

def rowCost (E i a b : PTm n) : PTm n :=
  two+negativeRadius constantF E i (baseRadius a b) (radiusPoint a b)+i*two

@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (p b : PTm n) :
    Syn.subst σ (clock p b) = clock (Syn.subst σ p) (Syn.subst σ b) := by
  simp [clock,denominatorClock,reciprocalClock,two,one]

@[simp] theorem subst_baseRadius {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (baseRadius a b) = baseRadius (Syn.subst σ a) (Syn.subst σ b) := by simp [baseRadius]

@[simp] theorem subst_rowCost {m : ℕ} (σ : Fin n → PTm m) (E i a b : PTm n) :
    Syn.subst σ (rowCost E i a b) =
      rowCost (Syn.subst σ E) (Syn.subst σ i) (Syn.subst σ a) (Syn.subst σ b) := by simp [rowCost,two,one]

private theorem base_input (a b : PTm n) : Γ ⊢[PRAAx] Input constantF (baseRadius a b) (radiusPoint a b) :=
  GaussianGammaFiniteApproximantName.exponential_input constantF _ (constant_regular _)

theorem scaled_at (p E i a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] ap2 Scale p (stageData E i (radiusPoint a b)) ≐ radiusPoint (i*a) b := by
  let k := GaussianNamedNaturalScale.clock p E
  exact (GaussianNamedNaturalScale.sample_at constantF p E i (radiusPoint a b)).eqTrans
    ((natScale_congr (.eqRefl i) (constant_at k (radiusPoint a b))).eqTrans
      (GaussianEulerIncompleteFactorialDenominator.scaled_radius i a b hb))

private theorem scaled_cross (E i a b : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hi : Γ ⊢[PRAAx] le i E) :
    Γ ⊢[PRAAx] crossEquivalent Scale constantF (stageData E i (radiusPoint a b)) (radiusPoint (i*a) b) := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _
    (GaussianNamedNaturalScale.name_regular constantF E i (baseRadius a b) (radiusPoint a b) (base_input a b) hi)
    (constant_regular (radiusPoint (i*a) b))
  refine .allI ?_
  let s (x : PTm n) := Syn.shift x
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (s b) := by simpa [Fm.shift,Syn.shift,s] using hb.shift
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,s,scaledF,stageData,
    GaussianNamedNaturalScale.subst_data,GaussianDominantPairAlgebra.subst_radiusPoint,
    PTm.subst_mul] using (scaled_at (var 0) (s E) (s i) (s a) (s b) bs).eqTrans
      (constant_at (var 0) (radiusPoint (s i*s a) (s b))).eqSymm

theorem signed_stage (E i a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hi : Γ ⊢[PRAAx] le i E) :
    Γ ⊢[PRAAx] crossEquivalent (Exp (negativeF Scale)) decayF
      (expData (radius E (baseRadius a b)) (negativeData (stageData E i (radiusPoint a b)))) (decayData (i*a) b) := by
  let x := stageData E i (radiusPoint a b)
  let y := radiusPoint (i*a) b
  let v := decayPoint (i*a) b
  let R := radius E (baseRadius a b)
  have hs := GaussianNamedNaturalScale.exponential_input constantF E i (baseRadius a b) (radiusPoint a b)
    (base_input a b) hi
  have ht := GaussianGammaFiniteApproximantName.exponential_input constantF v (constant_regular (Γ := Γ) v)
  have neg := negative_equivalent Scale constantF x y hs.andE₁ (constant_regular y)
    (cross_to_diagonal _ _ _ _ (scaled_cross E i a b hb hi))
  have e := cross_trans (negativeF Scale) (negativeF constantF) constantF (negativeData x) (negativeData y) v
    neg (GaussianEulerDecayFactorBounds.negative_constant_cross (i*a) b hb)
  exact GaussianExponentialRadiusIndependence.independent_radii_proper (negativeF Scale) constantF
    R (GaussianNameBounds.U constantF v) (negativeData x) v
    (GaussianExponentialInverse.negative_input Scale R x hs) ht e

private theorem exponential_unit_lower (p a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] lower (ap2 exponentialF p (exponentialData a b)) one one := by
  let t := radiusPoint a b
  let R := baseRadius a b
  let k := GaussianRadiusExponentialName.index R p
  let u := GaussianRadiusExponentialName.inputPrecision R p
  have read : Γ ⊢[PRAAx] ap2 exponentialF p (exponentialData a b) ≐ scalarSum t k :=
    (GaussianRadiusExponentialName.sample_at constantF R p t).eqTrans
      (GaussianRationalFiniteSum.sum_index_congr scalarBody (.eqRefl _) (constant_at u t))
  have obs := GaussianPositiveExponentialTermBound.original_monomial_lower a b zero k hb (zero_le k)
  exact lower_congr read.eqSymm (pw_zero a)
    ((congrMul (fact_zero zero) (pw_zero b)).eqTrans (one_mul one)) obs

private theorem inverse_unit_bound (p a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] GaussianRationalMetric.bounded (reciprocal (ap2 exponentialF p (exponentialData a b))) one one :=
  inverse_bound _ _ _ (le_refl one) (le_refl one) (exponential_unit_lower p a b hb)

theorem inverse_clock_error (p a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] distanceBounded (negative constantF (clock p b) (baseRadius a b) (radiusPoint a b))
      (ratio p a b) two (unit (clock p b)) := by
  let t := radiusPoint a b
  let R := baseRadius a b
  let r := clock p b
  let s := r+GaussianNameReciprocal.anchor (height constantF R t)
  let x := ap2 exponentialF s (exponentialData a b)
  let y := ap2 exponentialF r (exponentialData a b)
  have reg := GaussianRadiusExponentialName.name_regular constantF R t (base_input (Γ := Γ) a b)
  have h (j : PTm n) : Γ ⊢[PRAAx] GaussianNameReciprocal.lower (ap2 exponentialF j (exponentialData a b)) one :=
    GaussianRationalLowerBounds.name_lower _ _ _ (le_refl one) (le_refl one) (exponential_unit_lower j a b hb)
  have d := GaussianNamedProductObservationBound.late_observation exponentialF (exponentialData a b) r s reg
    (le_add_right _ _)
  have raw := GaussianNameReciprocal.inverse_distance_two x y one one two (unit r) (le_refl one) (le_refl one)
    (unit_positive r) (h s) (h r) d
  exact GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) raw

theorem row_error (p E i a b : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hi : Γ ⊢[PRAAx] le i E) (hE : Γ ⊢[PRAAx] le one E) :
    Γ ⊢[PRAAx] distanceBounded (ap2 decayF (clock p b) (decayData (i*a) b))
      (power (ratio p a b) i) (rowCost E i a b) (unit (clock p b)) := by
  let r := clock p b
  let t := radiusPoint a b
  let R := baseRadius a b
  let s := r+GaussianNameReciprocal.anchor (height constantF R t)
  let x := negative constantF r R t
  let y := ratio p a b
  have step := signed_stage E i a b hb hi
  have first := diagonal_at _ _ _ _ r (cross_to_diagonal _ _ _ _ step)
  have center := negative_power constantF r E i R t (base_input a b) hi hE
  have last := GaussianRationalPowerDifference.unit_disk_power_difference x y two (unit r) i
    (unit_positive r) (inverse_unit_bound s a b hb) (inverse_unit_bound r a b hb) (inverse_clock_error p a b hb)
  exact distance_triangle_same _ _ _ _ _ _ (unit_positive r)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive r)
      (distance_symmetric _ _ _ _ (unit_positive r) first) center) last

theorem prefix_row_error (p E j a b : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hj : Γ ⊢[PRAAx] le (succ j) E) (hE : Γ ⊢[PRAAx] le one E) :
    Γ ⊢[PRAAx] distanceBounded (ap2 decayF (clock p b) (decayData (succ j*a) b))
      (inst2 GaussianRationalInverseGeometric.body j (ratio p a b)) (rowCost E (succ j) a b) (unit (clock p b)) := by
  rw [prefix_term]
  exact row_error p E (succ j) a b hb hj hE

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinDecayRows
