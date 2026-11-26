import IPRADerivations.Analysis.Barnes.Deflation.GaussianBarnesCanonicalDeflatedValue
import IPRADerivations.Analysis.Barnes.HeadProducts.GaussianBarnesCanonicalHeadLipschitz
import IPRADerivations.Analysis.Names.GaussianNamedBoundedProductObservation

/-!
# Disk Lipschitz bounds for the original deflated Barnes head

The multiplier has a fixed inverse integer power and the original
quadratic exponential. Apply the two exact finite range bounds to the
skipped head and combine them at the actual product names.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDeflatedHeadLipschitz

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalFactor (source exponentRadius correction exponentialF exponentialData)
open GaussianBarnesCanonicalDeflatedFactor (inversePower inverseInteger)
open GaussianBarnesCanonicalDeflatedValue (headCoefficientF headCoefficientData head_coefficient_regular)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianCyclicExponentialSamples (exponential_bound)
open GaussianEulerNamedPowerScalingPowerFrozen (constant_bound multiply_same_denominator)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedBoundedProductObservation (sample_bounds)
open GaussianNameArithmetic (multiply_fast)
open GaussianRationalHorner (ofGaussian ofGaussian_represents positive_product)
open GaussianRationalMetric (distanceBounded bounded bounded_of_cleared)
open GaussianRationalReciprocal (bound_congr)
open GaussianRadiusExponentialLipschitzRate (factor)
open ComplexLogarithmRemainder (oneCode normSq_one)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (pred)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "H" => GaussianBarnesCanonicalHead.nameF
local notation "Hd" => GaussianBarnesCanonicalHead.data
local notation "Hcap" => GaussianBarnesCanonicalHead.cap
local notation "Hgain" => GaussianBarnesCanonicalHeadLipschitz.gain
local notation "U" => GaussianBarnesCanonicalDeflatedFactor.nameF
local notation "Ud" => GaussianBarnesCanonicalDeflatedFactor.data
local notation "S" => GaussianBarnesCanonicalDeflatedHead.nameF
local notation "Sd" => GaussianBarnesCanonicalDeflatedHead.data

def multiplierCap (R : PTm n) : PTm n := one*factor (exponentRadius R)
def multiplierGain (R : PTm n) : PTm n := factor (exponentRadius R)*(two*R+one)
def skippedCap (R m r : PTm n) : PTm n := Hcap R zero (pred m)*Hcap R m r
def skippedGain (R m r : PTm n) : PTm n :=
  Hcap R m r*Hgain R zero (pred m)+Hcap R zero (pred m)*Hgain R m r
def cap (R m r : PTm n) : PTm n := multiplierCap R*skippedCap R m r
def gain (R m r : PTm n) : PTm n := skippedCap R m r*multiplierGain R+multiplierCap R*skippedGain R m r

@[simp] theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) (R k r : PTm n) :
    Syn.subst σ (gain R k r) = gain (Syn.subst σ R) (Syn.subst σ k) (Syn.subst σ r) := by
  simp [gain,skippedCap,skippedGain,multiplierCap,multiplierGain,exponentRadius,one,two]

private theorem inverse_power_bound (m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] bounded (inversePower m) one one := by
  have e : Γ ⊢[PRAAx] (one*one)*ComplexLogarithmRemainder.normSq (oneCode : PTm n) ≐ one :=
    (congrMul (.eqRefl _) normSq_one).eqTrans (by ipra_ring)
  have b : Γ ⊢[PRAAx] bounded (inverseInteger m) one one :=
    bounded_of_cleared _ _ _ _ _ hm (le_refl one) (ofGaussian_represents oneCode m hm)
      (le_congr e.eqSymm (by ipra_ring) (positive_product m m hm hm))
  exact bound_congr (.eqRefl _) (GaussianPolynomialPerturbation.one_power m) (.eqRefl _)
    (GaussianRationalPowerDifference.bounded_power_integer (inverseInteger m) one m b)

private theorem exponent_bounds (z R B m : PTm n) (h : Γ ⊢[PRAAx] source z R B m) :
    Γ ⊢[PRAAx] sampleBound exponentialF (exponentialData z R B m) (factor (exponentRadius R)) := by
  refine .allI ?_
  let s (a : PTm n) := Syn.shift a
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (s z) (s R) (s B) (s m) := by
    simpa [Fm.shift,Syn.shift,s] using h.shift
  have b := exponential_bound constantF (exponentRadius (s R)) (correction (s z) (s B) (s m)) (var 0)
    (GaussianBarnesCanonicalFactor.exponential_input (s z) (s R) (s B) (s m) hs)
  simpa only [sampleBound,GaussianBarnesCanonicalFactor.subst_exponentialData,GaussianRadiusExponentialLipschitzRate.subst_factor,
    GaussianBarnesCanonicalFactor.exponentialData,GaussianCyclicExponentialSamples.sampleBound,factor,
    GaussianRadiusExponentialName.subst_data,GaussianBarnesCanonicalFactor.subst_correction,subst_ap2,PTm.subst_num,
    exponentRadius,PTm.subst_add,PTm.subst_mul,Syn.shift,s] using b

private theorem multiplier_bound (z R B m : PTm n) (h : Γ ⊢[PRAAx] source z R B m) :
    Γ ⊢[PRAAx] sampleBound U (Ud z R B m) (multiplierCap R) :=
  sample_bounds constantF exponentialF (inversePower m) (exponentialData z R B m) one (factor (exponentRadius R))
    (constant_bound (inversePower m) one (inverse_power_bound m h.andE₂.andE₁)) (exponent_bounds z R B m h)

private theorem multiplier_rate (z w R B D m A N : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B m) (hw : Γ ⊢[PRAAx] source w R D m) (hN : Γ ⊢[PRAAx] le one N)
    (h : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) A N) :
    Γ ⊢[PRAAx] independentRate U U (Ud z R B m) (Ud w R D m) (multiplierGain R*A) N := by
  let x := inversePower m
  let a := correction z B m
  let b := correction w D m
  let E := exponentRadius R
  let C := factor E
  let K := (two*R+one)*A
  have hzE := GaussianBarnesCanonicalFactor.exponential_input z R B m hz
  have hwE := GaussianBarnesCanonicalFactor.exponential_input w R D m hw
  have err := GaussianBarnesCanonicalFactorLipschitz.correction_distance z w R B D m A N hz hw hN h
  have hconst := GaussianNamedAddRate.constant_rate a b K N hN err
  have re := GaussianRadiusExponentialLipschitzRate.independent_rate constantF constantF E a b K N
    (.andI hN (.andI hzE (.andI hwE hconst)))
  have hx : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN constantF x := constant_regular x
  have mul := multiply_same_denominator constantF exponentialF constantF exponentialF x (exponentialData z R B m)
    x (exponentialData w R D m) zero (C*K) N C one hN hx (GaussianRadiusExponentialName.name_regular _ _ _ hzE)
    hx (GaussianRadiusExponentialName.name_regular _ _ _ hwE) (exponent_bounds z R B m hz)
    (constant_bound x one (inverse_power_bound m hz.andE₂.andE₁))
    (GaussianNamedAddRate.constant_rate x x zero N hN (GaussianRationalPowerDifference.distance_refl_zero x N hN)) re
  exact GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _
    (by unfold multiplierGain C K E; ipra_ring) (.eqRefl _) mul

private theorem range_bound (z R B N r : PTm n) (h : Γ ⊢[PRAAx] GaussianBarnesCanonicalHead.source z R B) :
    Γ ⊢[PRAAx] sampleBound H (Hd z R B N r) (Hcap R N r) := by
  refine .allI ?_
  let s (a : PTm n) := Syn.shift a
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianBarnesCanonicalHead.source (s z) (s R) (s B) := by
    simpa [Fm.shift,Syn.shift,s] using h.shift
  simpa only [sampleBound,Syn.shift,s,GaussianBarnesCanonicalHead.subst_data,GaussianBarnesCanonicalHead.subst_cap] using
    GaussianBarnesCanonicalHead.sample_bound (var 0) (s z) (s R) (s B) (s N) (s r) hs

private theorem skipped_bound (z R B m r : PTm n) (h : Γ ⊢[PRAAx] source z R B m) :
    Γ ⊢[PRAAx] sampleBound S (Sd z R B m r) (skippedCap R m r) := by
  have d : Γ ⊢[PRAAx] GaussianBarnesCanonicalHead.source z R B := .andI h.andE₁ h.andE₂.andE₂
  exact sample_bounds H H _ _ _ _ (range_bound z R B zero (pred m) d) (range_bound z R B m r d)

private theorem skipped_rate (z w R B D m r A N : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B m) (hw : Γ ⊢[PRAAx] source w R D m) (hN : Γ ⊢[PRAAx] le one N)
    (h : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) A N) :
    Γ ⊢[PRAAx] independentRate S S (Sd z R B m r) (Sd w R D m r) (skippedGain R m r*A) N := by
  have dz : Γ ⊢[PRAAx] GaussianBarnesCanonicalHead.source z R B := .andI hz.andE₁ hz.andE₂.andE₂
  have dw : Γ ⊢[PRAAx] GaussianBarnesCanonicalHead.source w R D := .andI hw.andE₁ hw.andE₂.andE₂
  have left := GaussianBarnesCanonicalHeadLipschitz.independent_rate z w R B D zero (pred m) A N dz dw hN h
  have right := GaussianBarnesCanonicalHeadLipschitz.independent_rate z w R B D m r A N dz dw hN h
  have mul := multiply_same_denominator H H H H (Hd z R B zero (pred m)) (Hd z R B m r)
    (Hd w R D zero (pred m)) (Hd w R D m r) _ _ N (Hcap R m r) (Hcap R zero (pred m)) hN
    (GaussianBarnesCanonicalHead.regular z R B zero (pred m) dz) (GaussianBarnesCanonicalHead.regular z R B m r dz)
    (GaussianBarnesCanonicalHead.regular w R D zero (pred m) dw) (GaussianBarnesCanonicalHead.regular w R D m r dw)
    (range_bound z R B m r dz) (range_bound w R D zero (pred m) dw) left right
  exact GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _ (by unfold skippedGain; ipra_ring) (.eqRefl _) mul

theorem sample_bound (z R B m r : PTm n) (h : Γ ⊢[PRAAx] source z R B m) :
    Γ ⊢[PRAAx] sampleBound headCoefficientF (headCoefficientData z R B m r) (cap R m r) :=
  sample_bounds U S _ _ _ _ (multiplier_bound z R B m h) (skipped_bound z R B m r h)

theorem independent_rate (z w R B D m r A N : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B m) (hw : Γ ⊢[PRAAx] source w R D m) (hN : Γ ⊢[PRAAx] le one N)
    (h : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) A N) :
    Γ ⊢[PRAAx] independentRate headCoefficientF headCoefficientF
      (headCoefficientData z R B m r) (headCoefficientData w R D m r) (gain R m r*A) N := by
  have hmult := multiplier_rate z w R B D m A N hz hw hN h
  have hskip := skipped_rate z w R B D m r A N hz hw hN h
  have raw := multiply_same_denominator U S U S (Ud z R B m) (Sd z R B m r) (Ud w R D m) (Sd w R D m r)
    _ _ N (skippedCap R m r) (multiplierCap R) hN
    (GaussianBarnesCanonicalDeflatedFactor.regular z R B m hz) (GaussianBarnesCanonicalDeflatedHead.regular z R B m r hz)
    (GaussianBarnesCanonicalDeflatedFactor.regular w R D m hw) (GaussianBarnesCanonicalDeflatedHead.regular w R D m r hw)
    (skipped_bound z R B m r hz) (multiplier_bound w R D m hw) hmult hskip
  exact GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _ (by unfold gain; ipra_ring) (.eqRefl _) raw

theorem actual_Barnes_deflated_head_disk_lipschitz_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (let z := var 0
     let w := var 1
     let R := var 2
     let B := var 3
     let D := var 4
     let m := var 5
     let r := var 6
     let A := var 7
     let N := var 8
     (source z R B m ⋏ (source w R D m ⋏ le one N)) ⟶
       distanceBounded (ofGaussian z B) (ofGaussian w D) A N ⟶
       independentRate headCoefficientF headCoefficientF (headCoefficientData z R B m r)
         (headCoefficientData w R D m r) (gain R m r*A) N) :=
  closeUniv 9 (.impI (.impI (independent_rate _ _ _ _ _ _ _ _ _
    Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDeflatedHeadLipschitz
