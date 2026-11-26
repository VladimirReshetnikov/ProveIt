import IPRADerivations.Analysis.GaussianBarnesCanonicalDerivativeContinuity
import IPRADerivations.Analysis.GaussianBarnesCanonicalTailExponentialDerivative
import IPRADerivations.Analysis.GaussianBarnesCanonicalTailContinuity
import IPRADerivations.Analysis.GaussianNamedBoundedProductObservation

/-!
# Uniform disk continuity of the original Barnes tail exponential derivative

The original derivative multiplies the cofinal tail exponential by
the cofinal logarithmic derivative. A common input precision pays the
two distinct moduli and an explicit uniform product bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTailExponentialDerivativeContinuity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalDerivativeRow (boundNumerator)
open GaussianBarnesCanonicalTailExponentialDerivative (derivativeF derivativeData)
open GaussianBarnesCanonicalFiniteLog (radius)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerNamedPowerScalingPowerFrozen (multiply_same_denominator unit_rate_after)
open GaussianFastValueCut (exponent)
open GaussianNamedDifferenceRate (rate_parameters_congr)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianRadiusExponentialLipschitzRate (factor)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (ofGaussian)
open GaussianRationalMetric (distanceBounded)
open GaussianExponentialReference (unit_monotone)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "T" => GaussianBarnesCanonicalTailExponential.nameF
local notation "td" => GaussianBarnesCanonicalTailExponential.data
local notation "L" => GaussianBarnesCanonicalDerivativeCofinal.nameF
local notation "ld" => GaussianBarnesCanonicalLogCofinal.data
local notation "Lgain" => GaussianBarnesCanonicalDerivativeContinuity.gain
local notation "tailClock" => GaussianBarnesCanonicalTailContinuity.inputClock

def sampleGain (R : PTm n) : PTm n := factor (radius R)*boundNumerator R
def productClock (R p : PTm n) : PTm n := exponent (boundNumerator R+factor (radius R)) p
def inputClock (R p : PTm n) : PTm n :=
  tailClock R (productClock R p)+exponent (Lgain R) (productClock R p)

@[simp] theorem subst_sampleGain {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (sampleGain R) = sampleGain (Syn.subst σ R) := by simp [sampleGain]

@[simp] theorem subst_productClock {m : ℕ} (σ : Fin n → PTm m) (R p : PTm n) :
    Syn.subst σ (productClock R p) = productClock (Syn.subst σ R) (Syn.subst σ p) := by simp [productClock]

@[simp] theorem subst_inputClock {m : ℕ} (σ : Fin n → PTm m) (R p : PTm n) :
    Syn.subst σ (inputClock R p) = inputClock (Syn.subst σ R) (Syn.subst σ p) := by simp [inputClock]

theorem samples (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] sampleBound derivativeF (derivativeData z R B) (sampleGain R) :=
  GaussianNamedBoundedProductObservation.sample_bounds T L (td z R B) (ld z R B) _ _
    (GaussianBarnesCanonicalTailContinuity.sample_bound z R B h) (GaussianBarnesCanonicalDerivativeContinuity.samples z R B h)

theorem uniform_input (z w R B D p : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source w R D)
    (h : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) one (unit (inputClock R p))) :
    Γ ⊢[PRAAx] independentRate derivativeF derivativeF (derivativeData z R B) (derivativeData w R D) one (unit p) := by
  let q := productClock R p
  let k := inputClock R p
  let a := tailClock R q
  let b := exponent (Lgain R) q
  let M := boundNumerator R
  let S := factor (radius R)
  let x := td z R B
  let y := td w R D
  let l := ld z R B
  let r := ld w R D
  have hk := unit_positive (Γ := Γ) k
  have hq := unit_positive (Γ := Γ) q
  have ha : Γ ⊢[PRAAx] le a k := le_add_right _ _
  have hb : Γ ⊢[PRAAx] le b k := le_add_left _ _
  have ha' : Γ ⊢[PRAAx] le (one*unit a) (one*unit k) := le_congr (one_mul _).eqSymm (one_mul _).eqSymm (unit_monotone ha)
  have ht := GaussianBarnesCanonicalTailContinuity.uniform_input z w R B D q hz hw
    (distance_radius_mono _ _ _ _ _ _ hk (unit_positive a) ha' h)
  have raw := GaussianBarnesCanonicalDerivativeContinuity.rate z w R B D one (unit k) hz hw hk h
  have raw' : Γ ⊢[PRAAx] independentRate L L l r (Lgain R) (unit k) :=
    rate_parameters_congr _ _ _ _ _ _ _ _ (by ipra_ring) (.eqRefl _) raw
  have hl := unit_rate_after L L l r (Lgain R) k q hb raw'
  have joined := multiply_same_denominator T L T L x l y r one one (unit q) M S hq
    (GaussianBarnesCanonicalTailExponential.regular z R B hz)
    (GaussianBarnesCanonicalDerivativeCofinal.regular z R B hz)
    (GaussianBarnesCanonicalTailExponential.regular w R D hw)
    (GaussianBarnesCanonicalDerivativeCofinal.regular w R D hw)
    (GaussianBarnesCanonicalDerivativeContinuity.samples z R B hz)
    (GaussianBarnesCanonicalTailContinuity.sample_bound w R D hw) ht hl
  have paid : Γ ⊢[PRAAx] independentRate derivativeF derivativeF (derivativeData z R B) (derivativeData w R D) (M+S) (unit q) :=
    rate_parameters_congr _ _ _ _ _ _ _ _ (by ipra_ring) (.eqRefl _) joined
  exact unit_rate_after derivativeF derivativeF (derivativeData z R B) (derivativeData w R D) (M+S) q p (le_refl _) paid

theorem actual_Barnes_tail_exponential_derivative_uniform_disk_continuity_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (let z := var 0
       let w := var 1
       let R := var 2
       let B := var 3
       let D := var 4
       let p := var 5
       (source z R B ⋏ source w R D) ⟶
         distanceBounded (ofGaussian z B) (ofGaussian w D) one (unit (inputClock R p)) ⟶
           independentRate derivativeF derivativeF (derivativeData z R B) (derivativeData w R D) one (unit p)) :=
  closeUniv 6 (.impI (.impI (uniform_input _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTailExponentialDerivativeContinuity
