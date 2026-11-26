import IPRADerivations.Analysis.Barnes.HeadProducts.GaussianBarnesCanonicalDyadicHeadCorrection
import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalCentralUniformBound
import IPRADerivations.Analysis.Exponential.GaussianNamedExponentialTaylorTransport

/-!
# Dyadic growth bound for the original Barnes central scalar

Keep the tail denominator at the actual initial index and use the
harmonic bound for the exact finite head correction. The resulting
quadratic radius bounds observations of the original central exponential.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDyadicCentralBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalCenteredExponentialShift (baseData)
open GaussianBarnesCanonicalCorrectionShift (total)
open GaussianBarnesCanonicalDiskBound (prefactorRadius radius_le)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogCofinalRate (cofinal_clock_budget initial_source)
open GaussianBarnesCanonicalLogRow (boundNumerator)
open GaussianBarnesCanonicalLogSchedule (initial initial_positive initial_radius length)
open GaussianBarnesCanonicalLogTail (tailDenominator tail_denominator_positive)
open GaussianBarnesCanonicalSingleExponential (exponentF exponentData exponent_regular prefixF prefixData prefactorExponentData)
open GaussianCoefficientNameBounds (bounded_radius_mono unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianGammaFiniteApproximantName (exponentialInputData exponential_input)
open GaussianNameBounds (U)
open GaussianNamedMultiplyRate (sampleBound sample_bound_at)
open GaussianRadiusExponentialLipschitzRate (factor)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "E" => GaussianRadiusExponentialName.nameF
local notation "P" => GaussianBarnesCanonicalPrefactorInverse.exponentF
local notation "L" => GaussianBarnesCanonicalLogCofinal.nameF
local notation "ld" => GaussianBarnesCanonicalLogCofinal.data
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def tailCap (R : PTm n) : PTm n := one+R*R

def prefixArgumentCap (R j : PTm n) : PTm n :=
  (prefactorRadius R+prefactorRadius R)+GaussianBarnesCanonicalDyadicHeadCorrection.radius R (initial R) j

def centralArgumentCap (R j : PTm n) : PTm n := prefixArgumentCap R j+tailCap R

def centralExponent (R j : PTm n) : PTm n := two*centralArgumentCap R j+two

def centralCap (R j : PTm n) : PTm n := factor (centralExponent R j)

theorem tail_observation (p z R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] bounded (ap2 L p (ld z R B)) (tailCap R) one := by
  let N := initial R
  let r := length p R
  let v := GaussianBarnesCanonicalLogSchedule.clock p R
  let K := GaussianBarnesCanonicalFiniteLog.gain N r
  let D := tailDenominator N
  let x := GaussianBarnesCanonicalLogRoundedTail.value v z R B N r
  let y := GaussianBarnesCanonicalLogTail.value z B N r (DyadicComplexLogarithm.precision v)
  have domain := initial_source z R B hz
  have hD : Γ ⊢[PRAAx] le one D := tail_denominator_positive N (initial_positive R)
  have wide : Γ ⊢[PRAAx] le (boundNumerator R*one) ((R*R)*D) := by
    have margin := initial_radius (Γ := Γ) R
    ipra_le 𝔞(R)*𝔞(R)*sl margin+2*𝔞(R)*𝔞(R)*𝔞(N) using
      dsimp only [D,tailDenominator,boundNumerator]
      ipra_simps
      ring
  have exactSum : Γ ⊢[PRAAx] bounded y (R*R) one :=
    bounded_radius_mono _ _ _ _ _ hD (le_refl one) wide
      (GaussianBarnesCanonicalLogTail.tail_bound z R B N r _ domain)
  have more : Γ ⊢[PRAAx] le K (K*unit p) :=
    le_congr (one_mul K) (mul_comm _ _) (mul_le_mul_right K (unit_positive p))
  have paid := le_trans (GaussianBarnesCanonicalFiniteLog.rounding_gain (Γ := Γ) N r)
    (le_trans more (cofinal_clock_budget p R v (le_refl _)))
  have rounding : Γ ⊢[PRAAx] distanceBounded x y one one :=
    distance_radius_mono _ _ _ _ _ _ (GaussianLocalLogarithmName.unit_positive v) (le_refl one)
      (le_congr (by ipra_ring) (by ipra_ring) paid)
      (GaussianBarnesCanonicalLogRoundedTail.rounding_error v z R B N r domain)
  exact bound_congr (GaussianBarnesCanonicalLogCofinal.sample_at p z R B).eqSymm
    (by dsimp only [tailCap]; ipra_ring) (one_mul one)
    (GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ (le_refl one) (le_refl one) rounding exactSum)

theorem tail_samples (z R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] sampleBound L (ld z R B) (tailCap R) := by
  refine .allI ?_
  let sh (x : PTm n) := Syn.shift x
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) :=
    by simpa [Fm.shift,sh,Syn.shift] using hz.shift
  simpa [sampleBound,tailCap,sh,Syn.shift,one] using tail_observation (var 0) (sh z) (sh R) (sh B) hs

private theorem constant_samples (x A : PTm n) (h : Γ ⊢[PRAAx] bounded x A one) :
    Γ ⊢[PRAAx] sampleBound constantF x A := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift x) (Syn.shift A) one := by
    simpa [Fm.shift,Syn.shift,one] using h.shift
  simpa only [sampleBound,Syn.shift] using bound_congr (constant_at (var 0) (Syn.shift x)).eqSymm (.eqRefl _) (.eqRefl _) hs

private theorem widen_samples (f : PR 2) (x A C : PTm n)
    (hA : Γ ⊢[PRAAx] le A C) (h : Γ ⊢[PRAAx] sampleBound f x A) : Γ ⊢[PRAAx] sampleBound f x C := by
  refine .allI ?_
  let sh (v : PTm n) := Syn.shift v
  have hs : Γ.map Fm.shift ⊢[PRAAx] sampleBound f (sh x) (sh A) :=
    by simpa [Fm.shift,sh,Syn.shift] using h.shift
  have hAs : Γ.map Fm.shift ⊢[PRAAx] le (sh A) (sh C) := by simpa [Fm.shift,sh,Syn.shift] using hA.shift
  simpa only [sampleBound,sh,Syn.shift] using
    bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one) (mul_le_mul_right one hAs)
      (sample_bound_at f (sh x) (sh A) (var 0) hs)

theorem prefix_argument_samples (z R B j : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hj : Γ ⊢[PRAAx] le (initial R) (pw two j)) :
    Γ ⊢[PRAAx] sampleBound prefixF (prefixData z R B) (prefixArgumentCap R j) := by
  have prefactor := GaussianBarnesCanonicalPrefactorInverse.exponent_input (Γ := Γ) z B
  have size := radius_le z R B hz
  have hp := widen_samples P (prefactorExponentData z B) (GaussianBarnesCanonicalPrefactorInverse.exponentRadius z B)
    (prefactorRadius R+prefactorRadius R) (add_le_add₂ size size) prefactor.andE₂
  have hc := constant_samples _ _ (GaussianBarnesCanonicalDyadicHeadCorrection.correction_bound z R B (initial R) j hz hj)
  exact GaussianNamedBoundedSumObservation.sample_bounds P constantF (prefactorExponentData z B) (total z B (initial R))
    _ _ hp hc

theorem central_argument_samples (z R B j : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hj : Γ ⊢[PRAAx] le (initial R) (pw two j)) :
    Γ ⊢[PRAAx] sampleBound exponentF (exponentData z R B) (centralArgumentCap R j) :=
  GaussianNamedBoundedSumObservation.sample_bounds prefixF L (prefixData z R B) (ld z R B) _ _
    (prefix_argument_samples z R B j hz hj) (tail_samples z R B hz)

theorem exponential_radius_le (z R B j : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hj : Γ ⊢[PRAAx] le (initial R) (pw two j)) :
    Γ ⊢[PRAAx] le (U exponentF (exponentData z R B)) (centralExponent R j) :=
  GaussianNamedExponentialTaylorTransport.radius_from_sample exponentF (exponentData z R B) (centralArgumentCap R j)
    (sample_bound_at _ _ _ zero (central_argument_samples z R B j hz hj))

theorem central_samples (z R B j : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hj : Γ ⊢[PRAAx] le (initial R) (pw two j)) :
    Γ ⊢[PRAAx] sampleBound (E exponentF) (baseData z R B) (centralCap R j) := by
  let x := exponentData z R B
  let u := U exponentF x
  have hu : Γ ⊢[PRAAx] le u (centralExponent R j) := exponential_radius_le z R B j hz hj
  have cap : Γ ⊢[PRAAx] le (factor u) (centralCap R j) :=
    GaussianFactorBudget.power_monotone_length (num 3) u (centralExponent R j) (zero_lt_succ _) hu
  exact widen_samples (E exponentF) (exponentialInputData exponentF x) (factor u) (centralCap R j) cap
    (GaussianNamedExponentialTaylorTransport.exponential_samples exponentF u x
      (exponential_input exponentF x (exponent_regular z R B hz)))

theorem actual_Barnes_central_scalar_dyadic_growth_bound_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (let z := var 0
       let R := var 1
       let B := var 2
       let j := var 3
       (source z R B ⋏ le (initial R) (pw two j)) ⟶
         sampleBound (E exponentF) (baseData z R B) (centralCap R j)) :=
  closeUniv 4 (.impI (central_samples _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDyadicCentralBound
