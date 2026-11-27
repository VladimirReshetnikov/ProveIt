import IPRADerivations.Analysis.Gamma.NegativeAxis.Values.GaussianGammaNegativeIntervalExponentialFreeze
import IPRADerivations.Analysis.Gamma.NegativeAxis.Logarithms.GaussianGammaNegativeIntervalNamedLogFrozen
import IPRADerivations.Analysis.Gamma.NegativeAxis.Input.GaussianGammaNegativeIntervalNamedInput
import IPRADerivations.Analysis.Gamma.NegativeAxis.Values.GaussianGammaNegativeIntervalNamedSign
import IPRADerivations.Analysis.Euler.VerticalBounds.Integrands.GaussianEulerVerticalRealSamples
import IPRADerivations.Analysis.Names.FiniteOperations.Products.Bounds.GaussianNamedMultiplyRate

/-!
# Negative Gamma at named real offsets

The exponential of the named logarithm agrees at a uniform rate with
the sign-adjusted original Gamma values at late rational observations.
Multiplying by the interval sign recovers the original Gamma evaluator
at those observations with the same leading rate.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedGamma

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaFiniteApproximantName (exponentialInputData)
open GaussianGammaNegativeIntervalNamedInput (sampleNumerator sampleDenominator frozen_guard)
open GaussianGammaNegativeIntervalNamedLog (clock data encodedData nameF name_regular name_real)
open GaussianGammaNegativeIntervalNamedSign (valueF valueData value_involution value_regular)
open GaussianGammaNegativeIntervalProductSign (signUnit)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameBounds (U all_samples_bounded)
open GaussianNameEquivalence (cross_refl cross_symm)
open GaussianNameRingLaws (three)
open GaussianNamedEulerUnitTime (source)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianRadiusExponentialLipschitzRate (factor)
open GaussianRationalMetric (bounded)
open GaussianRationalPowerAlgebra (unit_bounded unit_power norm_one)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSyntheticDivision (qone)
open GaussianStirlingLogDuplication (exponential_regular)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => GaussianGammaNegativeIntervalLogAbsolute.nameF
local notation "S" => GaussianGammaNegativeIntervalGammaSign.signedF
local notation "sd" => GaussianGammaNegativeIntervalGammaSign.signedData
local notation "gd" => GaussianGammaNegativeIntervalNative.data

def signedF (f : PR 2) : PR 2 := GaussianRadiusExponentialName.nameF (nameF f)
def signedData (f : PR 2) (x E N : PTm n) : PTm n := exponentialInputData (nameF f) (data x E N)
def actualF (f : PR 2) : PR 2 := valueF (signedF f)
def actualData (f : PR 2) (x E N : PTm n) : PTm n := valueData (signedF f) N (signedData f x E N)
def rateFactor (f : PR 2) (x E N : PTm n) : PTm n := factor (U (nameF f) (data x E N)+three)

theorem signed_regular (f : PR 2) (x E N : PTm n) (hs : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] pointCN (signedF f) (signedData f x E N) :=
  exponential_regular _ _ (name_regular f x E N hs)

theorem signed_real (f : PR 2) (x E N : PTm n) :
    Γ ⊢[PRAAx] GaussianSignedNameExponentialOrder.realSamples (signedF f) (signedData f x E N) :=
  GaussianEulerVerticalRealSamples.original_exponential_real_samples (nameF f) _ _ (name_real f x E N)

theorem actual_regular (f : PR 2) (x E N : PTm n) (hs : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] pointCN (actualF f) (actualData f x E N) :=
  value_regular _ _ _ (signed_regular f x E N hs)

theorem signed_frozen_rate (f : PR 2) (s k x E N : PTm n) (hs : Γ ⊢[PRAAx] source f x E)
    (late : Γ ⊢[PRAAx] le (clock s E N) k) : Γ ⊢[PRAAx]
    independentRate (signedF f) S (signedData f x E N) (sd (sampleNumerator f k x) (sampleDenominator f k x) N)
      (rateFactor f x E N) (unit s) := by
  let a := sampleNumerator f k x
  let b := sampleDenominator f k x
  let u := signedData f x E N
  let v := exponentialInputData L (encodedData f k x N)
  have h := frozen_guard f k x E hs
  have hf := name_regular f x E N hs
  have hg := GaussianGammaNegativeIntervalLogAbsolute.name_regular a b N h
  have logRate := GaussianGammaNegativeIntervalNamedLogFrozen.original_frozen_rate f s k x E N hs late
  have expRate := GaussianGammaNegativeIntervalExponentialFreeze.exponential_rate (nameF f) L
    (data x E N) (encodedData f k x N) s hf hg logRate
  exact GaussianNamedRateTransport.transport (signedF f) (GaussianRadiusExponentialName.nameF L) (signedF f) S
    u v u (sd a b N) (rateFactor f x E N) (unit s) (unit_positive s) expRate
    (cross_refl _ _ (signed_regular f x E N hs))
    (cross_symm _ _ _ _ (GaussianGammaNegativeIntervalLogAbsolute.original_exponential a b N h))

private theorem sign_samples (N : PTm n) : Γ ⊢[PRAAx] sampleBound constantF (signUnit (succ N)) one := by
  refine .allI ?_
  have fixed : Γ.map Fm.shift ⊢[PRAAx] bounded (signUnit (succ (Syn.shift N))) one one :=
    unit_bounded _ (unit_power _ _ ((GaussianRationalRelativeTwoTerm.norm_negative qone).eqTrans norm_one))
  simpa only [sampleBound,Syn.shift,GaussianGammaNegativeIntervalProductSign.subst_signUnit,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    bound_congr (constant_at (var 0) (signUnit (succ (Syn.shift N)))).eqSymm (.eqRefl _) (.eqRefl _) fixed

theorem actual_frozen_rate (f : PR 2) (s k x E N : PTm n) (hs : Γ ⊢[PRAAx] source f x E)
    (late : Γ ⊢[PRAAx] le (clock s E N) k) : Γ ⊢[PRAAx]
    independentRate (actualF f) gammaF (actualData f x E N) (gd (sampleNumerator f k x) (sampleDenominator f k x) N)
      (rateFactor f x E N) (unit s) := by
  let a := sampleNumerator f k x
  let b := sampleDenominator f k x
  let u := signedData f x E N
  let v := sd a b N
  let w := gd a b N
  let c := signUnit (succ N)
  let A := rateFactor f x E N
  have hu := signed_regular f x E N hs
  have hw := GaussianGammaNegativeIntervalNative.negative_regular a b N (frozen_guard f k x E hs)
  have hv : Γ ⊢[PRAAx] pointCN S v := value_regular gammaF N w hw
  have hc := constant_regular (Γ := Γ) c
  have rate := GaussianNamedMultiplyRate.independent_rate constantF (signedF f) constantF S c u c v
    zero one A (unit s) (U (signedF f) u) one (le_refl one) (unit_positive s) hc hu hc hv
    (all_samples_bounded (signedF f) u hu) (sign_samples N) (GaussianNamedAddRate.self_rate constantF c hc)
    (signed_frozen_rate f s k x E N hs late)
  have reduced := GaussianNamedDifferenceRate.rate_parameters_congr (actualF f) (valueF S)
    (actualData f x E N) (valueData S N v) _ _ A (unit s)
    (by dsimp only [GaussianNamedMultiplyRate.leadingNumerator]; ipra_ring)
    (by dsimp only [GaussianNamedMultiplyRate.leadingDenominator]; ipra_ring) rate
  exact GaussianNamedRateTransport.transport (actualF f) (valueF S) (actualF f) gammaF
    (actualData f x E N) (valueData S N v) (actualData f x E N) w A (unit s) (unit_positive s)
    reduced (cross_refl _ _ (actual_regular f x E N hs))
    (cross_symm _ _ _ _ (value_involution gammaF N w hw))

theorem actual_named_negative_Gamma_frozen_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source f (var 0) (var 1) ⟶ le (clock (var 3) (var 1) (var 2)) (var 4) ⟶
        independentRate (actualF f) gammaF (actualData f (var 0) (var 1) (var 2))
          (gd (sampleNumerator f (var 4) (var 0)) (sampleDenominator f (var 4) (var 0)) (var 2))
          (rateFactor f (var 0) (var 1) (var 2)) (unit (var 3))) :=
  closeUniv 5 (.impI (.impI (actual_frozen_rate f _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedGamma
