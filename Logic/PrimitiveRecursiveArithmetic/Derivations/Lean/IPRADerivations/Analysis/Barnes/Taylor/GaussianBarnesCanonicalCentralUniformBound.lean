import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalDiskBound
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalSingleExponential
import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalCenteredExponentialShift
import IPRADerivations.Analysis.FiniteOperations.GaussianUniformFiniteSumBound
import IPRADerivations.Analysis.Names.GaussianNamedBoundedSumObservation

/-!
# Disk-uniform bounds for the original Barnes central exponential

The retained correction is an actual finite sum with an explicit uniform
row bound. Add its bound to the original prefactor exponent bound, then
add the original logarithmic tail bound for the cofinal central scalar.
All resulting sample caps depend only on the disk radius.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCentralUniformBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalCorrectionShift (total body parameters body_at subst_parameters)
open GaussianBarnesCanonicalDiskBound (prefactorRadius radius_le)
open GaussianBarnesCanonicalFactor (exponentRadius correction_bound)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalSingleExponential (prefactorExponentData prefixF prefixData exponentF exponentData)
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaFiniteApproximantName (exponentialInputData exponential_input)
open GaussianNameBounds (U)
open GaussianNamedMultiplyRate (sampleBound sample_bound_at)
open GaussianRadiusExponentialLipschitzRate (factor subst_factor)
open GaussianRationalMetric (bounded)
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

def correctionCap (R N : PTm n) : PTm n := N*exponentRadius R
def prefixArgumentCap (R : PTm n) : PTm n := (prefactorRadius R+prefactorRadius R)+correctionCap R (initial R)
def centralArgumentCap (R : PTm n) : PTm n := prefixArgumentCap R+GaussianBarnesCanonicalFiniteLog.radius R
def prefixCap (R : PTm n) : PTm n := factor (two*prefixArgumentCap R+two)
def centralCap (R : PTm n) : PTm n := factor (two*centralArgumentCap R+two)
def prefixUGain (R : PTm n) : PTm n := two*prefixCap R+two
def centralUGain (R : PTm n) : PTm n := two*centralCap R+two

theorem correction_total_bound (z R B N : PTm n) (hz : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    bounded (total z B N) (correctionCap R N) one := by
  refine GaussianUniformFiniteSumBound.uniform_sum_bound body N (parameters z B) (exponentRadius R) one
    (le_refl one) (.allI (.impI ?_))
  let a (x : PTm n) := Syn.shift x
  let Δ := lt (var 0) (a N) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (a z) (a R) (a B) := by simpa [Δ,a,Fm.shift,Syn.shift] using hz.shift.wk
  have row := correction_bound (a z) (a R) (a B) (ConciseIPRA.PTm.succ (var 0))
    (.andI hs.andE₁ (.andI (zero_lt_succ _) hs.andE₂))
  simpa only [Δ,a,Syn.shift,subst_parameters,exponentRadius,LeanProofs.IPRA.PTm.subst_add,LeanProofs.IPRA.PTm.subst_mul,
    one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    bound_congr (body_at (var 0) (a z) (a B)).eqSymm (.eqRefl _) (.eqRefl _) row

private theorem constant_samples (x A : PTm n) (h : Γ ⊢[PRAAx] bounded x A one) :
    Γ ⊢[PRAAx] sampleBound constantF x A := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift x) (Syn.shift A) one := by
    simpa [Fm.shift,Syn.shift,one] using h.shift
  simpa only [sampleBound,Syn.shift] using bound_congr (constant_at (var 0) (Syn.shift x)).eqSymm
    (.eqRefl _) (.eqRefl _) hs

private theorem widen_samples (f : PR 2) (x A C : PTm n) (hA : Γ ⊢[PRAAx] le A C)
    (h : Γ ⊢[PRAAx] sampleBound f x A) : Γ ⊢[PRAAx] sampleBound f x C := by
  refine .allI ?_
  let a (v : PTm n) := Syn.shift v
  have hs : Γ.map Fm.shift ⊢[PRAAx] sampleBound f (a x) (a A) := by simpa [Fm.shift,a,Syn.shift] using h.shift
  have hAs : Γ.map Fm.shift ⊢[PRAAx] le (a A) (a C) := by simpa [Fm.shift,a,Syn.shift] using hA.shift
  simpa only [sampleBound,a,Syn.shift] using
    bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one) (mul_le_mul_right one hAs)
      (sample_bound_at f (a x) (a A) (var 0) hs)

theorem prefix_argument_samples (z R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    sampleBound prefixF (prefixData z R B) (prefixArgumentCap R) := by
  have pref := GaussianBarnesCanonicalPrefactorInverse.exponent_input (Γ := Γ) z B
  have size := radius_le z R B hz
  have pre := widen_samples P (prefactorExponentData z B) (GaussianBarnesCanonicalPrefactorInverse.exponentRadius z B)
    (prefactorRadius R+prefactorRadius R) (add_le_add₂ size size) pref.andE₂
  have correction := constant_samples (total z B (initial R)) (correctionCap R (initial R))
    (correction_total_bound z R B (initial R) hz)
  exact GaussianNamedBoundedSumObservation.sample_bounds P constantF (prefactorExponentData z B) (total z B (initial R))
    _ _ pre correction

theorem central_argument_samples (z R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    sampleBound exponentF (exponentData z R B) (centralArgumentCap R) :=
  GaussianNamedBoundedSumObservation.sample_bounds prefixF L (prefixData z R B) (ld z R B) _ _
    (prefix_argument_samples z R B hz) (GaussianBarnesCanonicalTailExponential.log_input z R B hz).andE₂

private theorem U_from_zero (f : PR 2) (x C : PTm n) (h : Γ ⊢[PRAAx] bounded (ap2 f zero x) C one) :
    Γ ⊢[PRAAx] le (U f x) (two*C+two) := by
  let q := ap2 f zero x
  let v := GaussianRationalL1.qL1 q
  let a := RationalIntegerNormalization.positivePart (RationalSupMetric.numeratorOf v)
  let b := RationalSupMetric.denominatorOf v
  have hb : Γ ⊢[PRAAx] le one b := RationalArgmin.denominator_positive v
  have hl := GaussianRationalL1Algebra.qL1_of_bounded q C one (le_refl one) h
  have cleared := GaussianRationalMetric.comparison_to_cleared v (GaussianEuclideanDistanceName.fraction (two*C) one)
    a (two*C) b one (GaussianGeneralFTAConstants.l1_natural_representation q)
    (GaussianEuclideanDistanceName.fraction_represents _ _ (le_refl one)) hl
  have ceiling := GaussianDescentClockArithmetic.ceiling_least a b (two*C) hb
    (le_congr (one_mul a) (mul_comm _ _) cleared)
  exact add_le_add_right two ceiling

private theorem exponential_samples (f : PR 2) (x C : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN f x) (hC : Γ ⊢[PRAAx] sampleBound f x C) :
    Γ ⊢[PRAAx] sampleBound (E f) (exponentialInputData f x) (factor (two*C+two)) := by
  refine .allI ?_
  let a (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  let u := U f (a x)
  let c := two*a C+two
  have hp : Δ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN f (a x) := by
    simpa [Δ,a,Fm.shift,Syn.shift] using h.shift
  have hc : Δ ⊢[PRAAx] sampleBound f (a x) (a C) := by simpa [Δ,a,Fm.shift,Syn.shift] using hC.shift
  have hU := U_from_zero f (a x) (a C) (sample_bound_at f (a x) (a C) zero hc)
  have b := GaussianPositiveExponentialMajorant.disk_bound (GaussianRadiusExponentialName.query f u (var 0) (a x)) u
    (GaussianRadiusExponentialName.index u (var 0))
    (GaussianRadiusExponentialName.query_bound f u (a x) (var 0) (exponential_input f (a x) hp))
  have hF : Δ ⊢[PRAAx] le (factor u) (factor c) :=
    GaussianFactorBudget.power_monotone_length (num 3) u c (zero_lt_succ _) hU
  have bound := bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one) (mul_le_mul_right one hF) b
  simpa only [sampleBound,a,Δ,u,c,Syn.shift,exponentialInputData,GaussianRadiusExponentialName.subst_data,
    GaussianRadiusExponentialName.sample,GaussianNameBounds.subst_U,subst_factor,LeanProofs.IPRA.PTm.subst_add,LeanProofs.IPRA.PTm.subst_mul,
    one,two,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    bound_congr (GaussianRadiusExponentialName.sample_at f u (var 0) (a x)).eqSymm (.eqRefl _) (.eqRefl _) bound

theorem prefix_samples (z R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    sampleBound (E prefixF) (exponentialInputData prefixF (prefixData z R B)) (prefixCap R) :=
  exponential_samples prefixF (prefixData z R B) (prefixArgumentCap R)
    (GaussianNameArithmetic.add_fast P constantF _ _
      (GaussianBarnesCanonicalPrefactorInverse.exponent_input z B).andE₁ (constant_regular _))
    (prefix_argument_samples z R B hz)

theorem central_samples (z R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    sampleBound (E exponentF) (GaussianBarnesCanonicalCenteredExponentialShift.baseData z R B) (centralCap R) :=
  exponential_samples exponentF (exponentData z R B) (centralArgumentCap R)
    (GaussianBarnesCanonicalSingleExponential.exponent_regular z R B hz) (central_argument_samples z R B hz)

theorem prefix_U_le (z R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    le (U (E prefixF) (exponentialInputData prefixF (prefixData z R B))) (prefixUGain R) :=
  U_from_zero _ _ _ (sample_bound_at _ _ _ zero (prefix_samples z R B hz))

theorem central_U_le (z R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    le (U (E exponentF) (GaussianBarnesCanonicalCenteredExponentialShift.baseData z R B)) (centralUGain R) :=
  U_from_zero _ _ _ (sample_bound_at _ _ _ zero (central_samples z R B hz))

theorem actual_Barnes_central_scalar_disk_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶
      sampleBound (E exponentF) (GaussianBarnesCanonicalCenteredExponentialShift.baseData (var 0) (var 1) (var 2))
        (centralCap (var 1))) :=
  closeUniv 3 (.impI (central_samples (var 0) (var 1) (var 2) Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCentralUniformBound
