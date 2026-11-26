import IPRADerivations.Analysis.Barnes.Deflation.GaussianBarnesCanonicalDeflatedHeadLipschitz
import IPRADerivations.Analysis.Barnes.TailControl.GaussianBarnesCanonicalTailContinuity
import IPRADerivations.Analysis.Barnes.Prefactors.GaussianBarnesCanonicalPrefactorLipschitz

/-!
# An explicit input demand for the original deflated Barnes coefficient

The literal deflated head, prefactor and cofinal tail have independent
rates on a disk. Their checked bounds pay the two original named
multiplications, giving one explicit input demand valid at the center.
-/

set_option autoImplicit false
set_option maxHeartbeats 1250000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDeflatedValueContinuity

open_ipra
open GaussianBarnesCanonicalFactor (source)
open GaussianBarnesCanonicalDeflatedValue (remainingLength headCoefficientF headCoefficientData head_coefficient_regular outerF outerData nameF data)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerNamedPowerScalingPowerFrozen (multiply_same_denominator unit_rate_after)
open GaussianNamedBoundedProductObservation (sample_bounds)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianNameArithmetic (multiply_fast)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (ofGaussian)
open GaussianRationalMetric (distanceBounded)
open GaussianFastValueCut (exponent)
open GaussianGammaCanonicalExponent (gammaF)
open GaussianNameBounds (U)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "P" => GaussianBarnesCanonicalPrefactor.nameF
local notation "Pd" => GaussianBarnesCanonicalPrefactor.data
local notation "Pc" => GaussianBarnesCanonicalDiskBound.prefactorBound
local notation "Pg" => GaussianBarnesCanonicalPrefactorLipschitz.gain
local notation "T" => GaussianBarnesCanonicalTailExponential.nameF
local notation "Td" => GaussianBarnesCanonicalTailExponential.data
local notation "Hc" => GaussianBarnesCanonicalDeflatedHeadLipschitz.cap
local notation "Hg" => GaussianBarnesCanonicalDeflatedHeadLipschitz.gain

def tailCap (R : PTm n) : PTm n := GaussianRadiusExponentialLipschitzRate.factor (GaussianBarnesCanonicalFiniteLog.radius R)
def productGain (R m : PTm n) : PTm n :=
  Pc R*tailCap R+Hc R m (remainingLength R m)*(tailCap R+Pc R)
def precision (R m p : PTm n) : PTm n := exponent (productGain R m) p
def inputClock (R m p : PTm n) : PTm n :=
  let q := precision R m p
  GaussianBarnesCanonicalTailContinuity.inputClock R q+
    (exponent (Pg R) q+exponent (Hg R m (remainingLength R m)) q)

@[simp] private theorem subst_prefactorRadius {l : ℕ} (σ : Fin n → PTm l) (R : PTm n) :
    Syn.subst σ (GaussianBarnesCanonicalDiskBound.prefactorRadius R) =
      GaussianBarnesCanonicalDiskBound.prefactorRadius (Syn.subst σ R) := by
  let shape {k : ℕ} (a : PTm k) := (two*(a*U GaussianStirlingConstant.nameF (GaussianStirlingConstant.nameData zero))+two)+
    (two*(a+(a*a)*(one+U gammaF zero))+two)
  change Syn.subst σ (shape R) = shape (Syn.subst σ R)
  simp [shape,GaussianStirlingConstant.nameData,one,two]

@[simp] theorem subst_inputClock {l : ℕ} (σ : Fin n → PTm l) (R m p : PTm n) :
    Syn.subst σ (inputClock R m p) = inputClock (Syn.subst σ R) (Syn.subst σ m) (Syn.subst σ p) := by
  simp [inputClock,precision,productGain,tailCap,remainingLength,GaussianBarnesCanonicalDeflatedHeadLipschitz.cap,
    GaussianBarnesCanonicalDeflatedHeadLipschitz.multiplierCap,GaussianBarnesCanonicalDeflatedHeadLipschitz.skippedCap,
    GaussianBarnesCanonicalFactor.exponentRadius,GaussianBarnesCanonicalPrefactorLipschitz.gain,
    GaussianBarnesCanonicalPrefactorLipschitz.disk,GaussianBarnesCanonicalPrefactorLipschitz.exponentGain,
    GaussianBarnesCanonicalPrefactorLipschitz.linearGain,GaussianBarnesCanonicalPrefactorLipschitz.quadraticGain,
    GaussianBarnesCanonicalPrefactorLipschitz.halfGain,GaussianBarnesCanonicalPrefactor.negativeHalf,
    GaussianBarnesCanonicalPrefactor.quadraticCoefficientData,GaussianStirlingConstant.nameData,one,two]

private theorem prefactor_bound (z R B : PTm n) (h : Γ ⊢[PRAAx] GaussianBarnesCanonicalLogCofinal.source z R B) :
    Γ ⊢[PRAAx] sampleBound P (Pd z B) (Pc R) := by
  refine .allI ?_
  let sh (v : PTm n) := Syn.shift v
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianBarnesCanonicalLogCofinal.source (sh z) (sh R) (sh B) := by
    simpa [Fm.shift,Syn.shift,sh] using h.shift
  simpa only [sampleBound,Syn.shift,sh,GaussianBarnesCanonicalPrefactor.subst_data,
    GaussianBarnesCanonicalDiskBound.subst_prefactorBound] using
    GaussianBarnesCanonicalDiskBound.prefactor_sample_bound (var 0) (sh z) (sh R) (sh B) hs

theorem uniform_input (z w R B D m p : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B m) (hw : Γ ⊢[PRAAx] source w R D m)
    (h : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) one (unit (inputClock R m p))) :
    Γ ⊢[PRAAx] independentRate nameF nameF (data z R B m) (data w R D m) one (unit p) := by
  let q := precision R m p
  let r := remainingLength R m
  let I := inputClock R m p
  let s := GaussianBarnesCanonicalTailContinuity.inputClock R q
  let a := Pd z B
  let b := Td z R B
  let c := Pd w D
  let d := Td w R D
  let x := headCoefficientData z R B m r
  let y := headCoefficientData w R D m r
  have hZ : Γ ⊢[PRAAx] GaussianBarnesCanonicalLogCofinal.source z R B := .andI hz.andE₁ hz.andE₂.andE₂
  have hW : Γ ⊢[PRAAx] GaussianBarnesCanonicalLogCofinal.source w R D := .andI hw.andE₁ hw.andE₂.andE₂
  have hp : Γ ⊢[PRAAx] le (exponent (Pg R) q) I :=
    le_trans (le_add_right _ _) (le_add_left _ _)
  have hh : Γ ⊢[PRAAx] le (exponent (Hg R m r) q) I :=
    le_trans (le_add_left _ _) (le_add_left _ _)
  have ht : Γ ⊢[PRAAx] le s I := le_add_right _ _
  have tailFine := distance_radius_mono _ _ _ _ one (unit s) (unit_positive I) (unit_positive s)
    (le_congr (one_mul _).eqSymm (one_mul _).eqSymm (GaussianExponentialReference.unit_monotone ht)) h
  have hp0 := GaussianBarnesCanonicalPrefactorLipschitz.independent_rate z w R B D one (unit I) hZ hW (unit_positive I) h
  have hh0 := GaussianBarnesCanonicalDeflatedHeadLipschitz.independent_rate z w R B D m r one (unit I) hz hw (unit_positive I) h
  have pr := unit_rate_after P P a c (Pg R) I q hp
    (GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _ (by ipra_ring) (.eqRefl _) hp0)
  have hr := unit_rate_after headCoefficientF headCoefficientF x y (Hg R m r) I q hh
    (GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _ (by ipra_ring) (.eqRefl _) hh0)
  have tr := GaussianBarnesCanonicalTailContinuity.uniform_input z w R B D q hZ hW tailFine
  have ha := GaussianBarnesCanonicalPrefactor.regular (Γ := Γ) z B
  have hb := GaussianBarnesCanonicalTailExponential.regular z R B hZ
  have hc := GaussianBarnesCanonicalPrefactor.regular (Γ := Γ) w D
  have hd := GaussianBarnesCanonicalTailExponential.regular w R D hW
  have bo := GaussianBarnesCanonicalTailContinuity.sample_bound z R B hZ
  have outer := multiply_same_denominator P T P T a b c d one one (unit q) (tailCap R) (Pc R) (unit_positive q)
    ha hb hc hd bo (prefactor_bound w R D hW) pr tr
  have bc := sample_bounds P T a b (Pc R) (tailCap R) (prefactor_bound z R B hZ) bo
  have full := multiply_same_denominator headCoefficientF outerF headCoefficientF outerF x (outerData z R B) y (outerData w R D)
    one _ (unit q) (Pc R*tailCap R) (Hc R m r) (unit_positive q)
    (head_coefficient_regular z R B m r hz) (multiply_fast P T a b ha hb)
    (head_coefficient_regular w R D m r hw) (multiply_fast P T c d hc hd)
    bc (GaussianBarnesCanonicalDeflatedHeadLipschitz.sample_bound w R D m r hw) hr outer
  exact unit_rate_after nameF nameF (data z R B m) (data w R D m) (productGain R m) q p (le_refl _)
    (GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _
      (by unfold productGain; dsimp only [r]; ipra_ring) (.eqRefl _) full)

theorem actual_Barnes_deflated_uniform_disk_continuity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let z := var 0
     let w := var 1
     let R := var 2
     let B := var 3
     let D := var 4
     let m := var 5
     let p := var 6
     (source z R B m ⋏ source w R D m) ⟶
       distanceBounded (ofGaussian z B) (ofGaussian w D) one (unit (inputClock R m p)) ⟶
       independentRate nameF nameF (data z R B m) (data w R D m) one (unit p)) :=
  closeUniv 7 (.impI (.impI (uniform_input _ _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDeflatedValueContinuity
