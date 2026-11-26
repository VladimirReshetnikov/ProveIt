import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalHeadDerivativeContinuity
import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalPrefactorDerivativeContinuity
import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalPrefixDerivative
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedBoundedSumObservation

/-!
# Uniform disk continuity of the original Barnes prefix derivative

The two terms of the actual product rule retain their original
prefactor and finite head observations, at the fixed kept cutoff.
Their separate disk rates and sample bounds supply a common rate for
the literal derivative name across arbitrary rational presentations.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefixDerivativeContinuity

open_ipra
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalPrefixDerivative (derivativeF derivativeData)
open GaussianEulerNamedPowerScalingPowerFrozen (multiply_same_denominator)
open GaussianNameArithmetic (addF addData multiplyF multiplyData)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "P" => GaussianBarnesCanonicalPrefactor.nameF
local notation "pd" => GaussianBarnesCanonicalPrefactor.data
local notation "DP" => GaussianBarnesCanonicalPrefactorDerivative.derivativeF
local notation "dp" => GaussianBarnesCanonicalPrefactorDerivative.derivativeData
local notation "H" => GaussianBarnesCanonicalHead.nameF
local notation "hd" => GaussianBarnesCanonicalHead.headData
local notation "DH" => GaussianBarnesCanonicalHeadDerivativeJoin.derivativeF
local notation "dh" => GaussianBarnesCanonicalHeadDerivativeJoin.derivativeData
local notation "Pcap" => GaussianBarnesCanonicalDiskBound.prefactorBound
local notation "DPcap" => GaussianBarnesCanonicalPrefactorDerivative.derivativeBound
local notation "Hcap" => GaussianBarnesCanonicalHead.cap
local notation "DHcap" => GaussianBarnesCanonicalHeadDerivativeContinuity.cap
local notation "Pgain" => GaussianBarnesCanonicalPrefactorLipschitz.gain
local notation "DPgain" => GaussianBarnesCanonicalPrefactorDerivativeContinuity.gain
local notation "Hgain" => GaussianBarnesCanonicalHeadLipschitz.gain
local notation "DHgain" => GaussianBarnesCanonicalHeadDerivativeContinuity.gain

def gain (R : PTm n) : PTm n :=
  (Hcap R zero (initial R)*DPgain R+DPcap R*Hgain R zero (initial R)) +
    (DHcap R (initial R)*Pgain R+Pcap R*DHgain R (initial R))

def cap (R : PTm n) : PTm n := DPcap R*Hcap R zero (initial R)+Pcap R*DHcap R (initial R)

private theorem subst_prefactor_gain {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (Pgain R) = Pgain (Syn.subst σ R) := by
  let p := GaussianBarnesCanonicalDiskBound.prefactorRadius R
  let q := GaussianBarnesCanonicalDiskBound.prefactorRadius (Syn.subst σ R)
  have h : Syn.subst σ p = q := by
    let L : PTm n := GaussianNameBounds.U GaussianStirlingConstant.nameF (GaussianStirlingConstant.nameData zero)
    let G : PTm n := GaussianNameBounds.U GaussianGammaCanonicalExponent.gammaF zero
    let L' : PTm m := GaussianNameBounds.U GaussianStirlingConstant.nameF (GaussianStirlingConstant.nameData zero)
    let G' : PTm m := GaussianNameBounds.U GaussianGammaCanonicalExponent.gammaF zero
    let r := Syn.subst σ R
    change Syn.subst σ ((two*(R*L)+two)+(two*(R+(R*R)*(one+G))+two)) =
      (two*(r*L')+two)+(two*(r+(r*r)*(one+G'))+two)
    simp [L,G,L',G',r,one,two,GaussianStirlingConstant.nameData]
  change Syn.subst σ (GaussianRadiusExponentialLipschitzRate.factor (p+p)*
    GaussianBarnesCanonicalPrefactorDerivative.incrementGain R) =
      GaussianRadiusExponentialLipschitzRate.factor (q+q)*
        GaussianBarnesCanonicalPrefactorDerivative.incrementGain (Syn.subst σ R)
  simp only [PTm.subst_mul,GaussianRadiusExponentialLipschitzRate.subst_factor,PTm.subst_add,h,
    GaussianBarnesCanonicalPrefactorDerivative.subst_incrementGain]

@[simp] theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (gain R) = gain (Syn.subst σ R) := by simp [gain,subst_prefactor_gain]

@[simp] theorem subst_cap {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (cap R) = cap (Syn.subst σ R) := by simp [cap]

private theorem sum_rate (F G : PR 2) (x y u v A C E : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (h₁ : Γ ⊢[PRAAx] independentRate F F x u A E) (h₂ : Γ ⊢[PRAAx] independentRate G G y v C E) :
    Γ ⊢[PRAAx] independentRate (addF F G) (addF F G) (addData x y) (addData u v) (A+C) E :=
  GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (positive_product _ _ hE hE) hE
    (le_of_eq_add (d := zero) (by dsimp only [GaussianNamedRateComposition.leadingNumerator,
      GaussianNamedRateComposition.leadingDenominator]; ipra_ring))
    (GaussianNamedAddRate.independent_rate F G F G x y u v A E C E hE hE h₁ h₂)

theorem independent_rate (z w R B D A E : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source w R D) (hE : Γ ⊢[PRAAx] le one E)
    (h : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) A E) :
    Γ ⊢[PRAAx] independentRate derivativeF derivativeF (derivativeData z R B) (derivativeData w R D) (gain R*A) E := by
  let N := initial R
  let X := multiplyF DP H
  let Y := multiplyF P DH
  let L := Hcap R zero N
  let M := DPcap R
  let U := DHcap R N
  let V := Pcap R
  let C := DPgain R
  let G := Hgain R zero N
  let I := Pgain R
  let J := DHgain R N
  let x := hd z R B N
  let y := hd w R D N
  let p := pd z B
  let q := pd w D
  let a := dp z B
  let b := dp w D
  let c := dh z B N
  let d := dh w D N
  have hs := GaussianBarnesCanonicalHeadDerivativeJoin.head_samples_bound z R B N hz
  have bs := GaussianBarnesCanonicalPrefactorDerivative.derivative_samples w R D hw
  have cs := GaussianBarnesCanonicalHeadDerivativeContinuity.samples_bound z R B N hz
  have ps := GaussianBarnesCanonicalPrefactorDerivative.prefactor_samples w R D hw
  have head := GaussianBarnesCanonicalHeadLipschitz.independent_rate z w R B D zero N A E hz hw hE h
  have head' := GaussianBarnesCanonicalHeadDerivativeContinuity.independent_rate z w R B D N A E hz hw hE h
  have pref := GaussianBarnesCanonicalPrefactorLipschitz.independent_rate z w R B D A E hz hw hE h
  have pref' := GaussianBarnesCanonicalPrefactorDerivativeContinuity.rate z w R B D A E hz hw hE h
  have left : Γ ⊢[PRAAx] independentRate X X (multiplyData DP H a x) (multiplyData DP H b y) (L*(C*A)+M*(G*A)) E :=
    multiply_same_denominator DP H DP H a x b y (C*A) (G*A) E L M hE
      (GaussianBarnesCanonicalPrefactorDerivative.derivative_regular z B) (GaussianBarnesCanonicalHead.regular z R B zero N hz)
      (GaussianBarnesCanonicalPrefactorDerivative.derivative_regular w D) (GaussianBarnesCanonicalHead.regular w R D zero N hw)
      hs bs pref' head
  have right : Γ ⊢[PRAAx] independentRate Y Y (multiplyData P DH p c) (multiplyData P DH q d) (U*(I*A)+V*(J*A)) E :=
    multiply_same_denominator P DH P DH p c q d (I*A) (J*A) E U V hE
      (GaussianBarnesCanonicalPrefactor.regular z B) (GaussianBarnesCanonicalHeadDerivativeJoin.regular z B N)
      (GaussianBarnesCanonicalPrefactor.regular w D) (GaussianBarnesCanonicalHeadDerivativeJoin.regular w D N)
      cs ps pref head'
  have paid : Γ ⊢[PRAAx] (L*(C*A)+M*(G*A))+(U*(I*A)+V*(J*A)) ≐ gain R*A := by
    change Γ ⊢[PRAAx] (L*(C*A)+M*(G*A))+(U*(I*A)+V*(J*A)) ≐ ((L*C+M*G)+(U*I+V*J))*A
    ipra_ring
  exact GaussianNamedDifferenceRate.rate_parameters_congr derivativeF derivativeF (derivativeData z R B) (derivativeData w R D)
    _ _ _ _ paid (.eqRefl _) (sum_rate X Y _ _ _ _ _ _ E hE left right)

theorem samples_bound (z R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] sampleBound derivativeF (derivativeData z R B) (cap R) := by
  let N := initial R
  have aa := GaussianBarnesCanonicalPrefactorDerivative.derivative_samples z R B hz
  have bb := GaussianBarnesCanonicalHeadDerivativeJoin.head_samples_bound z R B N hz
  have cc := GaussianBarnesCanonicalPrefactorDerivative.prefactor_samples z R B hz
  have dd := GaussianBarnesCanonicalHeadDerivativeContinuity.samples_bound z R B N hz
  have left := GaussianNamedBoundedProductObservation.sample_bounds DP H (dp z B) (hd z R B N) _ _ aa bb
  have right := GaussianNamedBoundedProductObservation.sample_bounds P DH (pd z B) (dh z B N) _ _ cc dd
  exact GaussianNamedBoundedSumObservation.sample_bounds (multiplyF DP H) (multiplyF P DH) _ _ _ _ left right

theorem actual_Barnes_prefix_derivative_uniform_lipschitz_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (let z := var 0
       let w := var 1
       let R := var 2
       let B := var 3
       let D := var 4
       let A := var 5
       let E := var 6
       (source z R B ⋏ (source w R D ⋏ (le one E ⋏ distanceBounded (ofGaussian z B) (ofGaussian w D) A E))) ⟶
         independentRate derivativeF derivativeF (derivativeData z R B) (derivativeData w R D) (gain R*A) E) :=
  closeUniv 7 (.impI (independent_rate _ _ _ _ _ _ _ Prf.hyp0.andE₁
    Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefixDerivativeContinuity
