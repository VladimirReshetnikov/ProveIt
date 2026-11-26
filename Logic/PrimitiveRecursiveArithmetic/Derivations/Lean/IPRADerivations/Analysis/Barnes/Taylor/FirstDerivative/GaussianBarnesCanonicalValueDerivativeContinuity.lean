import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalValueDerivative
import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalPrefixDerivativeContinuity
import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalTailExponentialDerivativeContinuity
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedAddRate

/-!
# Uniform continuity of the original full Barnes derivative

The prefix and its derivative have uniform Lipschitz constants at the
kept cutoff. The two cofinal tail names have certified disk moduli.
One primitive-recursive input precision feeds all four rates through
the actual named sum of products.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalValueDerivativeContinuity

open_ipra
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalValueDerivative (nameF data)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerNamedPowerScalingPowerFrozen (multiply_same_denominator unit_rate_after)
open GaussianFastValueCut (exponent)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "I" => GaussianBarnesCanonicalValue.prefixF
local notation "id" => GaussianBarnesCanonicalValue.prefixData
local notation "J" => GaussianBarnesCanonicalPrefixDerivative.derivativeF
local notation "jd" => GaussianBarnesCanonicalPrefixDerivative.derivativeData
local notation "T" => GaussianBarnesCanonicalTailExponential.nameF
local notation "td" => GaussianBarnesCanonicalTailExponential.data
local notation "D" => GaussianBarnesCanonicalTailExponentialDerivative.derivativeF
local notation "dd" => GaussianBarnesCanonicalTailExponentialDerivative.derivativeData
local notation "Icap" => GaussianBarnesCanonicalDiskBound.prefixBound
local notation "Jcap" => GaussianBarnesCanonicalPrefixDerivativeContinuity.cap
local notation "Tcap" => GaussianBarnesCanonicalTailExponentialMargin.exponentialBound
local notation "Dcap" => GaussianBarnesCanonicalValueDerivativeJoin.tailDerivativeBound
local notation "Igain" => GaussianBarnesCanonicalUniformContinuity.gain
local notation "Jgain" => GaussianBarnesCanonicalPrefixDerivativeContinuity.gain
local notation "Tclock" => GaussianBarnesCanonicalTailContinuity.inputClock
local notation "Dclock" => GaussianBarnesCanonicalTailExponentialDerivativeContinuity.inputClock

def outputGain (R : PTm n) : PTm n := Icap R+Dcap R+(Jcap R+Tcap R)
def productClock (R p : PTm n) : PTm n := exponent (outputGain R) p

def inputClock (R p : PTm n) : PTm n :=
  let q := productClock R p
  exponent (Igain R (initial R)) q+exponent (Jgain R) q+Tclock R q+Dclock R q

def inputClockF : PR 2 := PTm.toPR (inputClock (var 0) (var 1))

@[simp] private theorem subst_prefactor_radius {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (GaussianBarnesCanonicalDiskBound.prefactorRadius R) =
      GaussianBarnesCanonicalDiskBound.prefactorRadius (Syn.subst σ R) := by
  let r := Syn.subst σ R
  let l : PTm n := GaussianNameBounds.U GaussianStirlingConstant.nameF (GaussianStirlingConstant.nameData zero)
  let c : PTm n := GaussianNameBounds.U GaussianGammaCanonicalExponent.gammaF zero
  let l' : PTm m := GaussianNameBounds.U GaussianStirlingConstant.nameF (GaussianStirlingConstant.nameData zero)
  let c' : PTm m := GaussianNameBounds.U GaussianGammaCanonicalExponent.gammaF zero
  change Syn.subst σ ((two*(R*l)+two)+(two*(R+(R*R)*(one+c))+two)) =
    (two*(r*l')+two)+(two*(r+(r*r)*(one+c'))+two)
  simp [r,l,c,l',c',one,two,GaussianStirlingConstant.nameData]

@[simp] theorem subst_inputClock {m : ℕ} (σ : Fin n → PTm m) (R p : PTm n) :
    Syn.subst σ (inputClock R p) = inputClock (Syn.subst σ R) (Syn.subst σ p) := by
  simp [inputClock,productClock,outputGain,GaussianBarnesCanonicalDiskBound.prefixBound,
    GaussianBarnesCanonicalValueDerivativeJoin.tailDerivativeBound,GaussianBarnesCanonicalUniformContinuity.gain,
    GaussianBarnesCanonicalPrefactorLipschitz.gain,GaussianBarnesCanonicalPrefactorLipschitz.disk,
    GaussianBarnesCanonicalPrefactorLipschitz.exponentGain,
    GaussianBarnesCanonicalPrefactorLipschitz.linearGain,GaussianBarnesCanonicalPrefactorLipschitz.quadraticGain,
    GaussianBarnesCanonicalPrefactorLipschitz.halfGain,GaussianBarnesCanonicalPrefactor.quadraticCoefficientData,
    GaussianBarnesCanonicalPrefactor.negativeHalf,GaussianStirlingConstant.nameData,one,two]

theorem input_clock_at (R p : PTm n) : Γ ⊢[PRAAx] ap2 inputClockF R p ≐ inputClock R p := by
  simpa only [inputClockF,ap2,subst_inputClock,Syn.subst_var,Matrix.cons_val] using
    toPR_eq (Γ := Γ) (inputClock (var 0) (var 1) : PTm 2) ![R,p]

private theorem narrow_input (x y j k : PTm n) (h : Γ ⊢[PRAAx] le j k)
    (hd : Γ ⊢[PRAAx] distanceBounded x y one (unit k)) :
    Γ ⊢[PRAAx] distanceBounded x y one (unit j) :=
  distance_radius_mono _ _ _ _ _ _ (unit_positive k) (unit_positive j)
    (le_congr (one_mul _).eqSymm (one_mul _).eqSymm (GaussianExponentialReference.unit_monotone h)) hd

theorem uniform_input (z w R B C p : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source w R C)
    (hd : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w C) one (unit (inputClock R p))) :
    Γ ⊢[PRAAx] independentRate nameF nameF (data z R B) (data w R C) one (unit p) := by
  let q := productClock R p
  let k := inputClock R p
  let U := unit q
  let N := initial R
  let a := exponent (Igain R N) q
  let b := exponent (Jgain R) q
  let c := Tclock R q
  let e := Dclock R q
  have ha : Γ ⊢[PRAAx] le a k := le_trans (le_add_right a b) (le_trans (le_add_right _ c) (le_add_right _ e))
  have hb : Γ ⊢[PRAAx] le b k := le_trans (le_add_left b a) (le_trans (le_add_right _ c) (le_add_right _ e))
  have hc : Γ ⊢[PRAAx] le c k := le_trans (le_add_left _ _) (le_add_right _ e)
  have he : Γ ⊢[PRAAx] le e k := le_add_left _ _
  have hU : Γ ⊢[PRAAx] le one U := unit_positive q
  have hK := unit_positive (Γ := Γ) k
  have i := GaussianBarnesCanonicalUniformContinuity.finite_rate z w R B C N one (unit k) hz hw hK hd
  have j := GaussianBarnesCanonicalPrefixDerivativeContinuity.independent_rate z w R B C one (unit k) hz hw hK hd
  have ip : Γ ⊢[PRAAx] independentRate I I (id z R B) (id w R C) (Igain R N) (unit k) :=
    GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _ (by ipra_ring) (.eqRefl _) i
  have jp : Γ ⊢[PRAAx] independentRate J J (jd z R B) (jd w R C) (Jgain R) (unit k) :=
    GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _ (by ipra_ring) (.eqRefl _) j
  have i' := unit_rate_after I I (id z R B) (id w R C) (Igain R N) k q ha ip
  have j' := unit_rate_after J J (jd z R B) (jd w R C) (Jgain R) k q hb jp
  have t := GaussianBarnesCanonicalTailContinuity.uniform_input z w R B C q hz hw (narrow_input _ _ c k hc hd)
  have d := GaussianBarnesCanonicalTailExponentialDerivativeContinuity.uniform_input z w R B C q hz hw
    (narrow_input _ _ e k he hd)
  have left := multiply_same_denominator D I D I (dd z R B) (id z R B) (dd w R C) (id w R C)
    one one U (Icap R) (Dcap R) hU
    (GaussianBarnesCanonicalTailExponentialDerivative.derivative_regular z R B hz)
    (GaussianBarnesCanonicalValue.prefix_regular z R B hz)
    (GaussianBarnesCanonicalTailExponentialDerivative.derivative_regular w R C hw)
    (GaussianBarnesCanonicalValue.prefix_regular w R C hw)
    (GaussianBarnesCanonicalValueDerivativeJoin.prefix_samples_bound z R B hz)
    (GaussianBarnesCanonicalValueDerivativeJoin.tail_derivative_samples_bound w R C hw) d i'
  have right := multiply_same_denominator T J T J (td z R B) (jd z R B) (td w R C) (jd w R C)
    one one U (Jcap R) (Tcap R) hU
    (GaussianBarnesCanonicalTailExponential.regular z R B hz)
    (GaussianBarnesCanonicalPrefixDerivative.regular z R B hz)
    (GaussianBarnesCanonicalTailExponential.regular w R C hw)
    (GaussianBarnesCanonicalPrefixDerivative.regular w R C hw)
    (GaussianBarnesCanonicalPrefixDerivativeContinuity.samples_bound z R B hz)
    (GaussianBarnesCanonicalTailExponentialMargin.exponential_samples_bound w R C hw) t j'
  have joined := GaussianNamedAddRate.independent_rate (multiplyF D I) (multiplyF T J) (multiplyF D I) (multiplyF T J)
    (multiplyData D I (dd z R B) (id z R B)) (multiplyData T J (td z R B) (jd z R B))
    (multiplyData D I (dd w R C) (id w R C)) (multiplyData T J (td w R C) (jd w R C))
    _ U _ U hU hU left right
  have reduced : Γ ⊢[PRAAx] independentRate nameF nameF (data z R B) (data w R C) (outputGain R) U := by
    apply GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (positive_product _ _ hU hU) hU _ joined
    apply le_of_eq_add (d := zero)
    change Γ ⊢[PRAAx]
      (Icap R+Dcap R+(Jcap R+Tcap R))*(U*U) ≐
        ((Icap R*one+Dcap R*one)*U+(Jcap R*one+Tcap R*one)*U)*U+zero
    ipra_ring
  exact unit_rate_after nameF nameF _ _ (outputGain R) q p (le_refl _) reduced

theorem actual_Barnes_full_derivative_uniform_disk_continuity_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (let z := var 0
       let w := var 1
       let R := var 2
       let B := var 3
       let C := var 4
       let p := var 5
       (source z R B ⋏ source w R C) ⟶
         distanceBounded (ofGaussian z B) (ofGaussian w C) one (unit (inputClock R p)) ⟶
         independentRate nameF nameF (data z R B) (data w R C) one (unit p)) :=
  closeUniv 6 (.impI (.impI (uniform_input _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalValueDerivativeContinuity
