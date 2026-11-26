import IPRADerivations.Analysis.Barnes.TailControl.GaussianBarnesCanonicalUniformCutoff
import IPRADerivations.Analysis.Barnes.Prefactors.GaussianBarnesCanonicalPrefactorLipschitz
import IPRADerivations.Analysis.Barnes.HeadProducts.GaussianBarnesCanonicalHeadLipschitz
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateComposition

/-!
# Uniform continuity of the original Barnes evaluator on a disk

Compare the two inputs at a common uniform literal cutoff. The finite
prefactor and head rates give an explicit input clock that absorbs the
effect of changing inputs. The two uniform tail bounds pay the remaining
output budget.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalUniformContinuity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalProduct (literalData)
open GaussianBarnesCanonicalUniformCutoff (cutoff uniform_rate)
open GaussianBarnesCanonicalValue (prefixF nameF data)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerNamedPowerScalingPowerFrozen (multiply_same_denominator unit_rate_after)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianNamedRateComposition (symmetric same_denominator)
open GaussianRationalHorner (ofGaussian)
open GaussianRationalMetric (distanceBounded)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "P" => GaussianBarnesCanonicalPrefactor.nameF
local notation "H" => GaussianBarnesCanonicalHead.nameF
local notation "pd" => GaussianBarnesCanonicalPrefactor.data
local notation "hd" => GaussianBarnesCanonicalHead.data
local notation "Pcap" => GaussianBarnesCanonicalDiskBound.prefactorBound
local notation "Hcap" => GaussianBarnesCanonicalHead.cap
local notation "Pgain" => GaussianBarnesCanonicalPrefactorLipschitz.gain
local notation "Hgain" => GaussianBarnesCanonicalHeadLipschitz.gain

def gain (R N : PTm n) : PTm n := Hcap R zero N*Pgain R+Pcap R*Hgain R zero N

private theorem prefactor_bound (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] sampleBound P (pd z B) (Pcap R) := by
  refine .allI ?_
  let s (x : PTm n) := Syn.shift x
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (s z) (s R) (s B) := by
    simpa [Fm.shift,Syn.shift,s] using h.shift
  simpa only [sampleBound,Syn.shift,s,GaussianBarnesCanonicalPrefactor.subst_data,
    GaussianBarnesCanonicalDiskBound.subst_prefactorBound] using
    GaussianBarnesCanonicalDiskBound.prefactor_sample_bound (var 0) (s z) (s R) (s B) hs

private theorem head_bound (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] sampleBound H (hd z R B zero N) (Hcap R zero N) := by
  refine .allI ?_
  let s (x : PTm n) := Syn.shift x
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (s z) (s R) (s B) := by
    simpa [Fm.shift,Syn.shift,s] using h.shift
  simpa only [sampleBound,Syn.shift,s,GaussianBarnesCanonicalHead.subst_data,
    GaussianBarnesCanonicalHead.subst_cap,ConciseIPRA.PTm.subst_zero] using
    GaussianBarnesCanonicalHead.sample_bound (var 0) (s z) (s R) (s B) zero (s N) hs

theorem finite_rate (z w R B D N A K : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source w R D)
    (hK : Γ ⊢[PRAAx] le one K)
    (h : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) A K) :
    Γ ⊢[PRAAx] independentRate prefixF prefixF (literalData z R B N) (literalData w R D N)
      (gain R N*A) K := by
  have hP := GaussianBarnesCanonicalPrefactorLipschitz.independent_rate z w R B D A K hz hw hK h
  have hH := GaussianBarnesCanonicalHeadLipschitz.independent_rate z w R B D zero N A K hz hw hK h
  have mul := multiply_same_denominator P H P H (pd z B) (hd z R B zero N) (pd w D) (hd w R D zero N)
    (Pgain R*A) (Hgain R zero N*A) K (Hcap R zero N) (Pcap R) hK
    (GaussianBarnesCanonicalPrefactor.regular z B) (GaussianBarnesCanonicalHead.regular z R B zero N hz)
    (GaussianBarnesCanonicalPrefactor.regular w D) (GaussianBarnesCanonicalHead.regular w R D zero N hw)
    (head_bound z R B N hz) (prefactor_bound w R D hw) hP hH
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ hK hK
    (le_of_eq_add (d := zero) (by unfold gain; ipra_ring)) mul

def inputClock (R p : PTm n) : PTm n :=
  GaussianFastValueCut.exponent (gain R (cutoff R (p+two))) (p+two)

theorem uniform_input (z w R B D p : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source w R D)
    (h : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) one (unit (inputClock R p))) :
    Γ ⊢[PRAAx] independentRate nameF nameF (data z R B) (data w R D) one (unit p) := by
  let q := p+two
  let N := cutoff R q
  let a := literalData z R B N
  let b := literalData w R D N
  let K := unit q
  have hK := unit_positive (Γ := Γ) q
  have near := finite_rate z w R B D N one (unit (inputClock R p)) hz hw (unit_positive _) h
  have paid : Γ ⊢[PRAAx] independentRate prefixF prefixF a b (gain R N) (unit (inputClock R p)) :=
    GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (unit_positive _) (unit_positive _)
      (le_of_eq_add (d := zero) (by ipra_ring)) near
  have finite := unit_rate_after prefixF prefixF a b (gain R N) (inputClock R p) q (le_refl _) paid
  have first := symmetric prefixF nameF a (data z R B) one K hK (uniform_rate z R B q N hz (le_refl _))
  have last := uniform_rate w R D q N hw (le_refl _)
  have joined := same_denominator nameF prefixF nameF (data z R B) b (data w R D) (one+one) K one hK
    (same_denominator nameF prefixF prefixF (data z R B) a b one K one hK first finite) last
  have clockEq : Γ ⊢[PRAAx] K ≐ unit p*(two*two) :=
    (pw_add two p two).eqTrans (congrMul (.eqRefl _) ((pw_succ two one).eqTrans (congrMul (pw_one two) (.eqRefl _))))
  exact GaussianNamedRateRadius.weaken nameF nameF _ _ _ K one (unit p) hK (unit_positive p)
    (le_congr (.eqRefl _) (congrMul (.eqRefl one) clockEq).eqSymm
      (le_of_eq_add (d := unit p) (by ipra_ring))) joined

theorem actual_Barnes_uniform_disk_continuity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (let z := var 0
     let w := var 1
     let R := var 2
     let B := var 3
     let D := var 4
     let p := var 5
     (source z R B ⋏ source w R D) ⟶
       distanceBounded (ofGaussian z B) (ofGaussian w D) one (unit (inputClock R p)) ⟶
       independentRate nameF nameF (data z R B) (data w R D) one (unit p)) :=
  closeUniv 6 (.impI (.impI (uniform_input _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalUniformContinuity
