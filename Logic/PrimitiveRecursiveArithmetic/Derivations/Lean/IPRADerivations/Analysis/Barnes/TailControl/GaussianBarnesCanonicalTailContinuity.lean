import IPRADerivations.Analysis.Barnes.Logarithms.FiniteRows.GaussianBarnesCanonicalFiniteLogProduct
import IPRADerivations.Analysis.Barnes.HeadProducts.GaussianBarnesCanonicalHeadLipschitz
import IPRADerivations.Analysis.Barnes.TailControl.GaussianBarnesCanonicalTailExponential
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateTransport
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateComposition
import IPRADerivations.Analysis.Trigonometry.Cyclic.GaussianCyclicExponentialSamples

/-!
# Disk continuity of the original cofinal Barnes tail

The finite logarithmic exponential is identified with the corresponding
literal product range. A uniform cutoff then transfers the finite head
Lipschitz bound to the cofinal tail at explicit input precision.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTailContinuity

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial initial_positive endpoint length initial_length suffix_budget)
open GaussianBarnesCanonicalLogTail (tailDenominator tail_denominator_positive)
open GaussianBarnesCanonicalTailExponential (nameF data finiteF finiteData errorNumerator exponential_tail_rate)
open GaussianBarnesCanonicalLogRow (boundNumerator)
open GaussianBarnesCanonicalFiniteLog (radius)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerNamedPowerScalingPowerFrozen (unit_rate_after)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedRateComposition (same_denominator symmetric)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianNameEquivalence (cross_refl cross_symm)
open GaussianRadiusExponentialLipschitzRate (factor)
open GaussianRationalHorner (ofGaussian)
open GaussianRationalMetric (distanceBounded)
open GaussianFastValueCut (exponent)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "H" => GaussianBarnesCanonicalHead.nameF
local notation "Hd" => GaussianBarnesCanonicalHead.data
local notation "Hgain" => GaussianBarnesCanonicalHeadLipschitz.gain

def cutoffClock (R p : PTm n) : PTm n := exponent (factor (radius R)) p
def cutoffLength (R p : PTm n) : PTm n := length (cutoffClock R p) R

def inputClock (R p : PTm n) : PTm n :=
  exponent (Hgain R (initial R) (cutoffLength R (p+two))) (p+two)

@[simp] theorem subst_inputClock {m : ℕ} (σ : Fin n → PTm m) (R p : PTm n) :
    Syn.subst σ (inputClock R p) = inputClock (Syn.subst σ R) (Syn.subst σ p) := by
  simp [inputClock,cutoffLength,cutoffClock,one,two]

theorem sample_bound (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] sampleBound nameF (data z R B) (factor (radius R)) := by
  refine .allI ?_
  let sh (a : PTm n) := Syn.shift a
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift
  have native := GaussianCyclicExponentialSamples.exponential_bound GaussianBarnesCanonicalLogCofinal.nameF
    (radius (sh R)) (GaussianBarnesCanonicalLogCofinal.data (sh z) (sh R) (sh B)) (var 0)
    (GaussianBarnesCanonicalTailExponential.log_input (sh z) (sh R) (sh B) hs)
  simpa only [sampleBound,GaussianBarnesCanonicalTailExponential.subst_data,GaussianBarnesCanonicalFiniteLog.subst_radius,
    GaussianRadiusExponentialLipschitzRate.subst_factor,GaussianBarnesCanonicalTailExponential.nameF,
    GaussianBarnesCanonicalTailExponential.data,GaussianCyclicExponentialSamples.sampleBound,factor,
    GaussianRadiusExponentialName.subst_data,GaussianBarnesCanonicalLogCofinal.subst_data,
    subst_ap2,PTm.subst_num,Syn.shift,sh,Δ] using native

theorem cutoff_rate (z R B p : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] independentRate H nameF (Hd z R B (initial R) (cutoffLength R p)) (data z R B) one (unit p) := by
  let a := initial R
  let q := cutoffClock R p
  let r := cutoffLength R p
  let N := a+r
  let gain := factor (radius R)
  let C := boundNumerator R
  let K := tailDenominator N
  have hK : Γ ⊢[PRAAx] le one K := tail_denominator_positive N (le_trans (initial_positive R) (le_add_right a r))
  have pay := GaussianFastValueCut.query_budget (Γ := Γ) gain p
  have big : Γ ⊢[PRAAx] le (unit q) (DyadicComplexLogarithm.unit q) :=
    GaussianExponentialReference.unit_monotone (le_add_right q _)
  have den : Γ ⊢[PRAAx] tailDenominator (endpoint q R) ≐ K := by
    unfold tailDenominator K N
    exact congrMul (.eqRefl _) (initial_length q R).eqSymm
  have guard : Γ ⊢[PRAAx] le (errorNumerator R*unit p) (one*K) :=
    le_congr (by unfold errorNumerator gain C; ipra_ring) (congrMul (.eqRefl one) den)
      (le_trans (le_mul_mono (le_refl C) (le_trans pay big)) (suffix_budget q R))
  have approx := GaussianNamedRateRadius.weaken finiteF nameF (finiteData z R B a r) (data z R B)
    (errorNumerator R) K one (unit p) hK (unit_positive p) guard (exponential_tail_rate z R B r h)
  have finite := GaussianBarnesCanonicalFiniteLogProduct.exponential_product_cross z R B a r
    (GaussianBarnesCanonicalLogCofinalRate.initial_source z R B h)
  exact GaussianNamedRateTransport.transport finiteF nameF H nameF _ _ _ _ _ _ (unit_positive p) approx
    (cross_symm _ _ _ _ finite) (cross_refl _ _ (GaussianBarnesCanonicalTailExponential.regular z R B h))

theorem uniform_input (z w R B D p : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source w R D)
    (h : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) one (unit (inputClock R p))) :
    Γ ⊢[PRAAx] independentRate nameF nameF (data z R B) (data w R D) one (unit p) := by
  let q := p+two
  let a := initial R
  let r := cutoffLength R q
  let U := unit q
  let L := inputClock R p
  let M := Hgain R a r
  let x := Hd z R B a r
  let y := Hd w R D a r
  have hU := unit_positive (Γ := Γ) q
  have near := GaussianBarnesCanonicalHeadLipschitz.independent_rate z w R B D a r one (unit L)
    hz hw (unit_positive L) h
  have paid : Γ ⊢[PRAAx] independentRate H H x y M (unit L) :=
    GaussianNamedDifferenceRate.rate_parameters_congr H H x y _ _ _ _ (by ipra_ring) (.eqRefl _) near
  have finite := unit_rate_after H H x y M L q (le_refl _) paid
  have first := symmetric H nameF x (data z R B) one U hU (cutoff_rate z R B q hz)
  have last := cutoff_rate w R D q hw
  have joined := same_denominator nameF H nameF (data z R B) y (data w R D) (one+one) U one hU
    (same_denominator nameF H H (data z R B) x y one U one hU first finite) last
  have clockEq : Γ ⊢[PRAAx] U ≐ unit p*(two*two) :=
    (pw_add two p two).eqTrans (congrMul (.eqRefl _) ((pw_succ two one).eqTrans (congrMul (pw_one two) (.eqRefl _))))
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ U one (unit p) hU (unit_positive p)
    (le_congr (.eqRefl _) (congrMul (.eqRefl one) clockEq).eqSymm
      (le_of_eq_add (d := unit p) (by ipra_ring))) joined

theorem actual_Barnes_tail_uniform_disk_continuity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
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

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTailContinuity
