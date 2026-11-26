import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalCentralUniformBound
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalFixedTaylorDerivativeName
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalFixedTaylorUniformConvergence
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalTaylorProductUniformMass

/-!
# Disk-uniform convergence with the original factorial and central scalar

The fixed and cofinal coefficient names are multiplied by the same
factorial. The actual finite central exponential approaches the actual
cofinal scalar at a disk-only cutoff. Uniform bounds on both original
factors yield a single cutoff for the factorially scaled derivative name.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFixedTaylorDerivativeUniformConvergence

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalCenteredExponentialShift (baseData base_regular)
open GaussianBarnesCanonicalCentralUniformBound (centralCap central_samples prefixUGain prefix_U_le)
open GaussianBarnesCanonicalFixedTaylorDerivativeName (scaleGain)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (exponent query_budget)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameBounds (all_samples_bounded)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianNamedUniformRateClosure (productBudget same_denominator_product)
open GaussianRationalNaturalScale (naturalPoint)
open LeanProofs.IPRA.Analysis.Products (fact)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "C" => GaussianBarnesCanonicalTaylorProductCoefficientName.nameF
local notation "cd" => GaussianBarnesCanonicalTaylorProductCoefficientName.data
local notation "F" => GaussianBarnesCanonicalFixedTaylorCoefficientName.nameF
local notation "fd" => GaussianBarnesCanonicalFixedTaylorCoefficientName.data
local notation "D" => GaussianBarnesCanonicalTaylorProductDerivativeName.nameF
local notation "dd" => GaussianBarnesCanonicalTaylorProductDerivativeName.data
local notation "G" => GaussianBarnesCanonicalFixedTaylorDerivativeName.nameF
local notation "gd" => GaussianBarnesCanonicalFixedTaylorDerivativeName.data
local notation "K" => GaussianBarnesCanonicalTaylorProductDerivativeName.coefficientF
local notation "kd" => GaussianBarnesCanonicalTaylorProductDerivativeName.coefficientData
local notation "J" => GaussianBarnesCanonicalFixedTaylorDerivativeName.coefficientF
local notation "jd" => GaussianBarnesCanonicalFixedTaylorDerivativeName.coefficientData
local notation "E" => GaussianRadiusExponentialName.nameF GaussianBarnesCanonicalSingleExponential.exponentF
local notation "S" => GaussianBarnesCanonicalFiniteCentralExponential.finiteNameF
local notation "sd" => GaussianBarnesCanonicalFiniteCentralExponential.finiteData
local notation "rawCap" => GaussianBarnesCanonicalTaylorProductUniformMass.cap
local notation "coefficientCutoff" => GaussianBarnesCanonicalTaylorProductUniformGap.cutoff

def factorialCap (R M e : PTm n) : PTm n := scaleGain e*rawCap R M
def scalarCutoff (p R : PTm n) : PTm n :=
  (prefixUGain R*GaussianBarnesCanonicalTailExponential.errorNumerator R)*unit p
def comparisonGain (R M e : PTm n) : PTm n := productBudget one (scaleGain e) (factorialCap R M e) (centralCap R)
def demand (p R M e : PTm n) : PTm n := exponent (comparisonGain R M e) p
def cutoff (p R M e : PTm n) : PTm n :=
  coefficientCutoff (demand p R M e) R M e+scalarCutoff (demand p R M e) R

theorem original_scalar_cutoff_le (p z R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] le (GaussianBarnesCanonicalFiniteCentralExponential.cutoff p z R B) (scalarCutoff p R) :=
  mul_le_mul_right (unit p)
    (mul_le_mul_right (GaussianBarnesCanonicalTailExponential.errorNumerator R) (prefix_U_le z R B hz))

theorem factorial_samples (z R B M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (he : Γ ⊢[PRAAx] le e (previous M)) : Γ ⊢[PRAAx] sampleBound K (kd z R B M e) (factorialCap R M e) :=
  GaussianNamedBoundedProductObservation.sample_bounds constantF C (naturalPoint (fact e)) (cd z R B M e)
    (scaleGain e) (rawCap R M) (all_samples_bounded _ _ (constant_regular _))
    (GaussianBarnesCanonicalTaylorProductUniformMass.cofinal_samples z R B M e hz he)

theorem factorial_rate (p z R B r M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (he : Γ ⊢[PRAAx] le e (previous M)) (hr : Γ ⊢[PRAAx] le (coefficientCutoff p R M e) r) : Γ ⊢[PRAAx]
    independentRate K J (kd z R B M e) (jd z R B r M e) (scaleGain e) (unit p) := by
  let a := naturalPoint (fact e)
  let x := cd z R B M e
  let y := fd z R B r M e
  have ha := constant_regular (Γ := Γ) a
  have hx := GaussianBarnesCanonicalTaylorProductCoefficientName.regular z R B M e hz he
  have hy := GaussianBarnesCanonicalFixedTaylorCoefficientName.regular z R B r M e hz he
  have raw := GaussianNamedMultiplyRate.independent_rate constantF C constantF F a x a y
    zero one one (unit p) (rawCap R M) (scaleGain e) (le_refl one) (unit_positive p) ha hx ha hy
    (GaussianBarnesCanonicalTaylorProductUniformMass.cofinal_samples z R B M e hz he) (all_samples_bounded _ _ ha)
    (GaussianNamedDifferenceRate.self_rate _ _ ha)
    (GaussianBarnesCanonicalFixedTaylorUniformConvergence.cofinal_rate p z R B r M e hz he hr)
  exact GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _
    (by unfold GaussianNamedMultiplyRate.leadingNumerator; ipra_ring) (one_mul _) raw

theorem comparison_rate (p z R B r M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (he : Γ ⊢[PRAAx] le e (previous M)) (hC : Γ ⊢[PRAAx] le (coefficientCutoff p R M e) r)
    (hS : Γ ⊢[PRAAx] le (scalarCutoff p R) r) : Γ ⊢[PRAAx]
    independentRate D G (dd z R B M e) (gd z R B r M e) (comparisonGain R M e) (unit p) := by
  have scalar := GaussianBarnesCanonicalFiniteCentralExponential.late_rate p z R B r hz
    (le_trans (original_scalar_cutoff_le p z R B hz) hS)
  exact same_denominator_product E K S J (baseData z R B) (kd z R B M e) (sd z R B r) (jd z R B r M e)
    one (scaleGain e) (unit p) (factorialCap R M e) (centralCap R) (unit_positive p)
    (base_regular z R B hz)
    (GaussianBarnesCanonicalTaylorProductDerivativeName.coefficient_regular z R B M e hz he)
    (GaussianBarnesCanonicalFiniteCentralExponential.finite_regular z R B r hz)
    (GaussianBarnesCanonicalFixedTaylorDerivativeName.coefficient_regular z R B r M e hz he)
    (factorial_samples z R B M e hz he) (central_samples z R B hz)
    (GaussianNamedRateComposition.symmetric _ _ _ _ _ _ (unit_positive p) scalar)
    (factorial_rate p z R B r M e hz he hC)

theorem late_rate (p z R B r M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (he : Γ ⊢[PRAAx] le e (previous M)) (hr : Γ ⊢[PRAAx] le (cutoff p R M e) r) : Γ ⊢[PRAAx]
    independentRate D G (dd z R B M e) (gd z R B r M e) one (unit p) := by
  let q := demand p R M e
  let a := coefficientCutoff q R M e
  let b := scalarCutoff q R
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (unit_positive q) (unit_positive p)
    (le_congr (.eqRefl _) (one_mul _).eqSymm (query_budget (comparisonGain R M e) p))
    (comparison_rate q z R B r M e hz he (le_trans (le_add_right a b) hr) (le_trans (le_add_left b a) hr))

theorem actual_Barnes_fixed_Taylor_derivative_disk_uniform_convergence_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let p := var 0
     let z := var 1
     let R := var 2
     let B := var 3
     let r := var 4
     let M := var 5
     let e := var 6
     (source z R B ⋏ le e (previous M)) ⟶ le (cutoff p R M e) r ⟶
       independentRate D G (dd z R B M e) (gd z R B r M e) one (unit p)) :=
  closeUniv 7 (.impI (.impI (late_rate (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)
    Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFixedTaylorDerivativeUniformConvergence
