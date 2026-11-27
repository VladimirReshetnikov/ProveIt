import IPRADerivations.Analysis.Barnes.CanonicalProducts.GaussianBarnesCanonicalProduct
import IPRADerivations.Analysis.Barnes.Taylor.CenteredCharts.GaussianBarnesCanonicalCenteredExponentialShift

/-!
# The central exponential of the literal finite Barnes products

Separate the exact kept powers from the prefactor, head correction and
actual finite logarithmic tail. The central exponential approaches the
original cofinal central exponential at an independent-clock rate.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteCentralExponential

open_ipra
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalBaseProductShift (powerProduct)
open GaussianBarnesCanonicalCenteredExponentialShift (baseData head)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial initial_positive)
open GaussianBarnesCanonicalLogTail (tailDenominator tail_denominator_positive)
open GaussianBarnesCanonicalSingleExponential
  (prefixF prefixData prefix_regular prefix_factorization exponentF exponentData exponent_regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaFiniteApproximantName (exponentialInputData exponential_input)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U all_samples_bounded)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedInverseRate (independentRate)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "E" => GaussianRadiusExponentialName.nameF
local notation "T" => GaussianBarnesCanonicalTailExponential.nameF
local notation "F" => GaussianBarnesCanonicalTailExponential.finiteF
local notation "td" => GaussianBarnesCanonicalTailExponential.data
local notation "fd" => GaussianBarnesCanonicalTailExponential.finiteData
local notation "C" => constantF

def prefixExpData (z R B : PTm n) : PTm n := exponentialInputData prefixF (prefixData z R B)

abbrev finiteNameF : PR 2 := multiplyF (E prefixF) F

def finiteData (z R B r : PTm n) : PTm n :=
  multiplyData (E prefixF) F (prefixExpData z R B) (fd z R B (initial R) r)

def errorNumerator (z R B : PTm n) : PTm n :=
  U (E prefixF) (prefixExpData z R B)*GaussianBarnesCanonicalTailExponential.errorNumerator R

def cutoff (p z R B : PTm n) : PTm n := errorNumerator z R B*unit p

theorem prefix_exp_regular (z R B : PTm n) :
    Γ ⊢[PRAAx] pointCN (E prefixF) (prefixExpData z R B) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (exponential_input _ _ (prefix_regular z R B))

theorem finite_regular (z R B r : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] pointCN finiteNameF (finiteData z R B r) :=
  multiply_fast _ _ _ _ (prefix_exp_regular z R B)
    (GaussianBarnesCanonicalTailExponential.finite_regular z R B (initial R) r
      (GaussianBarnesCanonicalLogCofinalRate.initial_source z R B hz))

private theorem cofinal_cross (z R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF (E prefixF) T) (E exponentF)
      (multiplyData (E prefixF) T (prefixExpData z R B) (td z R B)) (baseData z R B) := by
  have hr := exponent_regular z R B hz
  exact GaussianGammaFoldedApproximantBalance.exponential_product_equivalent prefixF
    GaussianBarnesCanonicalLogCofinal.nameF exponentF
    (U prefixF (prefixData z R B)) (GaussianBarnesCanonicalFiniteLog.radius R) (U exponentF (exponentData z R B))
    (prefixData z R B) (GaussianBarnesCanonicalLogCofinal.data z R B) (exponentData z R B)
    (exponential_input _ _ (prefix_regular z R B)) (GaussianBarnesCanonicalTailExponential.log_input z R B hz)
    (exponential_input _ _ hr) (cross_refl _ _ hr)

theorem tail_rate (z R B r : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] independentRate finiteNameF (E exponentF) (finiteData z R B r) (baseData z R B)
      (errorNumerator z R B) (tailDenominator (initial R+r)) := by
  let x := prefixExpData z R B
  let y := fd z R B (initial R) r
  let t := td z R B
  let M := U F y
  let K := U (E prefixF) x
  let A := GaussianBarnesCanonicalTailExponential.errorNumerator R
  let D := tailDenominator (initial R+r)
  have hx := prefix_exp_regular (Γ := Γ) z R B
  have hy := GaussianBarnesCanonicalTailExponential.finite_regular z R B (initial R) r
    (GaussianBarnesCanonicalLogCofinalRate.initial_source z R B hz)
  have ht := GaussianBarnesCanonicalTailExponential.regular z R B hz
  have hd := tail_denominator_positive (Γ := Γ) (initial R+r) (le_trans (initial_positive R) (le_add_right _ _))
  have raw := GaussianNamedMultiplyRate.independent_rate (E prefixF) F (E prefixF) T x y x t zero one A D M K
    (le_refl one) hd hx hy hx ht (all_samples_bounded F y hy) (all_samples_bounded (E prefixF) x hx)
    (GaussianNamedDifferenceRate.self_rate _ _ hx) (GaussianBarnesCanonicalTailExponential.exponential_tail_rate z R B r hz)
  have reduced := GaussianNamedDifferenceRate.rate_parameters_congr finiteNameF (multiplyF (E prefixF) T)
    (finiteData z R B r) (multiplyData (E prefixF) T x t) _ _ (errorNumerator z R B) D
    (by change Γ ⊢[PRAAx] (M*zero*D+K*A*one) ≐ K*A; ipra_ring) (one_mul D) raw
  exact GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _ hd reduced
    (cross_refl _ _ (finite_regular z R B r hz))
    (cross_symm _ _ _ _ (cofinal_cross z R B hz))

theorem late_rate (p z R B r : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hr : Γ ⊢[PRAAx] le (cutoff p z R B) r) :
    Γ ⊢[PRAAx] independentRate finiteNameF (E exponentF) (finiteData z R B r) (baseData z R B) one (unit p) := by
  let a := initial R
  have hd := tail_denominator_positive (Γ := Γ) (a+r) (le_trans (initial_positive R) (le_add_right _ _))
  have fit : Γ ⊢[PRAAx] le (cutoff p z R B) (one*tailDenominator (a+r)) :=
    le_trans hr (le_of_eq_add (d := num 3*a+two*r) (by unfold tailDenominator; ipra_ring))
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ hd (unit_positive p) fit (tail_rate z R B r hz)

theorem literal_factorization (z R B r : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] crossEquivalent GaussianBarnesCanonicalValue.prefixF (multiplyF C finiteNameF)
      (GaussianBarnesCanonicalProduct.literalData z R B (initial R+r))
      (multiplyData C finiteNameF (powerProduct z B (initial R)) (finiteData z R B r)) := by
  let x := prefixExpData z R B
  let y := fd z R B (initial R) r
  let w := powerProduct z B (initial R)
  have hx := prefix_exp_regular (Γ := Γ) z R B
  have hy := GaussianBarnesCanonicalTailExponential.finite_regular z R B (initial R) r
    (GaussianBarnesCanonicalLogCofinalRate.initial_source z R B hz)
  have hw := constant_regular (Γ := Γ) w
  have literal := GaussianBarnesCanonicalProduct.finite_cross z R B r hz
  have small := multiply_cross GaussianBarnesCanonicalValue.prefixF (multiplyF C (E prefixF)) F F
    (GaussianBarnesCanonicalValue.prefixData z R B) (multiplyData C (E prefixF) w x) y y
    (GaussianBarnesCanonicalValue.prefix_regular z R B hz) (multiply_fast _ _ _ _ hw hx) hy hy
    (prefix_factorization z R B hz) (cross_refl _ _ hy)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ literal)
    (cross_trans _ _ _ _ _ _ small (GaussianNameRingLaws.multiply_associative C (E prefixF) F w x y hw hx hy))

theorem shifted_factorization (z h R B r : PTm n) (hw : Γ ⊢[PRAAx] source (add z h) R B) :
    Γ ⊢[PRAAx] crossEquivalent GaussianBarnesCanonicalValue.prefixF (multiplyF C finiteNameF)
      (GaussianBarnesCanonicalProduct.literalData (add z h) R B (initial R+r))
      (multiplyData C finiteNameF (head z h R B) (finiteData (add z h) R B r)) := by
  let w := add z h
  let v := finiteData w R B r
  have changeHead : Γ ⊢[PRAAx] multiplyData C finiteNameF (powerProduct w B (initial R)) v ≐
      multiplyData C finiteNameF (head z h R B) v := by
    dsimp only [w, head]
    ipra_congr (multiplyData C finiteNameF (var 0) (var 1) : PTm 2) with
      [(GaussianBarnesCanonicalCenteredHead.original_evaluation z h B (initial R) hw.andE₁).eqSymm, .eqRefl v]
  exact GaussianGammaCompactCutoffAlignment.cross_data_congr _ _ _ _ _ _ (.eqRefl _) changeHead
    (literal_factorization w R B r hw)

theorem actual_Barnes_finite_central_exponential_late_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let p := var 0
     let z := var 1
     let R := var 2
     let B := var 3
     let r := var 4
     source z R B ⟶ le (cutoff p z R B) r ⟶
       independentRate finiteNameF (E exponentF) (finiteData z R B r) (baseData z R B) one (unit p)) :=
  closeUniv 5 (.impI (.impI (late_rate _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_Barnes_finite_product_centered_factorization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     let r := var 4
     let w := add z h
     source w R B ⟶ crossEquivalent GaussianBarnesCanonicalValue.prefixF (multiplyF C finiteNameF)
       (GaussianBarnesCanonicalProduct.literalData w R B (initial R+r))
       (multiplyData C finiteNameF (head z h R B) (finiteData w R B r))) :=
  closeUniv 5 (.impI (shifted_factorization _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteCentralExponential
