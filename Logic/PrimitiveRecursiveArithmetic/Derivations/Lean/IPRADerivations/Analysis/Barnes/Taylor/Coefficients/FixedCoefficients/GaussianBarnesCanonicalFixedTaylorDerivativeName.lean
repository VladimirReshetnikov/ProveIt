import IPRADerivations.Analysis.Barnes.Taylor.CenteredCharts.GaussianBarnesCanonicalFiniteCentralExponentialBound
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.FixedCoefficients.GaussianBarnesCanonicalFixedTaylorCoefficientName
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.ProductCoefficients.GaussianBarnesCanonicalTaylorProductFiniteDerivativeRate

/-!
# Factorially scaled Taylor names at every literal Barnes partial product

At a fixed cutoff, only the prefactor clock varies in the coefficient name.
The literal finite central scalar multiplies its factorial scaling. An
explicit cutoff then compares the entire fixed name with its cofinal
counterpart, with the two observation clocks independent.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFixedTaylorDerivativeName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalCenteredExponentialShift (baseData base_regular)
open GaussianBarnesCanonicalFiniteCentralExponentialBound (centralCap central_samples)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalTaylorProductCoefficientCauchy (productCoefficient)
open GaussianBarnesCanonicalTaylorProductCoefficientName (clock)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianFastValueCut (exponent query_budget)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U all_samples_bounded)
open GaussianNameEquivalence (cross_refl cross_symm)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianNamedUniformRateClosure (productBudget same_denominator_product)
open GaussianRationalNaturalScale (naturalPoint natScale_as_product)
open LeanProofs.IPRA.Analysis.Products (fact)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "C" => constantF
local notation "F" => GaussianBarnesCanonicalFixedTaylorCoefficientName.nameF
local notation "fd" => GaussianBarnesCanonicalFixedTaylorCoefficientName.data
local notation "S" => GaussianBarnesCanonicalFiniteCentralExponential.finiteNameF
local notation "sd" => GaussianBarnesCanonicalFiniteCentralExponential.finiteData
local notation "E" => GaussianRadiusExponentialName.nameF GaussianBarnesCanonicalSingleExponential.exponentF
local notation "L" => GaussianBarnesCanonicalTaylorProductDerivativeName.nameF
local notation "ld" => GaussianBarnesCanonicalTaylorProductDerivativeName.data
local notation "K" => GaussianBarnesCanonicalTaylorProductDerivativeName.coefficientF
local notation "kd" => GaussianBarnesCanonicalTaylorProductDerivativeName.coefficientData
local notation "V" => GaussianBarnesCanonicalTaylorProductFiniteDerivativeRate.finiteF
local notation "vd" => GaussianBarnesCanonicalTaylorProductFiniteDerivativeRate.finiteData

abbrev coefficientF : PR 2 := multiplyF C F

def coefficientData (z R B r M e : PTm n) : PTm n :=
  multiplyData C F (naturalPoint (fact e)) (fd z R B r M e)

abbrev nameF : PR 2 := multiplyF S coefficientF

def data (z R B r M e : PTm n) : PTm n :=
  multiplyData S coefficientF (sd z R B r) (coefficientData z R B r M e)

def scaleGain (e : PTm n) : PTm n := U C (naturalPoint (fact e))

def readbackGain (z R B e : PTm n) : PTm n :=
  centralCap z R B*(scaleGain e*(one+one))

def comparisonGain (z R B M e : PTm n) : PTm n :=
  productBudget one (scaleGain e*(one+(one+one))) (U K (kd z R B M e)) (U E (baseData z R B))

def demand (p z R B M e : PTm n) : PTm n := exponent (comparisonGain z R B M e) p

def cutoff (p z R B M e : PTm n) : PTm n :=
  GaussianBarnesCanonicalExponentTaylorRetainedCoefficient.cutoff (clock (demand p z R B M e) z R B M e) R M+
    GaussianBarnesCanonicalFiniteCentralExponential.cutoff (demand p z R B M e) z R B

theorem coefficient_regular (z R B r M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e (previous M)) :
    Γ ⊢[PRAAx] pointCN coefficientF (coefficientData z R B r M e) :=
  multiply_fast _ _ _ _ (constant_regular _) (GaussianBarnesCanonicalFixedTaylorCoefficientName.regular z R B r M e hz he)

theorem regular (z R B r M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e (previous M)) :
    Γ ⊢[PRAAx] pointCN nameF (data z R B r M e) :=
  multiply_fast _ _ _ _ (GaussianBarnesCanonicalFiniteCentralExponential.finite_regular z R B r hz)
    (coefficient_regular z R B r M e hz he)

/-- Multiplication by the same first factor preserves an independent rate. -/
private theorem multiply_same_left (A B G : PR 2) (a x y J D M : PTm n)
    (ha : Γ ⊢[PRAAx] pointCN A a) (hx : Γ ⊢[PRAAx] pointCN B x) (hy : Γ ⊢[PRAAx] pointCN G y)
    (hd : Γ ⊢[PRAAx] le one D) (hM : Γ ⊢[PRAAx] sampleBound A a M)
    (hr : Γ ⊢[PRAAx] independentRate B G x y J D) :
    Γ ⊢[PRAAx] independentRate (multiplyF A B) (multiplyF A G) (multiplyData A B a x) (multiplyData A G a y)
      (M*J) D := by
  have raw := GaussianNamedMultiplyRate.independent_rate A B A G a x a y zero one J D (U B x) M
    (le_refl one) hd ha hx ha hy (all_samples_bounded B x hx) hM
    (GaussianNamedDifferenceRate.self_rate A a ha) hr
  exact GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _
    (by unfold GaussianNamedMultiplyRate.leadingNumerator; ipra_ring) (one_mul D) raw

theorem readback_rate (p q z R B r M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (he : Γ ⊢[PRAAx] le e (previous M)) (hq : Γ ⊢[PRAAx] GaussianBarnesCanonicalFixedTaylorCoefficientName.ready p z R B M e q) :
    Γ ⊢[PRAAx] independentRate nameF V (data z R B r M e) (vd q z R B r M e)
      (readbackGain z R B e) (unit p) := by
  let x := fd z R B r M e
  let y := productCoefficient q z R B r M e
  let a := naturalPoint (fact e)
  let v := GaussianBarnesCanonicalTaylorProductDerivativeName.finiteCoefficient q z R B r M e
  let d := unit p
  have hx := GaussianBarnesCanonicalFixedTaylorCoefficientName.regular z R B r M e hz he
  have ha := constant_regular (Γ := Γ) a
  have raw := multiply_same_left C F C a x y (one+one) d (scaleGain e) ha hx (constant_regular y) (unit_positive p)
    (all_samples_bounded C a ha)
    (GaussianBarnesCanonicalFixedTaylorCoefficientName.finite_rate p z R B r M e q hz he hq)
  have exactScale := GaussianGammaDigammaTwoShiftNamedSize.constant_product (Γ := Γ)
    a y v (natScale_as_product (fact e) y).eqSymm
  have scaled : Γ ⊢[PRAAx] independentRate coefficientF C (coefficientData z R B r M e) v (scaleGain e*(one+one)) d :=
    GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _ (unit_positive p) raw
      (cross_refl _ _ (coefficient_regular z R B r M e hz he)) (cross_symm _ _ _ _ exactScale)
  exact multiply_same_left S coefficientF C (sd z R B r) (coefficientData z R B r M e) v _ _ (centralCap z R B)
    (GaussianBarnesCanonicalFiniteCentralExponential.finite_regular z R B r hz)
    (coefficient_regular z R B r M e hz he) (constant_regular v) (unit_positive p) (central_samples z R B r hz) scaled

theorem comparison_rate (p z R B r M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e (previous M))
    (hc : Γ ⊢[PRAAx] le (GaussianBarnesCanonicalExponentTaylorRetainedCoefficient.cutoff (clock p z R B M e) R M) r)
    (hs : Γ ⊢[PRAAx] le (GaussianBarnesCanonicalFiniteCentralExponential.cutoff p z R B) r) :
    Γ ⊢[PRAAx] independentRate L nameF (ld z R B M e) (data z R B r M e) (comparisonGain z R B M e) (unit p) := by
  let T := GaussianBarnesCanonicalTaylorProductCoefficientName.nameF
  let x := GaussianBarnesCanonicalTaylorProductCoefficientName.data z R B M e
  let y := fd z R B r M e
  let a := naturalPoint (fact e)
  have hx := GaussianBarnesCanonicalTaylorProductCoefficientName.regular z R B M e hz he
  have hy := GaussianBarnesCanonicalFixedTaylorCoefficientName.regular z R B r M e hz he
  have ha := constant_regular (Γ := Γ) a
  have factorialRate := multiply_same_left C T F a x y (one+(one+one)) (unit p) (scaleGain e)
    ha hx hy (unit_positive p) (all_samples_bounded C a ha)
    (GaussianBarnesCanonicalFixedTaylorCoefficientName.cofinal_rate p z R B r M e hz he hc)
  have hb := base_regular z R B hz
  have hk := GaussianBarnesCanonicalTaylorProductDerivativeName.coefficient_regular z R B M e hz he
  have tailRate := GaussianBarnesCanonicalFiniteCentralExponential.late_rate p z R B r hz hs
  exact same_denominator_product E K S coefficientF (baseData z R B) (kd z R B M e) (sd z R B r) (coefficientData z R B r M e)
    one (scaleGain e*(one+(one+one))) (unit p) (U K (kd z R B M e)) (U E (baseData z R B)) (unit_positive p) hb hk
    (GaussianBarnesCanonicalFiniteCentralExponential.finite_regular z R B r hz) (coefficient_regular z R B r M e hz he)
    (all_samples_bounded _ _ hk) (all_samples_bounded _ _ hb)
    (GaussianNamedRateComposition.symmetric _ _ _ _ _ _ (unit_positive p) tailRate) factorialRate

theorem late_rate (p z R B r M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (he : Γ ⊢[PRAAx] le e (previous M)) (hr : Γ ⊢[PRAAx] le (cutoff p z R B M e) r) :
    Γ ⊢[PRAAx] independentRate L nameF (ld z R B M e) (data z R B r M e) one (unit p) := by
  let q := demand p z R B M e
  let a := GaussianBarnesCanonicalExponentTaylorRetainedCoefficient.cutoff (clock q z R B M e) R M
  let b := GaussianBarnesCanonicalFiniteCentralExponential.cutoff q z R B
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (unit_positive q) (unit_positive p)
    (le_congr (.eqRefl _) (one_mul _).eqSymm (query_budget (comparisonGain z R B M e) p))
    (comparison_rate q z R B r M e hz he (le_trans (le_add_right a b) hr) (le_trans (le_add_left b a) hr))

theorem actual_Barnes_fixed_cutoff_factorial_coefficient_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((source (var 0) (var 1) (var 2) ⋏ le (var 5) (previous (var 4))) ⟶
      pointCN nameF (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (regular _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_Barnes_fixed_cutoff_factorial_coefficient_convergence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let p := var 0
     let z := var 1
     let R := var 2
     let B := var 3
     let r := var 4
     let M := var 5
     let e := var 6
     (source z R B ⋏ le e (previous M)) ⟶ le (cutoff p z R B M e) r ⟶
       independentRate L nameF (ld z R B M e) (data z R B r M e) one (unit p)) :=
  closeUniv 7 (.impI (.impI (late_rate _ _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFixedTaylorDerivativeName
