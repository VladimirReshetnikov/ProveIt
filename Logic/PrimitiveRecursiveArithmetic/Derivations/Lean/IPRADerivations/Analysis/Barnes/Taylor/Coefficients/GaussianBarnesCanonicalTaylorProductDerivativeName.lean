import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalTaylorProductCoefficientName
import IPRADerivations.Analysis.Names.Scaling.GaussianNamedNaturalScale
import IPRADerivations.Analysis.Names.Rates.GaussianNamedUniformRateClosure

/-!
# Factorially scaled Barnes Taylor coefficients with the original scalar

The retained coefficient is multiplied by its order factorial and by
the actual centered exponential. A finite central scalar may have its
own convergence rate, independent of the prefactor and tail clocks
used to compute the retained finite coefficient.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorProductDerivativeName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalCenteredExponentialShift (baseData base_regular)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalTaylorProductCoefficientCauchy (productCoefficient)
open GaussianBarnesCanonicalTaylorProductCoefficientName (ready)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U all_samples_bounded)
open GaussianNameEquivalence (cross_refl cross_symm)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianNamedUniformRateClosure (productBudget same_denominator_product)
open GaussianRationalNaturalScale (naturalPoint natScale natScale_as_product)
open LeanProofs.IPRA.Analysis.Products (fact)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "C" => constantF
local notation "K" => GaussianBarnesCanonicalTaylorProductCoefficientName.nameF
local notation "kd" => GaussianBarnesCanonicalTaylorProductCoefficientName.data
local notation "E" => GaussianRadiusExponentialName.nameF GaussianBarnesCanonicalSingleExponential.exponentF

def finiteCoefficient (q z R B r M e : PTm n) : PTm n :=
  natScale (fact e) (productCoefficient q z R B r M e)

abbrev coefficientF : PR 2 := multiplyF C K

def coefficientData (z R B M e : PTm n) : PTm n :=
  multiplyData C K (naturalPoint (fact e)) (kd z R B M e)

abbrev nameF : PR 2 := multiplyF E coefficientF

def data (z R B M e : PTm n) : PTm n := multiplyData E coefficientF (baseData z R B) (coefficientData z R B M e)

def finiteData (G : PR 2) (y q z R B r M e : PTm n) : PTm n :=
  multiplyData G C y (finiteCoefficient q z R B r M e)

def errorNumerator (z R B M e A : PTm n) : PTm n :=
  productBudget A (fact e) (U coefficientF (coefficientData z R B M e)) (U E (baseData z R B))

private theorem natural_constant_bound (i : PTm n) : Γ ⊢[PRAAx] sampleBound C (naturalPoint i) i := by
  refine .allI ?_
  simpa [sampleBound,Syn.shift] using
    GaussianRationalReciprocal.bound_congr (constant_at (var 0) (naturalPoint (Syn.shift i))).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianNamedNaturalScale.natural_point_bound (Syn.shift i))

theorem coefficient_regular (z R B M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e (previous M)) :
    Γ ⊢[PRAAx] pointCN coefficientF (coefficientData z R B M e) :=
  multiply_fast _ _ _ _ (constant_regular _) (GaussianBarnesCanonicalTaylorProductCoefficientName.regular z R B M e hz he)

theorem regular (z R B M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e (previous M)) :
    Γ ⊢[PRAAx] pointCN nameF (data z R B M e) :=
  multiply_fast _ _ _ _ (base_regular z R B hz) (coefficient_regular z R B M e hz he)

theorem factorial_rate (P z R B M e q r : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e (previous M))
    (hr : Γ ⊢[PRAAx] ready P z R B M e q r) :
    Γ ⊢[PRAAx] independentRate coefficientF C (coefficientData z R B M e) (finiteCoefficient q z R B r M e) (fact e) (unit P) := by
  let i := fact e
  let a := naturalPoint i
  let x := kd z R B M e
  let y := productCoefficient q z R B r M e
  have ha := constant_regular (Γ := Γ) a
  have hx := GaussianBarnesCanonicalTaylorProductCoefficientName.regular z R B M e hz he
  have hy := constant_regular (Γ := Γ) y
  have raw := GaussianNamedMultiplyRate.independent_rate C K C C a x a y zero one one (unit P) (U K x) i
    (le_refl one) (unit_positive P) ha hx ha hy (all_samples_bounded K x hx) (natural_constant_bound i)
    (GaussianNamedDifferenceRate.self_rate C a ha)
    (GaussianBarnesCanonicalTaylorProductCoefficientName.finite_rate P z R B M e q r hz he hr)
  have reduced := GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ i (unit P)
    (by unfold GaussianNamedMultiplyRate.leadingNumerator; ipra_ring)
    (one_mul _) raw
  exact GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _ (unit_positive P) reduced
    (cross_refl _ _ (coefficient_regular z R B M e hz he))
    (cross_symm _ _ _ _ (GaussianGammaDigammaTwoShiftNamedSize.constant_product a y (natScale i y) (natScale_as_product i y).eqSymm))

theorem with_scalar_rate (G : PR 2) (P z R B M e q r y A : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e (previous M)) (hr : Γ ⊢[PRAAx] ready P z R B M e q r)
    (hG : Γ ⊢[PRAAx] pointCN G y) (hscalar : Γ ⊢[PRAAx] independentRate E G (baseData z R B) y A (unit P)) :
    Γ ⊢[PRAAx] independentRate nameF (multiplyF G C) (data z R B M e) (finiteData G y q z R B r M e)
      (errorNumerator z R B M e A) (unit P) := by
  have hx := base_regular z R B hz
  have hk := coefficient_regular z R B M e hz he
  exact same_denominator_product E coefficientF G C (baseData z R B) (coefficientData z R B M e) y
    (finiteCoefficient q z R B r M e) A (fact e) (unit P) _ _ (unit_positive P) hx hk hG
    (constant_regular _) (all_samples_bounded _ _ hk) (all_samples_bounded _ _ hx) hscalar
    (factorial_rate P z R B M e q r hz he hr)

theorem centered_rate (P z R B M e q r : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e (previous M))
    (hr : Γ ⊢[PRAAx] ready P z R B M e q r) :
    Γ ⊢[PRAAx] independentRate nameF (multiplyF E C) (data z R B M e)
      (finiteData E (baseData z R B) q z R B r M e) (errorNumerator z R B M e zero) (unit P) := by
  have he' := base_regular z R B hz
  have hr' := GaussianNamedRateRadius.weaken E E (baseData z R B) (baseData z R B) zero one zero (unit P)
    (le_refl one) (unit_positive P) (le_congr (zero_mul _).eqSymm (zero_mul _).eqSymm (le_refl zero))
    (GaussianNamedDifferenceRate.self_rate E (baseData z R B) he')
  exact with_scalar_rate E P z R B M e q r (baseData z R B) zero hz he hr he' hr'

theorem actual_Barnes_factorially_scaled_Taylor_coefficient_regular_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((source (var 0) (var 1) (var 2) ⋏ le (var 4) (previous (var 3))) ⟶
      pointCN nameF (data (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (regular _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_Barnes_factorially_scaled_Taylor_coefficient_readback_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (let P := var 0
     let z := var 1
     let R := var 2
     let B := var 3
     let M := var 4
     let e := var 5
     let q := var 6
     let r := var 7
     (source z R B ⋏ le e (previous M)) ⟶ ready P z R B M e q r ⟶
       independentRate nameF (multiplyF E C) (data z R B M e)
         (finiteData E (baseData z R B) q z R B r M e) (errorNumerator z R B M e zero) (unit P)) :=
  closeUniv 8 (.impI (.impI (centered_rate _ _ _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorProductDerivativeName
