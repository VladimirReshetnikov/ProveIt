import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.ProductCoefficients.GaussianBarnesCanonicalTaylorProductDerivativeName
import IPRADerivations.Analysis.Barnes.Taylor.CenteredCharts.GaussianBarnesCanonicalFiniteCentralExponential

/-!
# Late readback with the actual finite Barnes central exponential

The literal finite central exponential and the retained polynomial use
a common tail cutoff. A separate prefactor precision remains free.
One computed dyadic demand controls the full factorially scaled
readback, including the independent central scalar error.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorProductFiniteDerivativeRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalTaylorProductDerivativeName (nameF data errorNumerator)
open GaussianBarnesCanonicalExponentTaylorRetainedCoefficient (precision cutoff)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (exponent query_budget)
open GaussianGammaCanonicalExponent (constantF)
open GaussianNameArithmetic (multiplyF)
open GaussianNamedInverseRate (independentRate)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev finiteF : PR 2 := multiplyF GaussianBarnesCanonicalFiniteCentralExponential.finiteNameF constantF

def finiteData (q z R B r M e : PTm n) : PTm n :=
  GaussianBarnesCanonicalTaylorProductDerivativeName.finiteData GaussianBarnesCanonicalFiniteCentralExponential.finiteNameF
    (GaussianBarnesCanonicalFiniteCentralExponential.finiteData z R B r) q z R B r M e

def demand (p z R B M e : PTm n) : PTm n := exponent (errorNumerator z R B M e one) p

def ready (p z R B M e q r : PTm n) : Fm PTm n :=
  GaussianBarnesCanonicalTaylorProductCoefficientName.ready (demand p z R B M e) z R B M e q r ⋏
    le (GaussianBarnesCanonicalFiniteCentralExponential.cutoff (demand p z R B M e) z R B) r

def prefactorClock (p z R B M e : PTm n) : PTm n :=
  precision (GaussianBarnesCanonicalTaylorProductCoefficientName.clock (demand p z R B M e) z R B M e) R

def tailCutoff (p z R B M e : PTm n) : PTm n :=
  cutoff (GaussianBarnesCanonicalTaylorProductCoefficientName.clock (demand p z R B M e) z R B M e) R M+
    GaussianBarnesCanonicalFiniteCentralExponential.cutoff (demand p z R B M e) z R B

theorem finite_regular (q z R B r M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN finiteF (finiteData q z R B r M e) :=
  GaussianNameArithmetic.multiply_fast _ _ _ _ (GaussianBarnesCanonicalFiniteCentralExponential.finite_regular z R B r hz)
    (GaussianGammaCanonicalExponent.constant_regular _)

theorem scheduled_ready (p z R B M e : PTm n) : Γ ⊢[PRAAx]
    ready p z R B M e (prefactorClock p z R B M e) (tailCutoff p z R B M e) := by
  let P := demand p z R B M e
  let C := cutoff (GaussianBarnesCanonicalTaylorProductCoefficientName.clock P z R B M e) R M
  let D := GaussianBarnesCanonicalFiniteCentralExponential.cutoff P z R B
  have hs := GaussianBarnesCanonicalTaylorProductCoefficientName.sample_ready (Γ := Γ) P z R B M e
  exact .andI (.andI hs.andE₁ (le_add_right C D)) (le_add_left D C)

theorem rate_at_demand (P q z R B r M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (he : Γ ⊢[PRAAx] le e (previous M)) (hq : Γ ⊢[PRAAx] GaussianBarnesCanonicalTaylorProductCoefficientName.ready P z R B M e q r)
    (hr : Γ ⊢[PRAAx] le (GaussianBarnesCanonicalFiniteCentralExponential.cutoff P z R B) r) :
    Γ ⊢[PRAAx] independentRate nameF finiteF (data z R B M e) (finiteData q z R B r M e)
      (errorNumerator z R B M e one) (unit P) := by
  have scalar := GaussianBarnesCanonicalFiniteCentralExponential.late_rate P z R B r hz hr
  exact GaussianBarnesCanonicalTaylorProductDerivativeName.with_scalar_rate
    GaussianBarnesCanonicalFiniteCentralExponential.finiteNameF P z R B M e q r
    (GaussianBarnesCanonicalFiniteCentralExponential.finiteData z R B r) one hz he hq
    (GaussianBarnesCanonicalFiniteCentralExponential.finite_regular z R B r hz)
    (GaussianNamedRateComposition.symmetric _ _ _ _ _ _ (unit_positive P) scalar)

theorem late_rate (p q z R B r M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (he : Γ ⊢[PRAAx] le e (previous M)) (hs : Γ ⊢[PRAAx] ready p z R B M e q r) :
    Γ ⊢[PRAAx] independentRate nameF finiteF (data z R B M e) (finiteData q z R B r M e) one (unit p) :=
  GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (unit_positive (demand p z R B M e)) (unit_positive p)
    (le_congr (.eqRefl _) (one_mul _).eqSymm (query_budget (errorNumerator z R B M e one) p))
    (rate_at_demand (demand p z R B M e) q z R B r M e hz he hs.andE₁ hs.andE₂)

theorem scheduled_rate (p z R B M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e (previous M)) :
    Γ ⊢[PRAAx] independentRate nameF finiteF (data z R B M e)
      (finiteData (prefactorClock p z R B M e) z R B (tailCutoff p z R B M e) M e) one (unit p) :=
  late_rate p _ z R B _ M e hz he (scheduled_ready p z R B M e)

theorem actual_Barnes_finite_Taylor_derivative_readback_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (let p := var 0
     let q := var 1
     let z := var 2
     let R := var 3
     let B := var 4
     let r := var 5
     let M := var 6
     let e := var 7
     (source z R B ⋏ le e (previous M)) ⟶ ready p z R B M e q r ⟶
       independentRate nameF finiteF (data z R B M e) (finiteData q z R B r M e) one (unit p)) :=
  closeUniv 8 (.impI (.impI (late_rate _ _ _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorProductFiniteDerivativeRate
