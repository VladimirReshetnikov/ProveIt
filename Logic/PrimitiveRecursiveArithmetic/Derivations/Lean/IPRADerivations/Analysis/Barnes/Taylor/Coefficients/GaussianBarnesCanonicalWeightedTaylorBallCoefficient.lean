import IPRADerivations.Analysis.Barnes.Taylor.TaylorBalls.GaussianBarnesCanonicalWeightedTaylorBall
import IPRADerivations.Analysis.Barnes.Taylor.CenteredCharts.GaussianBarnesCanonicalCentralUniformBound
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.ProductCoefficients.GaussianBarnesCanonicalTaylorProductDerivativeName

/-!
# Factorial derivative readback of the stored weighted Barnes polynomial

The coefficient at the original storage address uses the same finite
exponent buffer, prefactor observation, and tail cutoff as the value
polynomial. The original central scalar then scales the coefficient.
A primitive-recursive observation clock pays both readiness conditions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalWeightedTaylorBallCoefficient

open_ipra
open ComplexLogarithmRemainder (bounded_mono)
open GaussianBarnesCanonicalCenteredExponentialShift (baseData)
open GaussianBarnesCanonicalCentralUniformBound (centralUGain central_U_le)
open GaussianBarnesCanonicalExponentTaylorBallSchedule (precision)
open GaussianBarnesCanonicalExponentTaylorRetainedCoefficient (prefactorGain tailGain)
open GaussianBarnesCanonicalExponentTaylorSchedule (tailCutoff)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalTaylorProductCoefficientCauchy (productCoefficient)
open GaussianBarnesCanonicalTaylorProductCoefficientName (ready)
open GaussianBarnesCanonicalTaylorProductDerivativeName (centered_rate errorNumerator finiteCoefficient)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianFastValueCut (exponent query_budget)
open GaussianGammaCanonicalExponent (constantF)
open GaussianNameArithmetic (multiplyData)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (positive_product)
open GaussianRationalNaturalScale (natScale)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "F" => GaussianBarnesCanonicalTaylorProductDerivativeName.nameF
local notation "fd" => GaussianBarnesCanonicalTaylorProductDerivativeName.data
local notation "E" => GaussianRadiusExponentialName.nameF GaussianBarnesCanonicalSingleExponential.exponentF
local notation "W" => GaussianBarnesCanonicalWeightedTaylorBall.nameF
local notation "polynomial" => GaussianBarnesCanonicalWeightedTaylorBall.polynomial
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def coefficient (p z R B H M e : PTm n) : PTm n :=
  entry (polynomial p z R B H M) (monus (previous M) e)

def data (p z R B H M e : PTm n) : PTm n :=
  multiplyData E constantF (baseData z R B) (natScale (fact e) (coefficient p z R B H M e))

theorem coefficient_at (p z R B H M e : PTm n) :
    Γ ⊢[PRAAx] coefficient p z R B H M e ≐ productCoefficient (precision p R H) z R B (tailCutoff p R) M e :=
  .eqRefl _

theorem rate_of_ready (P p z R B H M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (he : Γ ⊢[PRAAx] le e (previous M))
    (hr : Γ ⊢[PRAAx] ready P z R B M e (precision p R H) (tailCutoff p R)) :
    Γ ⊢[PRAAx] independentRate F W (fd z R B M e) (data p z R B H M e)
      (errorNumerator z R B M e zero) (unit P) :=
  centered_rate P z R B M e (precision p R H) (tailCutoff p R) hz he hr

def readinessClock (P z R B M e : PTm n) : PTm n :=
  exponent (prefactorGain R+tailGain R M) (GaussianBarnesCanonicalTaylorProductCoefficientName.clock P z R B M e)

private theorem freeze_positive (R : PTm n) (hR : Γ ⊢[PRAAx] le one R) :
    Γ ⊢[PRAAx] le one (GaussianBarnesCanonicalCorrectedMercatorCofinal.freezeNumerator R) := by
  let a := GaussianBarnesCanonicalLogRow.boundNumerator R
  have ha : Γ ⊢[PRAAx] le one a :=
    positive_product _ _ (positive_product _ _ (positive_product _ _ (le_succ_self one) hR) hR) hR
  exact le_trans ha (le_add_right a a)

theorem ready_of_le (P p z R B H M e : PTm n) (hR : Γ ⊢[PRAAx] le one R)
    (hlate : Γ ⊢[PRAAx] le (readinessClock P z R B M e) p) :
    Γ ⊢[PRAAx] ready P z R B M e (precision p R H) (tailCutoff p R) := by
  let c := GaussianBarnesCanonicalTaylorProductCoefficientName.clock P z R B M e
  let a := prefactorGain R
  let b := tailGain R M
  have due : Γ ⊢[PRAAx] le ((a+b)*unit c) (unit p) :=
    le_trans (query_budget (a+b) c) (unit_monotone hlate)
  have hq : Γ ⊢[PRAAx] le (unit p) (unit (precision p R H)) :=
    unit_monotone (le_add_right p _)
  have hr : Γ ⊢[PRAAx] le (unit p) (tailCutoff p R) :=
    le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (unit p) (freeze_positive R hR))
  exact .andI
    (le_trans (mul_le_mul_right (unit c) (le_add_right a b)) (le_trans due hq))
    (le_trans (mul_le_mul_right (unit c) (le_add_left b a)) (le_trans due hr))

def coefficientBudget (R e : PTm n) : PTm n := (centralUGain R+two)*fact e

def coefficientClock (P R e : PTm n) : PTm n := exponent (coefficientBudget R e) P

def clock (P z R B M e : PTm n) : PTm n := readinessClock (coefficientClock P R e) z R B M e

private theorem budget (z R B M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] le (errorNumerator z R B M e zero) (coefficientBudget R e) := by
  unfold errorNumerator GaussianNamedUniformRateClosure.productBudget coefficientBudget
  ipra_le 𝔞(fact e)*sl (central_U_le z R B hz)

theorem rate_of_le (P p z R B H M e : PTm n) (hR : Γ ⊢[PRAAx] le one R)
    (hz : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e (previous M))
    (hlate : Γ ⊢[PRAAx] le (clock P z R B M e) p) :
    Γ ⊢[PRAAx] independentRate F W (fd z R B M e) (data p z R B H M e) one (unit P) := by
  let A := errorNumerator z R B M e zero
  let c := coefficientClock P R e
  have pay : Γ ⊢[PRAAx] le (A*unit P) (one*unit c) :=
    le_congr (.eqRefl _) (one_mul _).eqSymm
      (le_trans (mul_le_mul_right (unit P) (budget z R B M e hz)) (query_budget (coefficientBudget R e) P))
  exact GaussianNamedRateRadius.weaken F W (fd z R B M e) (data p z R B H M e)
    A (unit c) one (unit P) (unit_positive c) (unit_positive P) pay
    (rate_of_ready c p z R B H M e hz he (ready_of_le c p z R B H M e hR hlate))

theorem shared_rate_of_le (P p z R B H M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (he : Γ ⊢[PRAAx] le e (previous M)) (hlate : Γ ⊢[PRAAx] le (clock P z (R+one) B M e) p) :
    Γ ⊢[PRAAx] independentRate F W (fd z (R+one) B M e) (data p z (R+one) B H M e) one (unit P) :=
  rate_of_le P p z (R+one) B H M e (le_add_left one R)
    (.andI hz.andE₁ (bounded_mono hz.andE₂ (le_of_eq_add (d := B) (by ipra_ring)))) he hlate

theorem actual_Barnes_weighted_Taylor_ball_factorial_coefficient_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (let P := var 0
       let p := var 1
       let z := var 2
       let R := var 3
       let B := var 4
       let H := var 5
       let M := var 6
       let e := var 7
       (source z R B ⋏ le e (previous M) ⋏ le (clock P z (R+one) B M e) p) ⟶
         independentRate F W (fd z (R+one) B M e) (data p z (R+one) B H M e) one (unit P)) :=
  closeUniv 8 (.impI (shared_rate_of_le _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalWeightedTaylorBallCoefficient
