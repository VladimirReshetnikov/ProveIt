import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.ExponentCoefficients.GaussianBarnesCanonicalExponentTaylor
import IPRADerivations.Analysis.Barnes.Prefactors.GaussianBarnesCanonicalPrefactorShiftBinding
import IPRADerivations.Analysis.Exponential.PositiveAxis.NamedValues.GaussianSignedNameExponentialOrder

/-!
# Frozen rational polynomials for the full original Barnes exponent

Only the two fixed prefactor constants need rational observations.
All powers of the increment and all finite-tail coefficients remain
literal rational operations. Their sampling clock can be chosen
independently of the cutoff for the cofinal logarithm.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalExponentTaylorFrozen

open_ipra
open GaussianBarnesCanonicalExponentTaylor
  (nameF data headPolynomial polynomialF polynomialData coefficient_rate_of_cutoff)
open GaussianBarnesCanonicalPrefactor (quadraticCoefficientF quadraticCoefficientData quadratic_coefficient_regular negativeHalf)
open GaussianBarnesCanonicalPrefactorExponentDerivative (squareStep)
open GaussianBarnesCanonicalPrefactorShiftBinding (Observation leaf const sum product)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalCorrectedMercatorCofinal
  (input cutoff freezeDenominator scheduledNumerator scheduledDenominator analytic_denominator_positive)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedRateComposition (leadingNumerator leadingDenominator)
open GaussianRationalHorner (ofGaussian qadd qmul positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "S" => GaussianStirlingConstant.nameF
local notation "sd" => GaussianStirlingConstant.nameData
local notation "Q" => quadraticCoefficientF
local notation "qd" => quadraticCoefficientData
local notation "tailValue" => GaussianBarnesCanonicalCorrectedMercatorPrefix.polynomial
local notation "degree" => GaussianBarnesCanonicalHigherRows.previous

private def observation (z h R B v : PTm n) : Observation Γ :=
  let a := const (ofGaussian h B)
  let b := const (squareStep z h B)
  let s := leaf S (sd zero) (GaussianStirlingConstant.name_regular zero)
  let g := leaf Q qd quadratic_coefficient_regular
  let prefactor := sum (product a s) (product (const negativeHalf) (sum a (product b g)))
  sum (sum prefactor (const (headPolynomial z h R B))) (const v)

def rationalValue (q z h R B v : PTm n) : PTm n :=
  let a := ofGaussian h B
  let b := squareStep z h B
  let s := ap2 S q (sd zero)
  let g := ap2 Q q qd
  let prefactor := qadd (qmul a s) (qmul negativeHalf (qadd a (qmul b g)))
  qadd (qadd prefactor (headPolynomial z h R B)) v

def cost (z h R B v : PTm n) : PTm n := one+(observation (Γ := []) z h R B v).cost

def numerator (p q z h R B H r M : PTm n) : PTm n :=
  leadingNumerator (scheduledNumerator p (degree M) R B H) (scheduledDenominator p (degree M) R B)
    (cost z h R B (tailValue z h B (initial R) r M)) (unit q)

def denominator (p q R B M : PTm n) : PTm n := leadingDenominator (scheduledDenominator p (degree M) R B) (unit q)

def rationalPolynomial (q z h R B r M : PTm n) : PTm n :=
  rationalValue q z h R B (tailValue z h B (initial R) r M)

theorem polynomial_readback (q z h R B v : PTm n) :
    Γ ⊢[PRAAx] independentRate polynomialF constantF (polynomialData z h R B v)
      (rationalValue q z h R B v) (cost z h R B v) (unit q) := by
  let obs := observation (Γ := Γ) z h R B v
  have first := GaussianSignedNameExponentialOrder.own_sample_rate obs.f obs.x q obs.reg
  have last := GaussianNamedAddRate.constant_rate (ap2 obs.f q obs.x) (obs.value q) obs.cost (unit q) (unit_positive q) (obs.close q)
  exact GaussianNamedRateComposition.same_denominator obs.f constantF constantF obs.x (ap2 obs.f q obs.x) (obs.value q)
    one (unit q) obs.cost (unit_positive q) first last

theorem rational_rate_of_cutoff (p q z h R B H r M : PTm n) (hs : Γ ⊢[PRAAx] input (degree M) z h R B H)
    (hr : Γ ⊢[PRAAx] le (cutoff p R) (freezeDenominator R r)) :
    Γ ⊢[PRAAx] independentRate nameF constantF (data z h R B) (rationalPolynomial q z h R B r M)
      (numerator p q z h R B H r M) (denominator p q R B M) := by
  let v := tailValue z h B (initial R) r M
  let D := scheduledDenominator p (degree M) R B
  have hD : Γ ⊢[PRAAx] le one D :=
    positive_product _ _ (unit_positive p) (analytic_denominator_positive (degree M) R B hs.andE₁.andE₁)
  exact GaussianNamedRateComposition.compose _ _ _ _ _ _ _ _ _ _ hD (unit_positive q)
    (coefficient_rate_of_cutoff p z h R B H r M hs hr) (polynomial_readback q z h R B v)

theorem actual_Barnes_full_exponent_rational_polynomial_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (let p := var 0
     let q := var 1
     let z := var 2
     let h := var 3
     let R := var 4
     let B := var 5
     let H := var 6
     let M := var 7
     let r := cutoff p R
     input (degree M) z h R B H ⟶ independentRate nameF constantF (data z h R B) (rationalPolynomial q z h R B r M)
       (numerator p q z h R B H r M) (denominator p q R B M)) :=
  closeUniv 8 (.impI (rational_rate_of_cutoff _ _ _ _ _ _ _ _ _ Prf.hyp0 (GaussianBarnesCanonicalCorrectedMercatorCofinal.cutoff_budget _ _)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalExponentTaylorFrozen
