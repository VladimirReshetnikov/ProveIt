import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalTailExponentialDerivative
import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalLogDerivativeQuotient

/-! The actual divided difference of the original Barnes tail exponential
converges to the original named product of the tail value and its
cofinal logarithmic derivative. The leading error is linear
in the size of the native Gaussian increment. Both observations have
independent dyadic precisions. -/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTailExponentialQuotient

open_ipra
open ComplexLogarithmRemainder (add normSq)
open GaussianBarnesCanonicalDerivativeTailBinding
  (base_source shifted_source leadingDenominator leading_denominator_positive)
open GaussianBarnesCanonicalTailExponentialDerivative (derivativeF derivativeData errorNumerator errorGain)
open GaussianBarnesCanonicalTailExponentialMargin (incrementNumerator)
open GaussianBarnesCanonicalLogSchedule (initial initial_positive)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianL1 (norm1)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (positive_product)
open GaussianNativeDerivativeQuotientRate (norm1_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "T" => GaussianBarnesCanonicalTailExponential.nameF
local notation "td" => GaussianBarnesCanonicalTailExponential.data
local notation "D" => derivativeF
local notation "dd" => derivativeData
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def input (z h R B : PTm n) : Fm PTm n :=
  GaussianBarnesCanonicalTailExponentialMargin.input z h R B (norm1 h) ⋏ le one (normSq h)

def nameF : PR 2 := GaussianNamedDifferenceQuotient.nameF T T

def data (z h R B : PTm n) : PTm n :=
  GaussianNamedDifferenceQuotient.data T T (td (add z h) R B) (td z R B) h B

def numerator (h R : PTm n) : PTm n := two*errorGain R*norm1 h
abbrev denominator (R B : PTm n) : PTm n := GaussianBarnesCanonicalLogDerivativeQuotient.denominator R B

theorem input_from_logarithm (z h R B : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianBarnesCanonicalLogDerivativeQuotient.input z h R B)
    (hm : Γ ⊢[PRAAx] le (incrementNumerator R (norm1 h)) B) : Γ ⊢[PRAAx] input z h R B :=
  .andI (.andI hs.andE₁ hm) hs.andE₂

theorem rate (z h R B : PTm n) (hs : Γ ⊢[PRAAx] input z h R B) :
    Γ ⊢[PRAAx] independentRate nameF D (data z h R B) (dd z R B) (numerator h R) (denominator R B) := by
  let H := norm1 h
  let E := leadingDenominator R B
  have hz := base_source z h R B H hs.andE₁.andE₁
  have hw := shifted_source z h R B H hs.andE₁.andE₁
  have hB := hz.andE₁
  have sep : Γ ⊢[PRAAx] GaussianNamedDifferenceQuotient.separated h B := .andI hB hs.andE₂
  have hE := leading_denominator_positive R B hB
  have hd := GaussianBarnesCanonicalTailExponentialDerivative.derivative_regular z R B hz
  have boundRate := GaussianNativeDerivativeQuotientRate.rate T T D (td (add z h) R B) (td z R B) (dd z R B)
    h B (errorNumerator R H) E (GaussianBarnesCanonicalTailExponential.regular _ _ _ hw)
    (GaussianBarnesCanonicalTailExponential.regular _ _ _ hz) hd sep hE
    (GaussianBarnesCanonicalTailExponentialDerivative.rate z h R B H hs.andE₁)
  have hMul := positive_product _ _ (norm1_positive h hs.andE₂) hE
  apply GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ hMul
    (positive_product _ _ hB (initial_positive R)) _ boundRate
  apply le_of_eq_add (d := zero)
  change Γ ⊢[PRAAx] two*errorGain R*H*(H*((B*B)*initial R)) ≐
    (two*B)*(errorGain R*H*H)*(B*initial R)+zero
  ipra_ring

theorem precision_rate (p z h R B : PTm n) (hs : Γ ⊢[PRAAx] input z h R B)
    (hp : Γ ⊢[PRAAx] le (numerator h R*unit p) (denominator R B)) : Γ ⊢[PRAAx]
    independentRate nameF D (data z h R B) (dd z R B) one (unit p) := by
  have hB := (base_source z h R B (norm1 h) hs.andE₁.andE₁).andE₁
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _
    (positive_product _ _ hB (initial_positive R)) (unit_positive p)
    (le_congr (.eqRefl _) (one_mul _).eqSymm hp) (rate z h R B hs)

theorem actual_Barnes_cofinal_tail_exponential_derivative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     input z h R B ⟶ independentRate nameF D (data z h R B) (dd z R B) (numerator h R) (denominator R B)) :=
  closeUniv 4 (.impI (rate _ _ _ _ Prf.hyp0))

theorem actual_Barnes_cofinal_tail_exponential_derivative_precision_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (let p := var 0
       let z := var 1
       let h := var 2
       let R := var 3
       let B := var 4
       input z h R B ⟶ le (numerator h R*unit p) (denominator R B) ⟶
         independentRate nameF D (data z h R B) (dd z R B) one (unit p)) :=
  closeUniv 5 (.impI (.impI (precision_rate _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTailExponentialQuotient
