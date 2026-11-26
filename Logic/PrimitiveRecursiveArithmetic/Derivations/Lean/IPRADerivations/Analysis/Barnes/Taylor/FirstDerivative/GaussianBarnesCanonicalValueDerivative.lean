import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalPrefixDerivative
import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalValueDerivativeJoin
import IPRADerivations.Analysis.Barnes.Names.GaussianBarnesCanonicalNamedQuotientBinding

/-!
# The derivative of the original Barnes evaluator

The fixed head and the cofinal tail supply an explicit original
derivative name. For a nonzero rational Gaussian increment, two
independent observations satisfy an error linear in its size. For
regular names giving the same rational configuration the estimate
also applies to the original named computation and named reciprocal.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalValueDerivative

open_ipra
open ComplexLogarithmRemainder (add normSq)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial_positive)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianL1 (norm1)
open GaussianNameArithmetic (add_fast multiply_fast)
open GaussianNameEquivalence (cross_refl)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "V" => GaussianBarnesCanonicalValue.nameF
local notation "vd" => GaussianBarnesCanonicalValue.data
local notation "I" => GaussianBarnesCanonicalValue.prefixF
local notation "id" => GaussianBarnesCanonicalValue.prefixData
local notation "T" => GaussianBarnesCanonicalTailExponential.nameF
local notation "td" => GaussianBarnesCanonicalTailExponential.data
local notation "DG" => GaussianBarnesCanonicalTailExponentialDerivative.derivativeF
local notation "dg" => GaussianBarnesCanonicalTailExponentialDerivative.derivativeData
local notation "P" => GaussianBarnesCanonicalPrefixDerivative.derivativeF
local notation "pd" => GaussianBarnesCanonicalPrefixDerivative.derivativeData

def input (z h R B : PTm n) : Fm PTm n :=
  GaussianBarnesCanonicalValueDerivativeJoin.input z h R B ⋏ GaussianBarnesCanonicalPrefixDerivative.input z h R B

def stepGain (R : PTm n) : PTm n :=
  num 16+GaussianBarnesCanonicalTailExponentialMargin.incrementGain R+
    GaussianBarnesCanonicalPrefixDerivative.incrementGain R

def nameF : PR 2 := GaussianBarnesCanonicalValueDerivativeJoin.derivativeF P
def data (z R B : PTm n) : PTm n := GaussianBarnesCanonicalValueDerivativeJoin.derivativeData P z R B (pd z R B)

def quotientF : PR 2 := GaussianNamedDifferenceQuotient.nameF V V
def quotientData (z h R B : PTm n) : PTm n :=
  GaussianNamedDifferenceQuotient.data V V (vd (add z h) R B) (vd z R B) h B

def numerator (R h : PTm n) : PTm n :=
  GaussianBarnesCanonicalValueDerivativeJoin.numerator R (GaussianBarnesCanonicalPrefixDerivative.gain R) h

abbrev denominator (R B : PTm n) : PTm n := GaussianBarnesCanonicalValueDerivativeJoin.denominator R B

theorem input_of_margin (z h R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (add z h) R B) (hn : Γ ⊢[PRAAx] le one (normSq h))
    (hs : Γ ⊢[PRAAx] le (stepGain R*norm1 h) B) : Γ ⊢[PRAAx] input z h R B := by
  let A := GaussianBarnesCanonicalTailExponentialMargin.incrementGain R
  let C := GaussianBarnesCanonicalPrefixDerivative.incrementGain R
  let H := norm1 h
  have h16 : Γ ⊢[PRAAx] le (num 16) (stepGain R) :=
    le_trans (le_add_right _ A) (le_add_right _ C)
  have hA : Γ ⊢[PRAAx] le A (stepGain R) :=
    le_trans (le_add_left _ _) (le_add_right _ C)
  have hC : Γ ⊢[PRAAx] le C (stepGain R) := le_add_left _ _
  have h1 : Γ ⊢[PRAAx] le one (stepGain R) :=
    le_trans (zero_lt_succ (num 15)) h16
  have hb : Γ ⊢[PRAAx] le H B :=
    le_trans (le_congr (one_mul H) (.eqRefl _) (mul_le_mul_right H h1)) hs
  have hi : Γ ⊢[PRAAx] le B (denominator R B) :=
    le_congr (one_mul B) (mul_comm _ _) (mul_le_mul_right B (initial_positive R))
  have hl := GaussianBarnesCanonicalLogDerivativeQuotient.input_of_sources z h R B hz hw hn
    (le_trans (le_trans (mul_le_mul_right H h16) hs) hi) hb
  exact .andI (GaussianBarnesCanonicalTailExponentialQuotient.input_from_logarithm z h R B hl
    (le_trans (mul_le_mul_right H hA) hs))
    (.andI hz (.andI hw (.andI hn (le_trans (mul_le_mul_right H hC) hs))))

private theorem base_source (z h R B : PTm n) (hs : Γ ⊢[PRAAx] input z h R B) :
    Γ ⊢[PRAAx] source z R B :=
  GaussianBarnesCanonicalDerivativeTailBinding.base_source z h R B (GaussianL1.norm1 h) hs.andE₁.andE₁.andE₁

theorem regular (z R B : PTm n) (hs : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx] pointCN nameF (data z R B) :=
  add_fast _ _ _ _
    (multiply_fast DG I (dg z R B) (id z R B)
      (GaussianBarnesCanonicalTailExponentialDerivative.derivative_regular z R B hs)
      (GaussianBarnesCanonicalValue.prefix_regular z R B hs))
    (multiply_fast T P (td z R B) (pd z R B) (GaussianBarnesCanonicalTailExponential.regular z R B hs)
      (GaussianBarnesCanonicalPrefixDerivative.regular z R B hs))

theorem rate (z h R B : PTm n) (hs : Γ ⊢[PRAAx] input z h R B) : Γ ⊢[PRAAx]
    independentRate quotientF nameF (quotientData z h R B) (data z R B) (numerator R h) (denominator R B) :=
  GaussianBarnesCanonicalValueDerivativeJoin.join P z h R B (pd z R B) (GaussianBarnesCanonicalPrefixDerivative.gain R)
    hs.andE₁ (GaussianBarnesCanonicalPrefixDerivative.regular z R B (base_source z h R B hs))
    (GaussianBarnesCanonicalPrefixDerivative.rate z h R B hs.andE₂)

theorem precision_rate (p z h R B : PTm n) (hs : Γ ⊢[PRAAx] input z h R B)
    (hp : Γ ⊢[PRAAx] le (numerator R h*unit p) (denominator R B)) : Γ ⊢[PRAAx]
    independentRate quotientF nameF (quotientData z h R B) (data z R B) one (unit p) :=
  GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _
    (positive_product _ _ (base_source z h R B hs).andE₁ (initial_positive R)) (unit_positive p)
    (le_congr (.eqRefl _) (one_mul _).eqSymm hp) (rate z h R B hs)

theorem named_rate (F H K : PR 2) (u v x a z h R B : PTm n)
    (hs : Γ ⊢[PRAAx] input z h R B)
    (hn : Γ ⊢[PRAAx] GaussianBarnesCanonicalNamedQuotientBinding.input F H K u v x a z h R R B) : Γ ⊢[PRAAx]
    independentRate (GaussianBarnesCanonicalNamedQuotientBinding.nameF F H K) nameF
      (GaussianBarnesCanonicalNamedQuotientBinding.quotientData F H K u v x a R R) (data z R B)
      (numerator R h) (denominator R B) := by
  have hz := base_source z h R B hs
  exact GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _
    (positive_product _ _ hz.andE₁ (initial_positive R)) (rate z h R B hs)
    (GaussianBarnesCanonicalNamedQuotientBinding.binding F H K u v x a z h R R B hn)
    (cross_refl _ _ (regular z R B hz))

theorem actual_Barnes_value_derivative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     input z h R B ⟶ independentRate quotientF nameF (quotientData z h R B) (data z R B)
       (numerator R h) (denominator R B)) :=
  closeUniv 4 (.impI (rate _ _ _ _ Prf.hyp0))

theorem actual_Barnes_value_derivative_precision_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let p := var 0
     let z := var 1
     let h := var 2
     let R := var 3
     let B := var 4
     input z h R B ⟶ le (numerator R h*unit p) (denominator R B) ⟶
       independentRate quotientF nameF (quotientData z h R B) (data z R B) one (unit p)) :=
  closeUniv 5 (.impI (.impI (precision_rate _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_named_Barnes_derivative_at_rational_configuration_closed (F H K : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (let u := var 0
       let v := var 1
       let x := var 2
       let a := var 3
       let z := var 4
       let h := var 5
       let R := var 6
       let B := var 7
       input z h R B ⟶ GaussianBarnesCanonicalNamedQuotientBinding.input F H K u v x a z h R R B ⟶
         independentRate (GaussianBarnesCanonicalNamedQuotientBinding.nameF F H K) nameF
           (GaussianBarnesCanonicalNamedQuotientBinding.quotientData F H K u v x a R R) (data z R B)
           (numerator R h) (denominator R B)) :=
  closeUniv 8 (.impI (.impI (named_rate F H K _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalValueDerivative
