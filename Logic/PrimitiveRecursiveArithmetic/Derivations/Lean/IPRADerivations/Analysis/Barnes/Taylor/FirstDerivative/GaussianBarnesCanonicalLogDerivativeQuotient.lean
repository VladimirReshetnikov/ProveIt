import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.Cofinal.GaussianBarnesCanonicalDerivativeTailBinding
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNativeDerivativeQuotientRate
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateRadius

/-! The actual divided difference of the original Barnes tail logarithm
converges to its cofinal derivative series. The leading error is linear
in the size of the native Gaussian increment. Both observations have
independent dyadic precisions. -/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalLogDerivativeQuotient

open_ipra
open ComplexLogarithmRemainder (add normSq)
open GaussianBarnesCanonicalDerivativeTailBinding
  (base_source shifted_source leadingDenominator leading_denominator_positive)
open GaussianBarnesCanonicalDerivativeInterval (errorNumerator)
open GaussianBarnesCanonicalLogSchedule (initial initial_positive initial_radius)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianL1 (norm1)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (positive_product)
open GaussianNativeDerivativeQuotientRate (norm1_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => GaussianBarnesCanonicalLogCofinal.nameF
local notation "D" => GaussianBarnesCanonicalDerivativeCofinal.nameF
local notation "ld" => GaussianBarnesCanonicalLogCofinal.data
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def input (z h R B : PTm n) : Fm PTm n :=
  GaussianBarnesCanonicalDerivativeTailBinding.input z h R B (norm1 h) ⋏ le one (normSq h)

def nameF : PR 2 := GaussianNamedDifferenceQuotient.nameF L L

def data (z h R B : PTm n) : PTm n :=
  GaussianNamedDifferenceQuotient.data L L (ld (add z h) R B) (ld z R B) h B

def numerator (h R : PTm n) : PTm n := two*(num 3*R+num 342)*norm1 h
def denominator (R B : PTm n) : PTm n := B*initial R

theorem input_of_sources (z h R B : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianBarnesCanonicalLogCofinal.source z R B)
    (hw : Γ ⊢[PRAAx] GaussianBarnesCanonicalLogCofinal.source (add z h) R B)
    (hn : Γ ⊢[PRAAx] le one (normSq h))
    (hl : Γ ⊢[PRAAx] le (num 16*norm1 h) (B*initial R))
    (hs : Γ ⊢[PRAAx] le (norm1 h) B) : Γ ⊢[PRAAx] input z h R B := by
  have atInitial (v : PTm n) (hv : Γ ⊢[PRAAx] GaussianBarnesCanonicalLogCofinal.source v R B) :
      Γ ⊢[PRAAx] GaussianBarnesCanonicalLogTail.source v R B (initial R) :=
    .andI hv.andE₁ (.andI (initial_positive R) (.andI hv.andE₂ (initial_radius R)))
  exact .andI (.andI (atInitial z hz) (.andI (atInitial (add z h) hw)
    (.andI (GaussianL1.normSq_le_norm1_square h) (.andI hl hs)))) hn

theorem rate (z h R B : PTm n) (hs : Γ ⊢[PRAAx] input z h R B) :
    Γ ⊢[PRAAx] independentRate nameF D (data z h R B) (ld z R B) (numerator h R) (denominator R B) := by
  let H := norm1 h
  let E := leadingDenominator R B
  have hz := base_source z h R B H hs.andE₁
  have hw := shifted_source z h R B H hs.andE₁
  have hB := hz.andE₁
  have sep : Γ ⊢[PRAAx] GaussianNamedDifferenceQuotient.separated h B := .andI hB hs.andE₂
  have hE := leading_denominator_positive R B hB
  have hd := GaussianBarnesCanonicalDerivativeCofinal.regular z R B hz
  have boundRate := GaussianNativeDerivativeQuotientRate.rate L L D (ld (add z h) R B) (ld z R B) (ld z R B)
    h B (errorNumerator R H) E (GaussianBarnesCanonicalLogCofinal.regular _ _ _ hw)
    (GaussianBarnesCanonicalLogCofinal.regular _ _ _ hz) hd sep hE
    (GaussianBarnesCanonicalDerivativeTailBinding.rate z h R B H hs.andE₁)
  have hMul := positive_product _ _ (norm1_positive h hs.andE₂) hE
  apply GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ hMul
    (positive_product _ _ hB (initial_positive R)) _ boundRate
  apply le_of_eq_add (d := zero)
  change Γ ⊢[PRAAx] two*(num 3*R+num 342)*H*(H*((B*B)*initial R)) ≐
    (two*B)*((num 3*R+num 342)*H*H)*(B*initial R)+zero
  ipra_ring

theorem precision_rate (p z h R B : PTm n) (hs : Γ ⊢[PRAAx] input z h R B)
    (hp : Γ ⊢[PRAAx] le (numerator h R*unit p) (denominator R B)) : Γ ⊢[PRAAx]
    independentRate nameF D (data z h R B) (ld z R B) one (unit p) := by
  have hB := (base_source z h R B (norm1 h) hs.andE₁).andE₁
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _
    (positive_product _ _ hB (initial_positive R)) (unit_positive p)
    (le_congr (.eqRefl _) (one_mul _).eqSymm hp) (rate z h R B hs)

theorem actual_Barnes_cofinal_logarithm_derivative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     input z h R B ⟶ independentRate nameF D (data z h R B) (ld z R B) (numerator h R) (denominator R B)) :=
  closeUniv 4 (.impI (rate _ _ _ _ Prf.hyp0))

theorem actual_Barnes_cofinal_logarithm_derivative_precision_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (let p := var 0
       let z := var 1
       let h := var 2
       let R := var 3
       let B := var 4
       input z h R B ⟶ le (numerator h R*unit p) (denominator R B) ⟶
         independentRate nameF D (data z h R B) (ld z R B) one (unit p)) :=
  closeUniv 5 (.impI (.impI (precision_rate _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalLogDerivativeQuotient
