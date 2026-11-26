import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.FirstDerivative.GaussianBarnesCanonicalPositiveFirstLogarithmPrefactor
import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.SecondDerivative.GaussianBarnesCanonicalPositiveSecondDerivativeSeriesBinding
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedAddRate

/-!
# The positive first logarithm name differentiates to the second name

The exact prefactor increment joins the independently verified
finite-prefix series rate. The resulting estimate controls the actual
native divided difference of the complete first logarithm name.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveSecondDerivativeBinding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (normSq)
open GaussianBarnesCanonicalPositiveFirstDerivativeRow (gain)
open GaussianBarnesCanonicalPositiveSecondDerivativeSeriesBinding (numerator)
open GaussianBarnesCanonicalThirdDerivativeCofinalBinding (source)
open GaussianBarnesCanonicalThirdDerivativePositiveMargin (step)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (addF addData multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (cross_refl)
open GaussianNameRingLaws (distributive)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (ofGaussian positive_product)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "F" => GaussianBarnesCanonicalPositiveFirstLogarithm.nameF
local notation "fd" => GaussianBarnesCanonicalPositiveFirstLogarithm.data
local notation "E" => GaussianBarnesCanonicalPrefactorInverse.exponentF
local notation "ed" => GaussianBarnesCanonicalPositiveFirstLogarithm.prefactorData
local notation "U" => GaussianBarnesCanonicalPositiveFirstLogarithm.seriesF
local notation "ud" => GaussianBarnesCanonicalPositiveFirstLogarithm.seriesData
local notation "G" => GaussianBarnesCanonicalPositiveSecondLogarithm.nameF
local notation "gd" => GaussianBarnesCanonicalPositiveSecondLogarithm.data
local notation "Kf" => GaussianBarnesCanonicalPositiveSecondLogarithm.coefficientF
local notation "kd" => GaussianBarnesCanonicalPositiveSecondLogarithm.coefficientData
local notation "V" => GaussianBarnesCanonicalPositiveSecondLogarithm.seriesF
local notation "vd" => GaussianBarnesCanonicalPositiveSecondLogarithm.seriesData
local notation "P" => GaussianBarnesCanonicalPositiveSecondDerivativeSeriesBinding.incrementF
local notation "pd" => GaussianBarnesCanonicalPositiveSecondDerivativeSeriesBinding.incrementData
local notation "Q" => GaussianBarnesCanonicalPositiveSecondDerivativeSeriesBinding.linearF
local notation "qd" => GaussianBarnesCanonicalPositiveSecondDerivativeSeriesBinding.linearData
local notation "Diff" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data

def incrementF : PR 2 := Diff F F
def incrementData (A C B R : PTm n) : PTm n := dd (fd C B R) (fd A B R)

def linearF : PR 2 := multiplyF constantF G
def linearData (A C B R : PTm n) : PTm n := multiplyData constantF G (ofGaussian (step A C) B) (gd A B R)

theorem rate (A C B R H K : PTm n) (h : Γ ⊢[PRAAx] source A C B R H K) :
    Γ ⊢[PRAAx] independentRate incrementF linearF (incrementData A C B R) (linearData A C B R)
      (numerator H K) (B*B) := by
  let s := ofGaussian (step A C) B
  let M := numerator H K
  let D := B*B
  let x := dd (ed C B) (ed A B)
  let y := multiplyData constantF Kf s kd
  let W := multiplyF constantF Kf
  let J := Diff E E
  have hB := h.andE₁.andE₁
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hB hB
  have rK := GaussianBarnesCanonicalPositiveSecondLogarithm.coefficient_regular (Γ := Γ) (n := n)
  have sr := constant_regular (Γ := Γ) s
  have wa := multiply_fast _ _ _ _ sr rK
  have ep := GaussianBarnesCanonicalPositiveFirstLogarithmPrefactor.increment A C B hB
  have prefactor : Γ ⊢[PRAAx] independentRate J W x y zero one :=
    GaussianNamedRateTransport.transport W W J W y y x y zero one (le_refl one)
      (GaussianNamedDifferenceRate.self_rate W y wa) ep (cross_refl _ _ wa)
  have rows := GaussianBarnesCanonicalPositiveSecondDerivativeSeriesBinding.rate A C B R H K h
  have added := GaussianNamedAddRate.independent_rate J P W Q x (pd A C B R) y (qd A C B R)
    zero one M D (le_refl one) hD prefactor rows
  have main := GaussianNamedDifferenceRate.rate_parameters_congr (addF J P) (addF W Q)
    (addData x (pd A C B R)) (addData y (qd A C B R))
    (GaussianNamedRateComposition.leadingNumerator zero one M D) (GaussianNamedRateComposition.leadingDenominator one D)
    M D (by unfold GaussianNamedRateComposition.leadingNumerator; ipra_ring)
    (by unfold GaussianNamedRateComposition.leadingDenominator; ipra_ring) added
  have left := GaussianNamedSumDifference.interleave E U E U (ed C B) (ud C B R) (ed A B) (ud A B R)
    (GaussianBarnesCanonicalPositiveFirstLogarithm.prefactor_regular C B)
    (GaussianBarnesCanonicalPositiveFirstLogarithm.series_regular C B R h.andE₂.andE₂)
    (GaussianBarnesCanonicalPositiveFirstLogarithm.prefactor_regular A B)
    (GaussianBarnesCanonicalPositiveFirstLogarithm.series_regular A B R h.andE₂.andE₁)
  have right := distributive constantF Kf V s kd (vd A B R) sr rK
    (GaussianBarnesCanonicalPositiveSecondLogarithm.series_regular A B R h.andE₂.andE₁)
  exact GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ M D hD main left right

def quotientF : PR 2 := GaussianNamedDifferenceQuotient.nameF F F
def quotientData (A C B R : PTm n) : PTm n :=
  GaussianNamedDifferenceQuotient.data F F (fd C B R) (fd A B R) (step A C) B

def quotientNumerator (H K : PTm n) : PTm n := num 4*H*(K*K*K)

theorem quotient_rate (A C B R K : PTm n)
    (h : Γ ⊢[PRAAx] source A C B R (GaussianL1.norm1 (step A C)) K)
    (hn : Γ ⊢[PRAAx] le one (normSq (step A C))) :
    Γ ⊢[PRAAx] independentRate quotientF G (quotientData A C B R) (gd A B R)
      (quotientNumerator (GaussianL1.norm1 (step A C)) K) B := by
  let H := GaussianL1.norm1 (step A C)
  have hB := h.andE₁.andE₁
  have hD := positive_product _ _ hB hB
  have hp := GaussianNativeDerivativeQuotientRate.norm1_positive (step A C) hn
  have raw : Γ ⊢[PRAAx] independentRate quotientF G (quotientData A C B R) (gd A B R)
      ((two*B)*numerator H K) (H*(B*B)) :=
    GaussianNativeDerivativeQuotientRate.rate F F G (fd C B R) (fd A B R) (gd A B R) (step A C) B
      (numerator H K) (B*B)
      (GaussianBarnesCanonicalPositiveFirstLogarithm.regular C B R h.andE₂.andE₂)
      (GaussianBarnesCanonicalPositiveFirstLogarithm.regular A B R h.andE₂.andE₁)
      (GaussianBarnesCanonicalPositiveSecondLogarithm.regular A B R h.andE₂.andE₁)
      (.andI hB hn) hD (rate A C B R H K h)
  have fit : Γ ⊢[PRAAx] le (((two*B)*numerator H K)*B) ((quotientNumerator H K)*(H*(B*B))) :=
    le_of_eq_add (d := zero) (by dsimp only [numerator,gain,quotientNumerator]; ipra_ring)
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (positive_product _ _ hp hD) hB fit raw

theorem actual_Barnes_positive_first_logarithm_second_derivative_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (let A := var 0
       let C := var 1
       let B := var 2
       let R := var 3
       let K := var 4
       let H := GaussianL1.norm1 (step A C)
       (source A C B R H K ⋏ le one (normSq (step A C))) ⟶
         independentRate quotientF G (quotientData A C B R) (gd A B R) (quotientNumerator H K) B) :=
  closeUniv 5 (.impI (quotient_rate _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveSecondDerivativeBinding
