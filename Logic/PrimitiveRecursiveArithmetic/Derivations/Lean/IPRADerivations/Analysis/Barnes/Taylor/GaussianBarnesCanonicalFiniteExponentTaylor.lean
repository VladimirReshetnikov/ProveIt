import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalExponentTaylorBallSchedule

/-!
# Taylor comparison for the complete literal finite Barnes exponent

Both endpoints use the same finite log cutoff. Interleave the actual
prefix and finite logarithm differences, then evaluate the existing
frozen exponent buffer by Horner. The prefactor observation clock is
independent of the cutoff.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteExponentTaylor

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalCorrectedMercatorCofinal (input interval_input analyticDenominator analytic_denominator_positive)
open GaussianBarnesCanonicalExponentTaylor (prefixIncrementF prefixIncrementData polynomialF polynomialData)
open GaussianBarnesCanonicalExponentTaylorBallSchedule (uniformCost precision)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogCofinalRate (initial_source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalSingleExponential (prefixF prefixData prefix_regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans)
open GaussianNamedDifferenceRate (rate_parameters_congr self_rate)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedRateComposition (leadingNumerator leadingDenominator)
open GaussianRationalHorner (positive_product)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "L" => GaussianBarnesCanonicalFiniteLog.nameF
local notation "ld" => GaussianBarnesCanonicalFiniteLog.data
local notation "I" => GaussianBarnesCanonicalDerivativeInterval.incrementF
local notation "id" => GaussianBarnesCanonicalDerivativeInterval.incrementData
local notation "C" => constantF
local notation "Diff" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data
local notation "T" => GaussianBarnesCanonicalCorrectedMercator.numerator

abbrev exponentF : PR 2 := addF prefixF L
def exponentData (z R B r : PTm n) : PTm n := addData (prefixData z R B) (ld z R B (initial R) r)

abbrev nameF : PR 2 := Diff exponentF exponentF
def data (z h R B r : PTm n) : PTm n := dd (exponentData (add z h) R B r) (exponentData z R B r)

abbrev value (q z h R B r M : PTm n) : PTm n := GaussianBarnesCanonicalExponentTaylorHorner.hornerValue q z h R B r M

def numerator (q R B H M : PTm n) : PTm n :=
  leadingNumerator (T (previous M) H) (analyticDenominator (previous M) R B) (uniformCost R H) (unit q)

def denominator (q R B M : PTm n) : PTm n := leadingDenominator (analyticDenominator (previous M) R B) (unit q)

def scheduledNumerator (p R B H M : PTm n) : PTm n :=
  T (previous M) H*unit p+analyticDenominator (previous M) R B

def scheduledDenominator (p R B M : PTm n) : PTm n := analyticDenominator (previous M) R B*unit p

@[simp] theorem subst_exponentData {m : ℕ} (σ : Fin n → PTm m) (z R B r : PTm n) :
    Syn.subst σ (exponentData z R B r) = exponentData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ r) := by
  simp [exponentData,prefixData,GaussianBarnesCanonicalSingleExponential.prefactorExponentData]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z h R B r : PTm n) :
    Syn.subst σ (data z h R B r) =
      data (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ r) := by simp [data]

private theorem finite_log_regular (z R B r : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] pointCN L (ld z R B (initial R) r) :=
  GaussianBarnesCanonicalFiniteLog.regular z R B (initial R) r (initial_source z R B hz)

theorem exponent_regular (z R B r : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] pointCN exponentF (exponentData z R B r) :=
  add_fast prefixF L _ _ (prefix_regular z R B) (finite_log_regular z R B r hz)

theorem regular (z h R B r : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source (add z h) R B) :
    Γ ⊢[PRAAx] pointCN nameF (data z h R B r) :=
  GaussianNamedDifference.name_regular exponentF exponentF _ _
    (exponent_regular (add z h) R B r hw) (exponent_regular z R B r hz)

theorem increment_split (z h R B r : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source (add z h) R B) :
    Γ ⊢[PRAAx] crossEquivalent nameF (addF prefixIncrementF I) (data z h R B r)
      (addData (prefixIncrementData z h R B) (id z h R B (initial R) r)) := by
  let w := add z h
  let a := prefixData w R B
  let b := prefixData z R B
  let u := ld w R B (initial R) r
  let v := ld z R B (initial R) r
  let t := prefixIncrementData z h R B
  let x := id z h R B (initial R) r
  have ha := prefix_regular (Γ := Γ) w R B
  have hb := prefix_regular (Γ := Γ) z R B
  have hu := finite_log_regular w R B r hw
  have hv := finite_log_regular z R B r hz
  have hi : Γ ⊢[PRAAx] pointCN I x := GaussianNamedDifference.name_regular L L u v hu hv
  have bound := GaussianNamedSumDifference.interleave prefixF L prefixF L a u b v ha hu hb hv
  have expand := GaussianNamedGammaHalfShift.add_cross (Diff prefixF prefixF) prefixIncrementF I I (dd a b) t x x
    (GaussianNamedDifference.name_regular _ _ _ _ ha hb) (GaussianBarnesCanonicalExponentTaylor.prefix_increment_regular z h R B)
    hi hi (GaussianBarnesCanonicalExponentTaylor.prefix_increment z h R B hz.andE₁) (cross_refl I x hi)
  exact cross_trans _ _ _ _ _ _ bound expand

private theorem polynomial_rate (z h R B H r M : PTm n) (hs : Γ ⊢[PRAAx] input (previous M) z h R B H) :
    let v := GaussianBarnesCanonicalCorrectedMercatorPrefix.polynomial z h B (initial R) r M
    Γ ⊢[PRAAx] independentRate nameF polynomialF (data z h R B r) (polynomialData z h R B v)
      (T (previous M) H) (analyticDenominator (previous M) R B) := by
  let m := previous M
  let N := initial R
  let v := GaussianBarnesCanonicalCorrectedMercatorPrefix.polynomial z h B N r M
  let w := GaussianBarnesCanonicalCorrectedMercatorInterval.value m z h B N r
  let J := T m H
  let D := analyticDenominator m R B
  let x := id z h R B N r
  let t := prefixIncrementData z h R B
  let F := prefixIncrementF
  have hz := hs.andE₁
  have hw := hs.andE₂.andE₁
  have hD := analytic_denominator_positive m R B hz.andE₁
  have leftReg : Γ ⊢[PRAAx] pointCN I x := GaussianNamedDifference.name_regular L L _ _
    (finite_log_regular (add z h) R B r hw) (finite_log_regular z R B r hz)
  have same := GaussianBarnesCanonicalCorrectedMercatorPrefix.coefficient_prefix z h R B N H r M (interval_input m z h R B H hs)
  have tail := GaussianNamedRateTransport.transport I C I C x w x v J D hD
    (GaussianBarnesCanonicalCorrectedMercatorCofinal.interval_uniform_rate m z h R B H r hs)
    (cross_refl I x leftReg) (GaussianGammaWeierstrassApproximant.constant_data_cross v w same.eqSymm)
  have head := self_rate (Γ := Γ) F t (GaussianBarnesCanonicalExponentTaylor.prefix_increment_regular z h R B)
  have raw := GaussianNamedAddRate.independent_rate F I F C t x t v zero one J D (le_refl one) hD head tail
  have reduce := rate_parameters_congr (addF F I) polynomialF (addData t x) (polynomialData z h R B v) _ _ J D
    (by unfold leadingNumerator; ipra_ring) (by unfold leadingDenominator; ipra_ring) raw
  exact GaussianNamedRateTransport.transport (addF F I) polynomialF nameF polynomialF (addData t x)
    (polynomialData z h R B v) (data z h R B r) (polynomialData z h R B v) J D hD reduce
    (increment_split z h R B r hz hw)
    (cross_refl polynomialF _ (GaussianBarnesCanonicalExponentTaylor.polynomial_regular z h R B v))

theorem rate (q z h R B H r M : PTm n) (hs : Γ ⊢[PRAAx] input (previous M) z h R B H) :
    Γ ⊢[PRAAx] independentRate nameF C (data z h R B r) (value q z h R B r M)
      (numerator q R B H M) (denominator q R B M) := by
  let m := previous M
  let v := GaussianBarnesCanonicalCorrectedMercatorPrefix.polynomial z h B (initial R) r M
  let t := polynomialData z h R B v
  let w := GaussianBarnesCanonicalExponentTaylorFrozen.rationalPolynomial q z h R B r M
  let A := T m H
  let D := analyticDenominator m R B
  let U := unit q
  let cost := GaussianBarnesCanonicalExponentTaylorFrozen.cost z h R B v
  let x := data z h R B r
  let y := value q z h R B r M
  have hB := hs.andE₁.andE₁
  have hD := analytic_denominator_positive m R B hB
  have hU := unit_positive (Γ := Γ) q
  have hb : Γ ⊢[PRAAx] le cost (uniformCost R H) :=
    GaussianBarnesCanonicalExponentTaylorBallSchedule.cost_bound z h R B H v M hs
  have frozen := GaussianNamedRateRadius.weaken polynomialF C t w cost U (uniformCost R H) U hU hU
    (mul_le_mul_right U hb) (GaussianBarnesCanonicalExponentTaylorFrozen.polynomial_readback q z h R B v)
  have joined := GaussianNamedRateComposition.compose nameF polynomialF C x t w A D (uniformCost R H) U
    hD hU (polynomial_rate z h R B H r M hs) frozen
  have read := GaussianBarnesCanonicalExponentTaylorHorner.horner_rationalPolynomial q z h R B r M hB
  exact GaussianNamedRateTransport.transport nameF C nameF C x w x y _ _
    (positive_product _ _ hD hU) joined (cross_refl nameF x (regular z h R B r hs.andE₁ hs.andE₂.andE₁))
    (GaussianGammaWeierstrassApproximant.constant_data_cross y w read)

theorem scheduled_rate (p z h R B H r M : PTm n) (hs : Γ ⊢[PRAAx] input (previous M) z h R B H) :
    Γ ⊢[PRAAx] independentRate nameF C (data z h R B r) (value (precision p R H) z h R B r M)
      (scheduledNumerator p R B H M) (scheduledDenominator p R B M) := by
  let m := previous M
  let q := precision p R H
  let D := analyticDenominator m R B
  let U := unit p
  let Q := unit q
  let A := T m H
  let K := uniformCost R H
  have hd := analytic_denominator_positive m R B hs.andE₁.andE₁
  have clock : Γ ⊢[PRAAx] le (K*U) Q := GaussianFastValueCut.query_budget K p
  have budget : Γ ⊢[PRAAx] le (numerator q R B H M*scheduledDenominator p R B M)
      (scheduledNumerator p R B H M*denominator q R B M) := by
    change Γ ⊢[PRAAx] le ((A*Q+K*D)*(D*U)) ((A*U+D)*(D*Q))
    let 𝔞 := fun x : PTm n => Groth.ι (IPRA.Q.mk Γ x)
    ipra_le (𝔞 D*𝔞 D)*sl clock
  exact GaussianNamedRateRadius.weaken nameF C (data z h R B r) (value q z h R B r M) _ _ _ _
    (positive_product D Q hd (unit_positive q)) (positive_product D U hd (unit_positive p)) budget (rate q z h R B H r M hs)

theorem actual_Barnes_finite_exponent_Taylor_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (let p := var 0
     let z := var 1
     let h := var 2
     let R := var 3
     let B := var 4
     let H := var 5
     let r := var 6
     let M := var 7
     input (previous M) z h R B H ⟶
       independentRate nameF C (data z h R B r) (value (precision p R H) z h R B r M)
         (scheduledNumerator p R B H M) (scheduledDenominator p R B M)) :=
  closeUniv 8 (.impI (scheduled_rate _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteExponentTaylor
