import IPRADerivations.Analysis.Barnes.CanonicalProducts.GaussianBarnesCanonicalSingleExponential
import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.CorrectedMercator.GaussianBarnesCanonicalCorrectedMercatorCofinal
import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.CorrectedMercator.GaussianBarnesCanonicalCorrectedMercatorPrefix
import IPRADerivations.Analysis.Names.FiniteOperations.Sums.GaussianNamedSumDifference
import IPRADerivations.Analysis.Names.FiniteOperations.Sums.GaussianNamedAddRate

/-!
# Taylor estimates for the exponent of the original Barnes factorization

The actual full exponent increment splits into the original quadratic
prefactor increment, the exact finite quadratic correction, and the
actual cofinal corrected logarithm increment. Its cofinal Taylor
estimate therefore uses the original prefactor constants and exact
finite polynomial coefficients at the chosen cutoff.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalExponentTaylor

open_ipra
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalCorrectionShift (total)
open GaussianBarnesCanonicalCorrectedMercatorCofinal
  (input cutoff scheduledNumerator scheduledDenominator analytic_denominator_positive cutoff_budget interval_input)
open GaussianCoefficientNameBounds (unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (qadd positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "A" => GaussianBarnesCanonicalPrefactorInverse.exponentF
local notation "AI" => GaussianBarnesCanonicalPrefactorExponentDerivative.incrementData
local notation "AD" => GaussianBarnesCanonicalSingleExponential.prefactorExponentData
local notation "F" => GaussianBarnesCanonicalSingleExponential.exponentF
local notation "fd" => GaussianBarnesCanonicalSingleExponential.exponentData
local notation "P" => GaussianBarnesCanonicalSingleExponential.prefixF
local notation "pd" => GaussianBarnesCanonicalSingleExponential.prefixData
local notation "L" => GaussianBarnesCanonicalLogCofinal.nameF
local notation "ld" => GaussianBarnesCanonicalLogCofinal.data
local notation "I" => GaussianBarnesCanonicalCorrectedMercatorCofinal.nameF
local notation "id" => GaussianBarnesCanonicalCorrectedMercatorCofinal.data
local notation "V" => GaussianBarnesCanonicalCorrectedMercatorInterval.value
local notation "Diff" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data

abbrev nameF : PR 2 := Diff F F

def data (z h R B : PTm n) : PTm n := dd (fd (add z h) R B) (fd z R B)

def headPolynomial (z h R B : PTm n) : PTm n :=
  qadd (GaussianBarnesCanonicalHeadCorrectionDerivative.linear z h B (initial R))
    (GaussianBarnesCanonicalHeadCorrectionDerivative.remainder h B (initial R))

abbrev prefixIncrementF : PR 2 := addF A constantF
def prefixIncrementData (z h R B : PTm n) : PTm n :=
  addData (AI z h B) (headPolynomial z h R B)

abbrev polynomialF : PR 2 := addF prefixIncrementF constantF
def polynomialData (z h R B v : PTm n) : PTm n :=
  addData (prefixIncrementData z h R B) v

@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (z h R B : PTm n) :
    Syn.subst σ (data z h R B) = data (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) := by
  simp [data]

@[simp] theorem subst_headPolynomial {l : ℕ} (σ : Fin n → PTm l) (z h R B : PTm n) :
    Syn.subst σ (headPolynomial z h R B) = headPolynomial (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) :=
  by simp [headPolynomial]

@[simp] theorem subst_prefixIncrementData {l : ℕ} (σ : Fin n → PTm l) (z h R B : PTm n) :
    Syn.subst σ (prefixIncrementData z h R B) =
      prefixIncrementData (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) := by simp [prefixIncrementData]

@[simp] theorem subst_polynomialData {l : ℕ} (σ : Fin n → PTm l) (z h R B v : PTm n) :
    Syn.subst σ (polynomialData z h R B v) =
      polynomialData (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ v) := by simp [polynomialData]

private theorem prefactor_regular (z B : PTm n) : Γ ⊢[PRAAx] pointCN A (AD z B) :=
  GaussianBarnesCanonicalPrefactorExponentDerivative.regular _ _

private theorem prefactor_increment_regular (z h B : PTm n) : Γ ⊢[PRAAx] pointCN A (AI z h B) :=
  GaussianBarnesCanonicalPrefactorExponentDerivative.regular _ _

theorem prefix_increment_regular (z h R B : PTm n) :
    Γ ⊢[PRAAx] pointCN prefixIncrementF (prefixIncrementData z h R B) :=
  add_fast _ _ _ _ (prefactor_increment_regular z h B) (constant_regular _)

theorem polynomial_regular (z h R B v : PTm n) : Γ ⊢[PRAAx] pointCN polynomialF (polynomialData z h R B v) :=
  add_fast _ _ _ _ (prefix_increment_regular z h R B) (constant_regular v)

private theorem prefactor_increment (z h B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent (Diff A A) A (dd (AD (add z h) B) (AD z B)) (AI z h B) := by
  let a := AD z B
  let w := AD (add z h) B
  let i := AI z h B
  have ha := prefactor_regular (Γ := Γ) z B
  have hw := prefactor_regular (Γ := Γ) (add z h) B
  have hi := prefactor_increment_regular (Γ := Γ) z h B
  have hsum := add_fast A A a i ha hi
  have shift : Γ ⊢[PRAAx] crossEquivalent (addF A A) A (addData a i) w :=
    GaussianBarnesCanonicalPrefactorExponentDerivative.increment_add z h B hB
  have difference := GaussianNamedDifferenceQuotientProperness.difference_proper A (addF A A) A A
    w (addData a i) a a hw hsum ha ha (cross_symm _ _ _ _ shift) (cross_refl A a ha)
  exact cross_trans _ _ _ _ _ _ difference (GaussianNamedSumDifference.cancel_added A A a i ha hi)

theorem prefix_increment (z h R B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent (Diff P P) prefixIncrementF (dd (pd (add z h) R B) (pd z R B))
      (prefixIncrementData z h R B) := by
  let w := add z h
  let N := initial R
  let a := AD w B
  let b := AD z B
  let u := total w B N
  let v := total z B N
  let i := AI z h B
  let j := headPolynomial z h R B
  let C := constantF
  have ha := prefactor_regular (Γ := Γ) w B
  have hb := prefactor_regular (Γ := Γ) z B
  have hu := constant_regular (Γ := Γ) u
  have hv := constant_regular (Γ := Γ) v
  have hi := prefactor_increment_regular (Γ := Γ) z h B
  have hj := constant_regular (Γ := Γ) j
  have bound := GaussianNamedSumDifference.interleave A C A C a u b v ha hu hb hv
  have head := GaussianNamedSumDifference.constant_difference u v j
    (GaussianBarnesCanonicalHeadCorrectionDerivative.exact_expansion z h B N hB)
  have expand := add_cross (Diff A A) A (Diff C C) C (dd a b) i (dd u v) j
    (GaussianNamedDifference.name_regular _ _ _ _ ha hb) hi
    (GaussianNamedDifference.name_regular _ _ _ _ hu hv) hj (prefactor_increment z h B hB) head
  exact cross_trans _ _ _ _ _ _ bound expand

theorem increment_split (z h R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source (add z h) R B) :
    Γ ⊢[PRAAx] crossEquivalent nameF (addF prefixIncrementF I) (data z h R B)
      (addData (prefixIncrementData z h R B) (id z h R B)) := by
  let w := add z h
  let a := pd w R B
  let b := pd z R B
  let u := ld w R B
  let v := ld z R B
  let e := prefixIncrementData z h R B
  have ha : Γ ⊢[PRAAx] pointCN P a :=
    add_fast _ _ _ _ (prefactor_regular w B) (constant_regular _)
  have hb : Γ ⊢[PRAAx] pointCN P b :=
    add_fast _ _ _ _ (prefactor_regular z B) (constant_regular _)
  have hu := GaussianBarnesCanonicalLogCofinal.regular w R B hw
  have hv := GaussianBarnesCanonicalLogCofinal.regular z R B hz
  have hi := GaussianBarnesCanonicalCorrectedMercatorCofinal.regular z h R B hz hw
  have bound := GaussianNamedSumDifference.interleave P L P L a u b v ha hu hb hv
  have expand := add_cross (Diff P P) prefixIncrementF I I (dd a b) e (id z h R B) (id z h R B)
    (GaussianNamedDifference.name_regular _ _ _ _ ha hb) (prefix_increment_regular z h R B) hi hi
    (prefix_increment z h R B hz.andE₁) (cross_refl I (id z h R B) hi)
  exact cross_trans _ _ _ _ _ _ bound expand

theorem transport_log_rate (z h R B v K D : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source (add z h) R B)
    (hD : Γ ⊢[PRAAx] le one D) (hs : Γ ⊢[PRAAx] independentRate I constantF (id z h R B) v K D) :
    Γ ⊢[PRAAx] independentRate nameF polynomialF (data z h R B) (polynomialData z h R B v) K D := by
  let J := prefixIncrementF
  let a := prefixIncrementData z h R B
  let x := id z h R B
  let y := polynomialData z h R B v
  have self := GaussianNamedDifferenceRate.self_rate (Γ := Γ) J a (prefix_increment_regular z h R B)
  have raw := GaussianNamedAddRate.independent_rate J I J constantF a x a v zero one K D (le_refl one) hD self hs
  have join : Γ ⊢[PRAAx] independentRate (addF J I) polynomialF (addData a x) y K D :=
    GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _
      (by unfold GaussianNamedRateComposition.leadingNumerator; ipra_ring)
      (by unfold GaussianNamedRateComposition.leadingDenominator; ipra_ring) raw
  have left : Γ ⊢[PRAAx] crossEquivalent nameF (addF J I) (data z h R B) (addData a x) :=
    increment_split z h R B hz hw
  have right : Γ ⊢[PRAAx] crossEquivalent polynomialF polynomialF y y :=
    cross_refl polynomialF y (polynomial_regular z h R B v)
  exact GaussianNamedRateTransport.transport (addF J I) polynomialF nameF polynomialF (addData a x) y
    (data z h R B) y K D hD join left right

theorem rate_of_cutoff (p m z h R B H r : PTm n) (hs : Γ ⊢[PRAAx] input m z h R B H)
    (hr : Γ ⊢[PRAAx] le (cutoff p R) (GaussianBarnesCanonicalCorrectedMercatorCofinal.freezeDenominator R r)) :
    Γ ⊢[PRAAx] independentRate nameF polynomialF (data z h R B) (polynomialData z h R B (V m z h B (initial R) r))
      (scheduledNumerator p m R B H) (scheduledDenominator p m R B) :=
  transport_log_rate z h R B _ _ _ hs.andE₁ hs.andE₂.andE₁
    (positive_product _ _ (unit_positive p) (analytic_denominator_positive m R B hs.andE₁.andE₁))
    (GaussianBarnesCanonicalCorrectedMercatorCofinal.rate_of_cutoff p m z h R B H r hs hr)

theorem coefficient_rate_of_cutoff (p z h R B H r M : PTm n)
    (hs : Γ ⊢[PRAAx] input (GaussianBarnesCanonicalHigherRows.previous M) z h R B H)
    (hr : Γ ⊢[PRAAx] le (cutoff p R) (GaussianBarnesCanonicalCorrectedMercatorCofinal.freezeDenominator R r)) :
    let m := GaussianBarnesCanonicalHigherRows.previous M
    let v := GaussianBarnesCanonicalCorrectedMercatorPrefix.polynomial z h B (initial R) r M
    Γ ⊢[PRAAx] independentRate nameF polynomialF (data z h R B) (polynomialData z h R B v)
      (scheduledNumerator p m R B H) (scheduledDenominator p m R B) := by
  let N := initial R
  let m := GaussianBarnesCanonicalHigherRows.previous M
  let v := GaussianBarnesCanonicalCorrectedMercatorPrefix.polynomial z h B N r M
  let K := scheduledNumerator p m R B H
  let D := scheduledDenominator p m R B
  have read := GaussianBarnesCanonicalCorrectedMercatorPrefix.coefficient_prefix z h R B N H r M
    (interval_input m z h R B H hs)
  have moved := Prf.eqSubst1 (Γ := Γ) (independentRate nameF polynomialF (Syn.shift (data z h R B))
    (polynomialData (Syn.shift z) (Syn.shift h) (Syn.shift R) (Syn.shift B) (var 0)) (Syn.shift K) (Syn.shift D))
    read (by simpa only [GaussianNamedInverseRate.subst_independentRate,subst_polynomialData,Syn.subst_inst_shift,
      Syn.subst_var,Syn.inst_zero] using rate_of_cutoff p m z h R B H r hs hr)
  simpa only [GaussianNamedInverseRate.subst_independentRate,subst_polynomialData,Syn.subst_inst_shift,
    Syn.subst_var,Syn.inst_zero] using moved

theorem actual_Barnes_exponent_taylor_coefficient_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let p := var 0
     let z := var 1
     let h := var 2
     let R := var 3
     let B := var 4
     let H := var 5
     let M := var 6
     let r := cutoff p R
     let m := GaussianBarnesCanonicalHigherRows.previous M
     let v := GaussianBarnesCanonicalCorrectedMercatorPrefix.polynomial z h B (initial R) r M
     input m z h R B H ⟶ independentRate nameF polynomialF (data z h R B) (polynomialData z h R B v)
       (scheduledNumerator p m R B H) (scheduledDenominator p m R B)) :=
  closeUniv 7 (.impI (coefficient_rate_of_cutoff _ _ _ _ _ _ _ _ Prf.hyp0 (cutoff_budget _ _)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalExponentTaylor
