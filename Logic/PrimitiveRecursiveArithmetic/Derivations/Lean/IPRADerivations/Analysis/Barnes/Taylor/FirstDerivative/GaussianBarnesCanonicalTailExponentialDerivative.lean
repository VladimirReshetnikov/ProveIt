import IPRADerivations.Analysis.Barnes.TailControl.GaussianBarnesCanonicalTailExponentialMargin
import IPRADerivations.Analysis.Exponential.Names.GaussianNamedExponentialShiftDerivative
import IPRADerivations.Analysis.Gamma.Ratios.GaussianGammaRationalRatioBinding
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateComposition

/-!
# First-order estimate for the original Barnes tail exponential

Apply the actual exponential addition theorem to the original Barnes
logarithm and its certified small difference. Transport back to the two
original radius-programmed observations and their product-rule name.
The quadratic coefficient depends only on the certified disk radius.
-/

set_option autoImplicit false
set_option maxHeartbeats 750000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTailExponentialDerivative

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalDerivativeTailBinding (leadingDenominator base_source shifted_source)
open GaussianBarnesCanonicalTailExponentialMargin
  (input logarithmErrorGain incrementGain incrementNumerator smallF smallData small_source small_cross
    exponentialBound exponentialUGain exponential_samples_bound exponential_U_bound logarithm_increment_regular)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (ofGaussian positive_product)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => GaussianBarnesCanonicalLogCofinal.nameF
local notation "ld" => GaussianBarnesCanonicalLogCofinal.data
local notation "T" => GaussianBarnesCanonicalTailExponential.nameF
local notation "td" => GaussianBarnesCanonicalTailExponential.data
local notation "D" => GaussianBarnesCanonicalDerivativeCofinal.nameF
local notation "radius" => GaussianBarnesCanonicalFiniteLog.radius
local notation "I" => GaussianBarnesCanonicalDerivativeTailBinding.incrementF
local notation "id" => GaussianBarnesCanonicalDerivativeTailBinding.incrementData
local notation "G" => GaussianBarnesCanonicalDerivativeTailBinding.scaledDerivativeF
local notation "gd" => GaussianBarnesCanonicalDerivativeTailBinding.scaledDerivativeData
local notation "Diff" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data

abbrev incrementF : PR 2 := Diff T T

def incrementData (z h R B : PTm n) : PTm n := dd (td (add z h) R B) (td z R B)

abbrev derivativeF : PR 2 := multiplyF T D

def derivativeData (z R B : PTm n) : PTm n := multiplyData T D (td z R B) (ld z R B)

abbrev linearF : PR 2 := multiplyF constantF derivativeF

def linearData (z h R B : PTm n) : PTm n := multiplyData constantF derivativeF (ofGaussian h B) (derivativeData z R B)

def errorGain (R : PTm n) : PTm n :=
  exponentialUGain R*(incrementGain R*incrementGain R)*initial R + exponentialBound R*logarithmErrorGain R

def errorNumerator (R H : PTm n) : PTm n := errorGain R*H*H

@[simp] theorem subst_incrementData {m : ℕ} (σ : Fin n → PTm m) (z h R B : PTm n) :
    Syn.subst σ (incrementData z h R B) =
      incrementData (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) := by simp [incrementData]

@[simp] theorem subst_derivativeData {m : ℕ} (σ : Fin n → PTm m) (z R B : PTm n) :
    Syn.subst σ (derivativeData z R B) = derivativeData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by
  simp [derivativeData]

@[simp] theorem subst_linearData {m : ℕ} (σ : Fin n → PTm m) (z h R B : PTm n) :
    Syn.subst σ (linearData z h R B) = linearData (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) :=
  by simp [linearData]

@[simp] theorem subst_errorGain {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (errorGain R) = errorGain (Syn.subst σ R) := by simp [errorGain]

@[simp] theorem subst_errorNumerator {m : ℕ} (σ : Fin n → PTm m) (R H : PTm n) :
    Syn.subst σ (errorNumerator R H) = errorNumerator (Syn.subst σ R) (Syn.subst σ H) := by simp [errorNumerator]

theorem derivative_regular (z R B : PTm n) (hs : Γ ⊢[PRAAx] GaussianBarnesCanonicalLogCofinal.source z R B) :
    Γ ⊢[PRAAx] pointCN derivativeF (derivativeData z R B) :=
  multiply_fast T D _ _ (GaussianBarnesCanonicalTailExponential.regular z R B hs)
    (GaussianBarnesCanonicalDerivativeCofinal.regular z R B hs)

private theorem sum_cross (z h R B H : PTm n) (hs : Γ ⊢[PRAAx] input z h R B H) :
    Γ ⊢[PRAAx] crossEquivalent (addF L smallF) L (addData (ld z R B) (smallData z h R B H)) (ld (add z h) R B) := by
  let x := ld z R B
  let y := smallData z h R B H
  let v := id z h R B
  let u := ld (add z h) R B
  have hx := GaussianBarnesCanonicalLogCofinal.regular z R B (base_source z h R B H hs.andE₁)
  have hu := GaussianBarnesCanonicalLogCofinal.regular (add z h) R B (shifted_source z h R B H hs.andE₁)
  have hy := (small_source z h R B H hs).andE₂.andE₂.andE₁
  have hv := logarithm_increment_regular z h R B H hs.andE₁
  have first := GaussianNamedGammaHalfShift.add_cross L L smallF I x x y v hx hx hy hv (cross_refl _ _ hx)
    (small_cross z h R B H hs)
  have swap := GaussianNameRingLaws.add_commutative L I x v hx hv
  have recover := GaussianGammaRationalRatioBinding.difference_add_recover L L u x hu hx
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ swap recover)

private theorem increment_cross (z h R B H : PTm n) (hs : Γ ⊢[PRAAx] input z h R B H) :
    Γ ⊢[PRAAx] crossEquivalent incrementF (GaussianNamedExponentialShiftDerivative.incrementF L smallF)
      (incrementData z h R B) (GaussianNamedExponentialShiftDerivative.incrementData (radius R) (ld z R B) (smallData z h R B H)) := by
  let r := radius R
  let x := ld z R B
  let y := smallData z h R B H
  let v := ld (add z h) R B
  let s := addData x y
  let a := td z R B
  let b := td (add z h) R B
  let W := GaussianExponentialAddition.sumF L smallF
  let c := GaussianExponentialAddition.sumData r x y
  have hR : Γ ⊢[PRAAx] le one r := le_add_right one _
  have hz := base_source z h R B H hs.andE₁
  have hv := shifted_source z h R B H hs.andE₁
  have hx := GaussianBarnesCanonicalTailExponential.log_input z R B hz
  have hy := GaussianNamedExponentialLinearRate.unit_input smallF y (incrementNumerator R H) B (small_source z h R B H hs)
  have wide := GaussianExponentialRadiusIndependence.input_widen smallF one r y hy hR
  have combined := GaussianExponentialReference.add_input L smallF r x y hx wide
  have eq := GaussianExponentialRadiusIndependence.independent_radii_proper (addF L smallF) L (r+r) r s v combined
    (GaussianBarnesCanonicalTailExponential.log_input (add z h) R B hv) (sum_cross z h R B H hs)
  have ha := GaussianBarnesCanonicalTailExponential.regular z R B hz
  have hb := GaussianBarnesCanonicalTailExponential.regular (add z h) R B hv
  have hc : Γ ⊢[PRAAx] pointCN W c := GaussianRadiusExponentialName.name_regular (addF L smallF) (r+r) s combined
  exact GaussianNamedDifferenceQuotientProperness.difference_proper T W T T b c a a hb hc ha ha
    (cross_symm _ _ _ _ eq) (cross_refl _ _ ha)

private theorem linear_cross (z h R B : PTm n) (hs : Γ ⊢[PRAAx] GaussianBarnesCanonicalLogCofinal.source z R B) :
    Γ ⊢[PRAAx] crossEquivalent linearF (multiplyF T G) (linearData z h R B) (multiplyData T G (td z R B) (gd z h R B)) := by
  let x := td z R B
  let y := ofGaussian h B
  let v := ld z R B
  let c := multiplyData constantF T y x
  let a := multiplyData T constantF x y
  have hx := GaussianBarnesCanonicalTailExponential.regular z R B hs
  have hy := constant_regular (Γ := Γ) y
  have hv := GaussianBarnesCanonicalDerivativeCofinal.regular z R B hs
  have first := cross_symm _ _ _ _ (GaussianNameRingLaws.multiply_associative constantF T D y x v hy hx hv)
  have change := GaussianGammaAdjacentCutoff.multiply_cross (multiplyF constantF T) (multiplyF T constantF) D D c a v v
    (multiply_fast _ _ _ _ hy hx) (multiply_fast _ _ _ _ hx hy) hv hv
    (GaussianNameRingLaws.multiply_commutative constantF T y x hy hx) (cross_refl _ _ hv)
  have last := GaussianNameRingLaws.multiply_associative T constantF D x y v hx hy hv
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ change last)

theorem rate (z h R B H : PTm n) (hs : Γ ⊢[PRAAx] input z h R B H) :
    Γ ⊢[PRAAx] independentRate incrementF linearF (incrementData z h R B) (linearData z h R B)
      (errorNumerator R H) (leadingDenominator R B) := by
  let r := radius R
  let x := ld z R B
  let y := smallData z h R B H
  let v := id z h R B
  let d := td z R B
  let a := gd z h R B
  let F := GaussianNamedExponentialShiftDerivative.incrementF L smallF
  let f := GaussianNamedExponentialShiftDerivative.incrementData r x y
  let G₀ := multiplyF T smallF
  let g := multiplyData T smallF d y
  let K := leadingDenominator R B
  let A := incrementNumerator R H
  let C := GaussianBarnesCanonicalDerivativeInterval.errorNumerator R H
  let M := exponentialBound R
  let P := exponentialUGain R*(A*A)*initial R
  have hz := base_source z h R B H hs.andE₁
  have hB := hz.andE₁
  have hB2 := positive_product B B hB hB
  have hK := GaussianBarnesCanonicalDerivativeTailBinding.leading_denominator_positive R B hB
  have ht := GaussianBarnesCanonicalTailExponential.regular z R B hz
  have hR : Γ ⊢[PRAAx] le one r := le_add_right one _
  have hSmall := small_source z h R B H hs
  have hS := hSmall.andE₂.andE₂.andE₁
  have hG := multiply_fast constantF D (ofGaussian h B) x (constant_regular _)
    (GaussianBarnesCanonicalDerivativeCofinal.regular z R B hz)
  have bound := exponential_U_bound z R B hz
  have pay : Γ ⊢[PRAAx] le (GaussianNamedExponentialShiftDerivative.coefficient L r x A*K) (P*(B*B)) := by
    change Γ ⊢[PRAAx] le ((GaussianNameBounds.U T d*(A*A))*K) (P*(B*B))
    exact le_congr (by ipra_ring)
      (by dsimp only [P,K]; unfold leadingDenominator; ipra_ring) (mul_le_mul_right ((A*A)*K) bound)
  have first : Γ ⊢[PRAAx] independentRate F G₀ f g P K :=
    GaussianNamedRateRadius.weaken F G₀ f g _ (B*B) P K hB2 hK pay
      (GaussianNamedExponentialShiftDerivative.independent_rate L smallF r x y A B hR
        (GaussianBarnesCanonicalTailExponential.log_input z R B hz) hSmall)
  have derivative := GaussianBarnesCanonicalDerivativeTailBinding.rate z h R B H hs.andE₁
  have diffRate := GaussianNamedRateTransport.transport I G smallF G v a y a C K hK derivative
    (small_cross z h R B H hs) (cross_refl _ _ hG)
  have weighted := GaussianNamedMultiplyRate.independent_rate T smallF T G d y d a
    (ConciseIPRA.PTm.zero) one C K (GaussianNameBounds.U smallF y) M
    (le_refl one) hK ht hS ht hG (GaussianNameBounds.all_samples_bounded smallF y hS)
    (exponential_samples_bound z R B hz) (GaussianNamedDifferenceRate.self_rate T d ht) diffRate
  have second : Γ ⊢[PRAAx] independentRate G₀ (multiplyF T G) g (multiplyData T G d a) (M*C) K :=
    GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _
      (by unfold GaussianNamedMultiplyRate.leadingNumerator; ipra_ring)
      (by unfold GaussianNamedMultiplyRate.leadingDenominator; ipra_ring) weighted
  have join := GaussianNamedRateComposition.same_denominator _ _ _ _ _ _ P K (M*C) hK first second
  have finalRate : Γ ⊢[PRAAx] independentRate F (multiplyF T G) f (multiplyData T G d a) (errorNumerator R H) K :=
    GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _
      (by simp only [P,A,C,M,incrementNumerator,logarithmErrorGain,errorNumerator,errorGain,
          GaussianBarnesCanonicalDerivativeInterval.errorNumerator,
          GaussianBarnesCanonicalDerivativeBinding.boundNumerator]; ipra_ring) (.eqRefl _) join
  exact GaussianNamedRateTransport.transport F (multiplyF T G) incrementF linearF f (multiplyData T G d a)
    (incrementData z h R B) (linearData z h R B) (errorNumerator R H) K hK finalRate
    (increment_cross z h R B H hs) (linear_cross z h R B hz)

theorem actual_Barnes_tail_exponential_first_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     let H := var 4
     input z h R B H ⟶ independentRate incrementF linearF (incrementData z h R B) (linearData z h R B)
       (errorNumerator R H) (leadingDenominator R B)) :=
  closeUniv 5 (.impI (rate _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTailExponentialDerivative
