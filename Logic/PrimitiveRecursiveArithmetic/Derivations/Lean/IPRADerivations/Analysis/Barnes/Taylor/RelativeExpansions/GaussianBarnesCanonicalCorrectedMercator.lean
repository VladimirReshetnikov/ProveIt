import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalDerivativeBinding
import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalRelativeMercatorRemainder
import IPRADerivations.Core.CommonLemmas

/-!
# Arbitrary-degree remainder for the original corrected Barnes row

A row at a relative chart point is the old Mercator increment multiplied
by its factor index, with the exact quadratic correction added. For every
degree at least two, the original rounded row has an inverse-square rate.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCorrectedMercator

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Common (pw_two succ_le_succ)
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalRelativeStep (source)
open GaussianBarnesCanonicalDerivativeBinding (nameF data logClock regular natScale_at_radius)
open GaussianBarnesCanonicalLogFactor (correctedF correctedData fullF)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianDominantPairAlgebra (radiusPoint radius_bounded)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNameArithmetic (sum_difference sum_distance)
open GaussianNamedInverseRate (independentRate rate_at rateNumerator rateDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open GaussianRationalHorner (qadd qmul positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Rel" => GaussianBarnesCanonicalRelativeMercatorRemainder.polynomial
local notation "Inc" => GaussianBarnesCanonicalRelativeMercatorRemainder.incrementF
local notation "incd" => GaussianBarnesCanonicalRelativeMercatorRemainder.incrementData
local notation "Q" => GaussianBarnesCanonicalLogFactor.nameF
local notation "qd" => GaussianBarnesCanonicalLogFactor.data
local notation "L" => GaussianLocalLogarithmName.pointF
local notation "ld" => GaussianLocalLogarithmName.data
local notation "corr" => GaussianBarnesCanonicalFactor.correction

abbrev correctionDelta := @GaussianBarnesCanonicalDerivativeAlgebra.correctionDifference

def polynomial (m z h B k : PTm n) : PTm n :=
  qadd (qmul (radiusPoint k one) (Rel m z h B k)) (correctionDelta z h B k)

def numerator (m H : PTm n) : PTm n := two*GaussianFiniteLogarithmTaylorRemainder.numerator (two*H) m
def scaleDenominator (m B : PTm n) : PTm n := succ m*pw B (succ m)
def denominator (m B k : PTm n) : PTm n := scaleDenominator m B*(k*k)
def sampleCost (k : PTm n) : PTm n := num 12+k*num 8

@[simp] theorem subst_polynomial {l : ℕ} (σ : Fin n → PTm l) (m z h B k : PTm n) :
    Syn.subst σ (polynomial m z h B k) = polynomial (Syn.subst σ m) (Syn.subst σ z) (Syn.subst σ h)
      (Syn.subst σ B) (Syn.subst σ k) := by simp [polynomial,one]

@[simp] theorem subst_numerator {l : ℕ} (σ : Fin n → PTm l) (m H : PTm n) :
    Syn.subst σ (numerator m H) = numerator (Syn.subst σ m) (Syn.subst σ H) := by simp [numerator,two]

@[simp] theorem subst_scaleDenominator {l : ℕ} (σ : Fin n → PTm l) (m B : PTm n) :
    Syn.subst σ (scaleDenominator m B) = scaleDenominator (Syn.subst σ m) (Syn.subst σ B) := by simp [scaleDenominator]

@[simp] theorem subst_denominator {l : ℕ} (σ : Fin n → PTm l) (m B k : PTm n) :
    Syn.subst σ (denominator m B k) = denominator (Syn.subst σ m) (Syn.subst σ B) (Syn.subst σ k) :=
  by simp [denominator]

@[simp] theorem subst_sampleCost {l : ℕ} (σ : Fin n → PTm l) (k : PTm n) :
    Syn.subst σ (sampleCost k) = sampleCost (Syn.subst σ k) := by simp [sampleCost]

theorem scale_denominator_positive (m B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] le one (scaleDenominator m B) :=
  positive_product _ _ (zero_lt_succ m) (GaussianFactorBudget.power_positive _ _ hB)

theorem denominator_positive (m B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] le one (denominator m B k) :=
  positive_product _ _ (scale_denominator_positive m B hB) (positive_product _ _ hk hk)

private theorem corrected_at (p z R B k : PTm n) :
    Γ ⊢[PRAAx] ap2 correctedF p (correctedData z R B k) ≐
      qadd (qmul (radiusPoint k one) (ap2 L (logClock p k) (ld z (R*B) (B*k)))) (corr z B k) := by
  let s := GaussianFastValueCut.exponent two p
  let x := ld z (R*B) (B*k)
  have scale := (GaussianNamedNaturalScale.sample_at (Γ := Γ) L s k k x).eqTrans
    (natScale_at_radius k (ap2 L (logClock p k) x))
  exact (GaussianExponentialReference.add_sample fullF constantF (qd z R B k) (corr z B k) p).eqTrans
    (qadd_congr scale (constant_at s (corr z B k)))

private theorem corrected_increment_at (p z h R B k : PTm n) :
    Γ ⊢[PRAAx] qsub (ap2 correctedF p (correctedData (add z h) R B k)) (ap2 correctedF p (correctedData z R B k)) ≐
      qadd (qmul (radiusPoint k one) (qsub (ap2 L (logClock p k) (ld (add z h) (R*B) (B*k)))
        (ap2 L (logClock p k) (ld z (R*B) (B*k))))) (correctionDelta z h B k) := by
  have left := qsub_congr (corrected_at (Γ := Γ) p (add z h) R B k) (corrected_at p z R B k)
  exact left.eqTrans ((sum_difference _ _ _ _).eqTrans
    (qadd_congr (GaussianRationalRoundedPower.multiplication_difference _ _ _) (.eqRefl _)))

private theorem ordinary_raw (p m z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H) :
    Γ ⊢[PRAAx] distanceBounded (qsub (ap2 L p (ld (add z h) (R*B) (B*k))) (ap2 L p (ld z (R*B) (B*k))))
      (Rel m z h B k) (numerator m H*unit p+num 8*GaussianBarnesCanonicalRelativeMercatorRemainder.powerDenominator m B k)
      (GaussianBarnesCanonicalRelativeMercatorRemainder.powerDenominator m B k*unit p) := by
  let D := GaussianBarnesCanonicalRelativeMercatorRemainder.powerDenominator m B k
  let C := numerator m H
  let U := unit p
  let x := ld (add z h) (R*B) (B*k)
  let y := ld z (R*B) (B*k)
  have hX := GaussianLocalLogarithmName.name_regular _ _ _ (GaussianBarnesCanonicalLogRow.local_source (add z h) R B k hs.andE₂.andE₁)
  have hY := GaussianLocalLogarithmName.name_regular _ _ _ (GaussianBarnesCanonicalLogRow.local_source z R B k hs.andE₁)
  have hD : Γ ⊢[PRAAx] le one D :=
    positive_product _ _ (scale_denominator_positive m B hs.andE₁.andE₁)
      (GaussianFactorBudget.power_positive _ _ hs.andE₁.andE₂.andE₁)
  have hU := unit_positive (Γ := Γ) p
  have hW := positive_product D U hD hU
  have diff := distance_symmetric _ _ _ _ hU (GaussianNamedDifference.sample_error L L x y p hX hY)
  have raw := rate_at Inc constantF (incd z h R B k) (Rel m z h B k) C D p p
    (GaussianBarnesCanonicalRelativeMercatorRemainder.power_rate m z h R B k H hs)
  have first := distance_radius_mono _ _ _ _ (num 6*D) (D*U) hU hW
    (le_of_eq_add (d := zero) (by ipra_ring)) diff
  have middle := distance_radius_mono _ _ _ _ (C*U+two*D) (D*U)
    (GaussianNamedInverseRate.denominator_positive D p p hD) hW
    (le_of_eq_add (d := zero) (by dsimp only [rateNumerator,rateDenominator,U]; ipra_ring)) raw
  have last := distance_congr (.eqRefl _) (constant_at p (Rel m z h B k)) (.eqRefl _) (.eqRefl _) middle
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hW first last)

private theorem weighted_budget (p t m B k H : PTm n) (hp : Γ ⊢[PRAAx] le p t)
    (hm : Γ ⊢[PRAAx] le two m) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] le
      ((k*(numerator m H*unit t+num 8*GaussianBarnesCanonicalRelativeMercatorRemainder.powerDenominator m B k))*
        (denominator m B k*unit p))
      ((numerator m H*unit p+(k*num 8)*denominator m B k)*
        (GaussianBarnesCanonicalRelativeMercatorRemainder.powerDenominator m B k*unit t)) := by
  let C := numerator m H
  let D := GaussianBarnesCanonicalRelativeMercatorRemainder.powerDenominator m B k
  let S := denominator m B k
  let U := unit p
  let V := unit t
  have cube : Γ ⊢[PRAAx] pw k (succ two) ≐ (k*k)*k :=
    (pw_succ k two).eqTrans (congrMul (pw_two k) (.eqRefl _))
  have kpow := GaussianFactorBudget.power_monotone_length k (succ two) (succ m) hk (succ_le_succ hm)
  have cubic : Γ ⊢[PRAAx] (k*k)*k*scaleDenominator m B ≐ k*S := by unfold S denominator; ipra_ring
  have e : Γ ⊢[PRAAx] pw k (succ m)*scaleDenominator m B ≐ D := mul_comm _ _
  have hC : Γ ⊢[PRAAx] le (k*S) D :=
    le_congr cubic e (mul_le_mul_right (scaleDenominator m B) (le_congr cube (.eqRefl _) kpow))
  have first := mul_le_mul_right (C*V*U) hC
  have second := mul_le_mul_right (k*num 8*D*S) (GaussianExponentialReference.unit_monotone hp)
  exact le_congr (by change Γ ⊢[PRAAx] _ ≐ (k*(C*V+num 8*D))*(S*U); ipra_ring)
    (by change Γ ⊢[PRAAx] _ ≐ (C*U+(k*num 8)*S)*(D*V); ipra_ring) (add_le_add₂ first second)

theorem sample_error (p m z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H)
    (hm : Γ ⊢[PRAAx] le two m) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data z h R B k)) (polynomial m z h B k)
      (numerator m H*unit p+sampleCost k*denominator m B k) (denominator m B k*unit p) := by
  let t := logClock p k
  let D := GaussianBarnesCanonicalRelativeMercatorRemainder.powerDenominator m B k
  let S := denominator m B k
  let C := numerator m H
  let e := correctionDelta z h B k
  let U := unit p
  let V := unit t
  have hB := hs.andE₁.andE₁
  have hk := hs.andE₁.andE₂.andE₁
  have hS := denominator_positive m B k hB hk
  have hD : Γ ⊢[PRAAx] le one D :=
    positive_product _ _ (scale_denominator_positive m B hB) (GaussianFactorBudget.power_positive _ _ hk)
  have hU := unit_positive (Γ := Γ) p
  have hV := unit_positive (Γ := Γ) t
  have correction := GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hU
    (distance_symmetric _ _ _ _ hU (GaussianBarnesCanonicalLogFactor.corrected_observation p (add z h) R B k hs.andE₂.andE₁))
    (distance_symmetric _ _ _ _ hU (GaussianBarnesCanonicalLogFactor.corrected_observation p z R B k hs.andE₁))
  have named := GaussianNamedDifference.sample_error Q Q (qd (add z h) R B k) (qd z R B k) p
    (GaussianBarnesCanonicalLogFactor.regular (add z h) R B k hs.andE₂.andE₁)
    (GaussianBarnesCanonicalLogFactor.regular z R B k hs.andE₁)
  have first := distance_triangle_same _ _ _ _ _ _ hU named correction
  have hDV := positive_product D V hD hV
  have raw := GaussianNamedDifferenceQuotient.scale_distance (radiusPoint k one) _ _ k _ _ hDV
    (radius_bounded k one (le_refl one)) (ordinary_raw t m z h R B k H hs)
  have corrected := sum_distance _ _ _ _ _ _ _ hDV raw (distance_refl_zero e (D*V) hDV)
  have middle := distance_congr (corrected_increment_at p z h R B k).eqSymm (.eqRefl (polynomial m z h B k))
    (add_zero _) (.eqRefl _) corrected
  have later : Γ ⊢[PRAAx] le p t :=
    le_trans (le_add_right p _) (GaussianNamedNaturalScale.clock_later _ k)
  have hSU := positive_product S U hS hU
  have late := distance_radius_mono _ _ _ _ _ _ hDV hSU (weighted_budget p t m B k H later hm hk) middle
  have early := distance_radius_mono _ _ _ _ ((num 6+(num 3+num 3))*S) (S*U) hU hSU
    (le_of_eq_add (d := zero) (by ipra_ring)) first
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold sampleCost; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hSU early late)

theorem correctionRate (m z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H)
    (hm : Γ ⊢[PRAAx] le two m) :
    Γ ⊢[PRAAx] independentRate nameF constantF (data z h R B k) (polynomial m z h B k)
      (numerator m H) (denominator m B k) := by
  apply GaussianNamedConstantRateFromSlack.independent_rate _ _ _ _ _ (sampleCost k)
    (regular z h R B k H hs) (denominator_positive m B k hs.andE₁.andE₁ hs.andE₁.andE₂.andE₁)
  refine .allI ?_
  let sh (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have hs' : Δ ⊢[PRAAx] source (sh z) (sh h) (sh R) (sh B) (sh k) (sh H) :=
    by simpa [Δ,sh,Fm.shift,Syn.shift] using hs.shift
  have hm' : Δ ⊢[PRAAx] le two (sh m) := by simpa [Δ,sh,Fm.shift,Syn.shift,two] using hm.shift
  simpa only [GaussianNamedConstantRateFromSlack.sampleSlack,GaussianRationalSlackRemoval.slack,
    distanceBounded,unit,sh,Syn.shift,GaussianBarnesCanonicalDerivativeBinding.subst_data,
    subst_polynomial,subst_numerator,subst_denominator,subst_sampleCost] using
      sample_error (var 0) (sh m) (sh z) (sh h) (sh R) (sh B) (sh k) (sh H) hs' hm'

theorem actual_Barnes_corrected_Mercator_row_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let m := var 0
     let z := var 1
     let h := var 2
     let R := var 3
     let B := var 4
     let k := var 5
     let H := var 6
     (source z h R B k H ⋏ le two m) ⟶ independentRate nameF constantF (data z h R B k) (polynomial m z h B k)
       (numerator m H) (denominator m B k)) :=
  closeUniv 7 (.impI (correctionRate _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCorrectedMercator
