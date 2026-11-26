import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalValue
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalHeadSplit
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalFiniteLogProduct
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateTransport
import IPRADerivations.Analysis.Gamma.GaussianGammaInputProperness
import IPRADerivations.Analysis.Names.GaussianFastValueCut

/-!
# The original Barnes canonical product at finite cutoffs

The literal products use the prefactor followed by the direct factors from
one through the requested cutoff. Above the fixed head boundary, their
finite tails agree with the actual exponential of the cubic logarithm sum.
This identifies the cofinal evaluator quantitatively, including an explicit
cutoff for each requested dyadic precision.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial endpoint)
open GaussianBarnesCanonicalLogTail (tailDenominator tail_denominator_positive)
open GaussianBarnesCanonicalValue (prefixF prefixData nameF data finiteF finiteData errorNumerator)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedInverseRate (independentRate)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (monus num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "P" => GaussianBarnesCanonicalPrefactor.nameF
local notation "H" => GaussianBarnesCanonicalHead.nameF
local notation "E" => GaussianBarnesCanonicalTailExponential.finiteF
local notation "pd" => GaussianBarnesCanonicalPrefactor.data
local notation "hd" => GaussianBarnesCanonicalHead.data

def literalData (z R B N : PTm n) : PTm n := multiplyData P H (pd z B) (hd z R B zero N)

@[simp] theorem subst_literalData {m : ℕ} (σ : Fin n → PTm m) (z R B N : PTm n) :
    Syn.subst σ (literalData z R B N) =
      literalData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [literalData]

theorem literal_regular (z R B N : PTm n) (hs : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] pointCN prefixF (literalData z R B N) :=
  multiply_fast P H _ _ (GaussianBarnesCanonicalPrefactor.regular z B)
    (GaussianBarnesCanonicalHead.regular z R B zero N hs)

private theorem head_join (z R B a r : PTm n) (hs : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF H H) H
      (multiplyData H H (hd z R B zero a) (hd z R B a r)) (hd z R B zero (a+r)) := by
  have h₁ := GaussianBarnesCanonicalHead.regular z R B zero a hs
  have h₂ := GaussianBarnesCanonicalHead.regular z R B a r hs
  have h₃ := GaussianBarnesCanonicalHead.regular z R B (zero+a) r hs
  have e : Γ ⊢[PRAAx] hd z R B a r ≐ hd z R B (zero+a) r := by
    ipra_congr (hd (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) with
      [.eqRefl z, .eqRefl R, .eqRefl B, (zero_add a).eqSymm, .eqRefl r]
  have nameEq := GaussianGammaInputProperness.code_data_cross H _ _ h₂ h₃ e
  have hprod := GaussianGammaAdjacentCutoff.multiply_cross H H H H _ _ _ _ h₁ h₁ h₂ h₃
    (cross_refl H _ h₁) nameEq
  exact cross_trans (multiplyF H H) (multiplyF H H) H _ _ _ hprod
    (cross_symm H (multiplyF H H) _ _ (GaussianBarnesCanonicalHeadSplit.split_cross z R B zero a r hs))

theorem finite_cross (z R B r : PTm n) (hs : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] crossEquivalent finiteF prefixF (finiteData z R B r) (literalData z R B (initial R+r)) := by
  let a := initial R
  let pref := pd z B
  let head := hd z R B zero a
  let tail := hd z R B a r
  let expTail := GaussianBarnesCanonicalTailExponential.finiteData z R B a r
  have hp := GaussianBarnesCanonicalPrefactor.regular (Γ := Γ) z B
  have hh := GaussianBarnesCanonicalHead.regular z R B zero a hs
  have ht := GaussianBarnesCanonicalHead.regular z R B a r hs
  have hi := GaussianBarnesCanonicalLogCofinalRate.initial_source z R B hs
  have he := GaussianBarnesCanonicalTailExponential.finite_regular z R B a r hi
  have hc := GaussianBarnesCanonicalFiniteLogProduct.exponential_product_cross z R B a r hi
  have hprefix := GaussianBarnesCanonicalValue.prefix_regular z R B hs
  have first := GaussianGammaAdjacentCutoff.multiply_cross prefixF prefixF E H
    (prefixData z R B) (prefixData z R B) expTail tail hprefix hprefix he ht
    (cross_refl prefixF _ hprefix) hc
  have assoc := GaussianNameRingLaws.multiply_associative P H H pref head tail hp hh ht
  have join := GaussianGammaAdjacentCutoff.multiply_cross P P (multiplyF H H) H pref pref
    (multiplyData H H head tail) (hd z R B zero (a+r)) hp hp
    (multiply_fast H H head tail hh ht) (GaussianBarnesCanonicalHead.regular z R B zero (a+r) hs)
    (cross_refl P pref hp) (head_join z R B a r hs)
  exact cross_trans finiteF (multiplyF prefixF H) prefixF _ _ _ first
    (cross_trans (multiplyF prefixF H) (multiplyF P (multiplyF H H)) prefixF _ _ _ assoc join)

theorem literal_rate (z R B r : PTm n) (hs : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] independentRate prefixF nameF (literalData z R B (initial R+r)) (data z R B)
      (errorNumerator z R B) (tailDenominator (initial R+r)) :=
  GaussianNamedRateTransport.transport finiteF nameF prefixF nameF _ _ _ _ _ _
    (tail_denominator_positive _ (le_trans (GaussianBarnesCanonicalLogSchedule.initial_positive R) (le_add_right _ _)))
    (GaussianBarnesCanonicalValue.finite_rate z R B r hs)
    (cross_symm finiteF prefixF _ _ (finite_cross z R B r hs))
    (cross_refl nameF _ (GaussianBarnesCanonicalValue.regular z R B hs))

theorem literal_rate_at (z R B N : PTm n) (hs : Γ ⊢[PRAAx] source z R B)
    (hN : Γ ⊢[PRAAx] le (initial R) N) :
    Γ ⊢[PRAAx] independentRate prefixF nameF (literalData z R B N) (data z R B)
      (errorNumerator z R B) (tailDenominator N) := by
  let r := monus N (initial R)
  let M := initial R+r
  have endpointEq : Γ ⊢[PRAAx] M ≐ N := (eq_add_of_le hN).eqSymm
  have phase : Γ ⊢[PRAAx] tailDenominator M ≐ tailDenominator N :=
    congrMul (.eqRefl (num 3)) endpointEq
  have hM := tail_denominator_positive (Γ := Γ) M
    (le_trans (GaussianBarnesCanonicalLogSchedule.initial_positive R) (le_add_right _ _))
  have positive := le_congr (.eqRefl _) phase hM
  have radiusEq := congrMul (.eqRefl (errorNumerator z R B)) phase.eqSymm
  have datumEq : Γ ⊢[PRAAx] literalData z R B M ≐ literalData z R B N := by
    ipra_congr (literalData (var 0) (var 1) (var 2) (var 3) : PTm 4) with
      [.eqRefl z, .eqRefl R, .eqRefl B, endpointEq]
  have rate := GaussianNamedRateRadius.weaken prefixF nameF (literalData z R B M) (data z R B)
    (errorNumerator z R B) (tailDenominator M) (errorNumerator z R B) (tailDenominator N)
    hM positive (le_congr (.eqRefl _) radiusEq (le_refl _)) (literal_rate z R B r hs)
  exact GaussianNamedRateTransport.transport prefixF nameF prefixF nameF _ _ _ _ _ _ positive rate
    (GaussianGammaInputProperness.code_data_cross prefixF _ _ (literal_regular z R B N hs)
      (literal_regular z R B M hs) datumEq.eqSymm)
    (cross_refl nameF _ (GaussianBarnesCanonicalValue.regular z R B hs))

def amplification (z R B : PTm n) : PTm n :=
  GaussianNameBounds.U prefixF (prefixData z R B) *
    GaussianRadiusExponentialLipschitzRate.factor (GaussianBarnesCanonicalFiniteLog.radius R)

def cutoff (p z R B : PTm n) : PTm n := endpoint (GaussianFastValueCut.exponent (amplification z R B) p) R

theorem cutoff_rate_of_le (p z R B N : PTm n) (hs : Γ ⊢[PRAAx] source z R B)
    (hN : Γ ⊢[PRAAx] le (cutoff p z R B) N) :
    Γ ⊢[PRAAx] independentRate prefixF nameF (literalData z R B N) (data z R B) one (unit p) := by
  let A := amplification z R B
  let q := GaussianFastValueCut.exponent A p
  let K := cutoff p z R B
  let C := GaussianBarnesCanonicalLogRow.boundNumerator R
  have hi := le_trans (GaussianBarnesCanonicalLogSchedule.initial_le_endpoint q R) hN
  have denominatorPositive : Γ ⊢[PRAAx] le one (tailDenominator N) :=
    tail_denominator_positive N (le_trans (GaussianBarnesCanonicalLogSchedule.initial_positive R) hi)
  have uq : Γ ⊢[PRAAx] le (unit q) (DyadicComplexLogarithm.unit q) :=
    GaussianExponentialReference.unit_monotone (le_add_right q _)
  have budget : Γ ⊢[PRAAx] le (errorNumerator z R B*unit p) (one*tailDenominator N) := by
    have e : Γ ⊢[PRAAx] errorNumerator z R B*unit p ≐ C*(A*unit p) := by
      unfold errorNumerator GaussianBarnesCanonicalTailExponential.errorNumerator A amplification C
      ipra_ring
    have pay := le_mul_mono (le_refl C) (le_trans (GaussianFastValueCut.query_budget (Γ := Γ) A p) uq)
    have denominatorLe : Γ ⊢[PRAAx] le (one*tailDenominator K) (one*tailDenominator N) := by
      unfold tailDenominator
      exact le_mul_mono (le_refl one) (le_mul_mono (le_refl (num 3)) hN)
    exact le_congr e.eqSymm (.eqRefl _) (le_trans pay
      (le_trans (GaussianBarnesCanonicalLogSchedule.suffix_budget q R) denominatorLe))
  exact GaussianNamedRateRadius.weaken prefixF nameF (literalData z R B N) (data z R B)
    (errorNumerator z R B) (tailDenominator N) one (unit p)
    denominatorPositive (unit_positive p) budget (literal_rate_at z R B N hs hi)

theorem cutoff_rate (p z R B : PTm n) (hs : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] independentRate prefixF nameF (literalData z R B (cutoff p z R B)) (data z R B) one (unit p) :=
  cutoff_rate_of_le p z R B _ hs (le_refl _)

theorem actual_Barnes_canonical_product_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (let z := var 0
     let R := var 1
     let B := var 2
     let r := var 3
     source z R B ⟶ independentRate prefixF nameF (literalData z R B (initial R+r)) (data z R B)
       (errorNumerator z R B) (tailDenominator (initial R+r))) :=
  closeUniv 4 (.impI (literal_rate _ _ _ _ Prf.hyp0))

theorem actual_Barnes_canonical_product_cutoff_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (let z := var 0
     let R := var 1
     let B := var 2
     let p := var 3
     source z R B ⟶ independentRate prefixF nameF (literalData z R B (cutoff p z R B)) (data z R B) one (unit p)) :=
  closeUniv 4 (.impI (cutoff_rate _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalProduct
