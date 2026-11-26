import IPRADerivations.Analysis.GaussianBarnesCanonicalPrefactor
import IPRADerivations.Analysis.GaussianBarnesCanonicalHead
import IPRADerivations.Analysis.GaussianBarnesCanonicalTailExponential
import IPRADerivations.Analysis.GaussianNamedDifferenceRate
import IPRADerivations.Analysis.GaussianNamedRateRadius

/-!
# The split original Barnes value on a rational Gaussian disk

The fixed direct head is multiplied by the literal prefactor and the
exponential of the original cofinal cubic logarithm. The same two
fixed factors multiply each finite logarithmic-tail exponential.
Their computed bound propagates the tail comparison to the complete
sampler at independent observation clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalValue

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial initial_positive)
open GaussianBarnesCanonicalLogTail (tailDenominator tail_denominator_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U all_samples_bounded)
open GaussianNamedInverseRate (independentRate)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "P" => GaussianBarnesCanonicalPrefactor.nameF
local notation "H" => GaussianBarnesCanonicalHead.nameF
local notation "T" => GaussianBarnesCanonicalTailExponential.nameF
local notation "E" => GaussianBarnesCanonicalTailExponential.finiteF
local notation "Td" => GaussianBarnesCanonicalTailExponential.data

def prefixF : PR 2 := multiplyF P H
def prefixData (z R B : PTm n) : PTm n :=
  multiplyData P H (GaussianBarnesCanonicalPrefactor.data z B) (GaussianBarnesCanonicalHead.headData z R B (initial R))

def nameF : PR 2 := multiplyF prefixF T
def data (z R B : PTm n) : PTm n := multiplyData prefixF T (prefixData z R B) (Td z R B)
def finiteF : PR 2 := multiplyF prefixF E
def finiteData (z R B r : PTm n) : PTm n :=
  multiplyData prefixF E (prefixData z R B) (GaussianBarnesCanonicalTailExponential.finiteData z R B (initial R) r)

def errorNumerator (z R B : PTm n) : PTm n :=
  U prefixF (prefixData z R B)*GaussianBarnesCanonicalTailExponential.errorNumerator R

@[simp] theorem subst_prefixData {m : ℕ} (σ : Fin n → PTm m) (z R B : PTm n) :
    Syn.subst σ (prefixData z R B) = prefixData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by
  simp [prefixData,GaussianBarnesCanonicalHead.headData]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z R B : PTm n) :
    Syn.subst σ (data z R B) = data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by simp [data]

@[simp] theorem subst_finiteData {m : ℕ} (σ : Fin n → PTm m) (z R B r : PTm n) :
    Syn.subst σ (finiteData z R B r) = finiteData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ r) := by
  simp [finiteData]

theorem prefix_regular (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] pointCN prefixF (prefixData z R B) :=
  multiply_fast _ _ _ _ (GaussianBarnesCanonicalPrefactor.regular z B)
    (GaussianBarnesCanonicalHead.regular z R B zero (initial R) h)

theorem regular (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] pointCN nameF (data z R B) :=
  multiply_fast _ _ _ _ (prefix_regular z R B h) (GaussianBarnesCanonicalTailExponential.regular z R B h)

theorem finite_rate (z R B r : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    independentRate finiteF nameF (finiteData z R B r) (data z R B)
      (errorNumerator z R B) (tailDenominator (initial R+r)) := by
  let x := prefixData z R B
  let y := GaussianBarnesCanonicalTailExponential.finiteData z R B (initial R) r
  let w := Td z R B
  let C := GaussianBarnesCanonicalTailExponential.errorNumerator R
  let D := tailDenominator (initial R+r)
  let M := U E y
  let K := U prefixF x
  have hx := prefix_regular z R B h
  have hy := GaussianBarnesCanonicalTailExponential.finite_regular z R B (initial R) r
    (GaussianBarnesCanonicalLogCofinalRate.initial_source z R B h)
  have hw := GaussianBarnesCanonicalTailExponential.regular z R B h
  have hD : Γ ⊢[PRAAx] le one D :=
    tail_denominator_positive _ (le_trans (initial_positive R) (le_add_right _ _))
  have rate := GaussianNamedMultiplyRate.independent_rate prefixF E prefixF T x y x w zero one C D M K
    (le_refl one) hD hx hy hx hw (all_samples_bounded E y hy) (all_samples_bounded prefixF x hx)
    (GaussianNamedDifferenceRate.self_rate prefixF x hx)
    (GaussianBarnesCanonicalTailExponential.exponential_tail_rate z R B r h)
  exact GaussianNamedRateRadius.weaken finiteF nameF (finiteData z R B r) (data z R B)
    (GaussianNamedMultiplyRate.leadingNumerator zero one C D M K) (one*D) (errorNumerator z R B) D
    (le_congr (.eqRefl _) (one_mul D).eqSymm hD) hD
    (le_of_eq_add (d := zero) (by
      change Γ ⊢[PRAAx] (K*C)*(one*D) ≐ (M*zero*D+K*C*one)*D+zero
      ipra_ring)) rate

theorem actual_Barnes_split_value_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶ pointCN nameF (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (regular _ _ _ Prf.hyp0))

theorem actual_Barnes_split_value_finite_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (let z := var 0
     let R := var 1
     let B := var 2
     let r := var 3
     source z R B ⟶ independentRate finiteF nameF (finiteData z R B r) (data z R B)
       (errorNumerator z R B) (tailDenominator (initial R+r))) :=
  closeUniv 4 (.impI (finite_rate _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalValue
