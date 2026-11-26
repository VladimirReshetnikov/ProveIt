import IPRADerivations.Analysis.GaussianBarnesCanonicalHeadDerivative
import IPRADerivations.Analysis.GaussianBarnesCanonicalPrefactorDerivative
import IPRADerivations.Analysis.GaussianBarnesCanonicalPrefixDerivativeJoin

/-!
# Derivative quotient for the original Barnes kept prefix

The fixed head uses the original cutoff and the prefactor uses the
original two exponential names. A single explicit displacement
guard supplies the local bounds for both exponentials. The resulting
rate has the denominator used for the cofinal tail.
-/

set_option autoImplicit false
set_option maxHeartbeats 1150000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefixDerivative

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add normSq)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalPrefixDerivativeJoin (denominator)
open GaussianBarnesCanonicalValue (prefixF prefixData)
open GaussianEuclideanDistanceName (pointCN)
open GaussianL1 (norm1 normSq_le_norm1_square)
open GaussianNamedInverseRate (independentRate)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "CF" => GaussianBarnesCanonicalHeadCorrectionExponentialDerivative.incrementGain
local notation "HF" => GaussianBarnesCanonicalHeadDerivative.gain
local notation "P" => GaussianBarnesCanonicalPrefactor.nameF
local notation "pd" => GaussianBarnesCanonicalPrefactor.data
local notation "DP" => GaussianBarnesCanonicalPrefactorDerivative.derivativeF
local notation "dp" => GaussianBarnesCanonicalPrefactorDerivative.derivativeData
local notation "PF" => GaussianBarnesCanonicalPrefactorDerivative.incrementGain
local notation "PG" => GaussianBarnesCanonicalPrefactorDerivative.errorGain
local notation "PB" => GaussianBarnesCanonicalPrefactorDerivative.derivativeBound
local notation "QF" => GaussianNamedDifferenceQuotient.nameF
local notation "qd" => GaussianNamedDifferenceQuotient.data

def incrementGain (R : PTm n) : PTm n := one+CF R (initial R)+PF R
def gain (R : PTm n) : PTm n :=
  GaussianBarnesCanonicalPrefixDerivativeJoin.gain R (HF R (initial R)) (two*PG R) (PB R)*initial R

def input (z h R B : PTm n) : Fm PTm n :=
  source z R B ⋏ (source (add z h) R B ⋏ (le one (normSq h) ⋏ le (incrementGain R*norm1 h) B))

abbrev derivativeF : PR 2 := GaussianBarnesCanonicalPrefixDerivativeJoin.derivativeF DP
def derivativeData (z R B : PTm n) : PTm n :=
  GaussianBarnesCanonicalPrefixDerivativeJoin.derivativeData DP z R B (dp z B)

@[simp] theorem subst_incrementGain {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (incrementGain R) = incrementGain (Syn.subst σ R) := by simp [incrementGain,one]

@[simp] theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (gain R) = gain (Syn.subst σ R) := by simp [gain,two]

@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (z h R B : PTm n) :
    (input z h R B).subst σ = input (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) := by
  simp [input,one]

@[simp] theorem subst_derivativeData {m : ℕ} (σ : Fin n → PTm m) (z R B : PTm n) :
    Syn.subst σ (derivativeData z R B) = derivativeData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by
  simp [derivativeData]

theorem regular (z R B : PTm n) (hs : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx] pointCN derivativeF (derivativeData z R B) :=
  GaussianBarnesCanonicalPrefixDerivativeJoin.regular DP z R B (dp z B) hs
    (GaussianBarnesCanonicalPrefactorDerivative.derivative_regular z B)

theorem small_bounds (h R B : PTm n) (hs : Γ ⊢[PRAAx] le (incrementGain R*norm1 h) B) : Γ ⊢[PRAAx]
    le (norm1 h) B ⋏ (le (CF R (initial R)*norm1 h) B ⋏ le (PF R*norm1 h) B) := by
  let L := CF R (initial R)
  let M := PF R
  have first := mul_le_mul_right (Γ := Γ) (norm1 h) (le_trans (le_add_right one L) (le_add_right (one+L) M))
  have next := mul_le_mul_right (Γ := Γ) (norm1 h) (le_trans (le_add_left L one) (le_add_right (one+L) M))
  have last := mul_le_mul_right (Γ := Γ) (norm1 h) (le_add_left M (one+L))
  exact .andI (le_trans (le_congr (one_mul _) (.eqRefl _) first) hs) (.andI (le_trans next hs) (le_trans last hs))

theorem prefactor_quotient_rate (z h R B : PTm n) (hi : Γ ⊢[PRAAx] input z h R B) : Γ ⊢[PRAAx]
    independentRate (QF P P) DP (qd P P (pd (add z h) B) (pd z B) h B) (dp z B) (two*PG R*norm1 h) B := by
  have hz := hi.andE₁
  have hw := hi.andE₂.andE₁
  have hn := hi.andE₂.andE₂.andE₁
  have guards := small_bounds h R B hi.andE₂.andE₂.andE₂
  have tiny : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded h (norm1 h) := normSq_le_norm1_square h
  have raw := GaussianBarnesCanonicalPrefactorDerivative.rate z h R B (norm1 h) hz hw tiny guards.andE₂.andE₂
  exact GaussianNativeDerivativeQuotientQuadratic.rate P P DP (pd (add z h) B) (pd z B) (dp z B) h B (PG R)
    (GaussianBarnesCanonicalPrefactor.regular (add z h) B) (GaussianBarnesCanonicalPrefactor.regular z B)
    (GaussianBarnesCanonicalPrefactorDerivative.derivative_regular z B) hz.andE₁ hn raw

theorem rate (z h R B : PTm n) (hi : Γ ⊢[PRAAx] input z h R B) : Γ ⊢[PRAAx]
    independentRate (QF prefixF prefixF) derivativeF
      (qd prefixF prefixF (prefixData (add z h) R B) (prefixData z R B) h B)
      (derivativeData z R B) (gain R*norm1 h) (denominator R B) := by
  let N := initial R
  have hz := hi.andE₁
  have hw := hi.andE₂.andE₁
  have hn := hi.andE₂.andE₂.andE₁
  have guards := small_bounds h R B hi.andE₂.andE₂.andE₂
  have hhead : Γ ⊢[PRAAx] GaussianBarnesCanonicalHeadDerivative.input z h R B N :=
    .andI (.andI hz.andE₁ (.andI hz.andE₂ (.andI hw.andE₂ (normSq_le_norm1_square h))))
      (.andI hn (.andI guards.andE₁ guards.andE₂.andE₁))
  exact GaussianBarnesCanonicalPrefixDerivativeJoin.rate DP z h R B (dp z B) (HF R N) (two*PG R) (PB R) hz hw hn
    (GaussianBarnesCanonicalPrefactorDerivative.derivative_regular z B)
    (GaussianBarnesCanonicalPrefactorDerivative.derivative_samples z R B hz)
    (prefactor_quotient_rate z h R B hi) (GaussianBarnesCanonicalHeadDerivative.rate z h R B N hhead)

theorem actual_Barnes_original_kept_prefix_derivative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     input z h R B ⟶ independentRate (QF prefixF prefixF) derivativeF
       (qd prefixF prefixF (prefixData (add z h) R B) (prefixData z R B) h B)
       (derivativeData z R B) (gain R*norm1 h) (denominator R B)) :=
  closeUniv 4 (.impI (rate _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefixDerivative
