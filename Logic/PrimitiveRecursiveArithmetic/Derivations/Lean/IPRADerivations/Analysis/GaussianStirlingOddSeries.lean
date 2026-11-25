import IPRADerivations.Analysis.GaussianStirlingDifference
import IPRADerivations.Analysis.GaussianRationalFiniteSum

/-!
# Finite odd series for the Stirling difference

A term with index j represents z^(2j+2)/(2j+3), where z = B/(2A+B).
The first K terms and the geometric remainder use only natural powers
and canonical rational arithmetic.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingOddSeries

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qzero qadd canonical)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def baseDenominator (A B : PTm n) : PTm n := two*A+B
def degree (j : PTm n) : PTm n := two*succ j
def term (A B j : PTm n) : PTm n :=
  fraction (pw B (degree j)) (succ (degree j)*pw (baseDenominator A B) (degree j))
def body : PTm 2 := term (fstT (var 1)) (sndT (var 1)) (var 0)
def partialSum (A B K : PTm n) : PTm n := GaussianRationalFiniteSum.sum body K (pairT A B)
def tailNumerator (A B K : PTm n) : PTm n := pw B (degree K)*(baseDenominator A B*baseDenominator A B)
def tailDenominator (A B K : PTm n) : PTm n :=
  succ (degree K)*pw (baseDenominator A B) (degree K)*(num 4*A*(A+B))
def tail (A B K : PTm n) : PTm n := fraction (tailNumerator A B K) (tailDenominator A B K)

@[simp] theorem subst_baseDenominator {l : ℕ} (σ : Fin n → PTm l) (A B : PTm n) :
    Syn.subst σ (baseDenominator A B) = baseDenominator (Syn.subst σ A) (Syn.subst σ B) := by simp [baseDenominator]
@[simp] theorem subst_degree {l : ℕ} (σ : Fin n → PTm l) (j : PTm n) :
    Syn.subst σ (degree j) = degree (Syn.subst σ j) := by simp [degree]
@[simp] theorem subst_term {l : ℕ} (σ : Fin n → PTm l) (A B j : PTm n) :
    Syn.subst σ (term A B j) = term (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ j) := by simp [term]
@[simp] theorem subst_partial {l : ℕ} (σ : Fin n → PTm l) (A B K : PTm n) :
    Syn.subst σ (partialSum A B K) = partialSum (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ K) := by simp [partialSum]
@[simp] theorem subst_tail {l : ℕ} (σ : Fin n → PTm l) (A B K : PTm n) :
    Syn.subst σ (tail A B K) = tail (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ K) := by
  simp [tail,tailNumerator,tailDenominator]

theorem body_at (A B j : PTm n) : Γ ⊢[PRAAx] inst2 body j (pairT A B) ≐ term A B j := by
  have e := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (term (var 0) (var 1) (var 2) : PTm 3)
    (σ := ![fstT (pairT A B),sndT (pairT A B),j]) (σ' := ![A,B,j])
    (fun i => by fin_cases i; exact fst_pair _ _; exact snd_pair _ _; exact .eqRefl _)
  simpa [body,inst2] using e

theorem partial_zero (A B : PTm n) : Γ ⊢[PRAAx] partialSum A B zero ≐ qzero :=
  GaussianRationalFiniteSum.sum_zero body (pairT A B)

theorem partial_succ (A B K : PTm n) : Γ ⊢[PRAAx] partialSum A B (succ K) ≐ qadd (partialSum A B K) (term A B K) :=
  (GaussianRationalFiniteSum.sum_succ body K (pairT A B)).eqTrans
    (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) (body_at A B K))

theorem partial_canonical (A B K : PTm n) : Γ ⊢[PRAAx] canonical (partialSum A B K) :=
  GaussianRationalFiniteSum.sum_canonical body K (pairT A B)

end LeanProofs.IPRA.Analysis.GaussianStirlingOddSeries
