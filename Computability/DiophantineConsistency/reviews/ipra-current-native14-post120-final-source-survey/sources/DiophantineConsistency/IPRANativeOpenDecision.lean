import DiophantineConsistency.IPRANativeAtomCoverage
import Foundation.Meta.IntProver
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.IPRANativeOpenDecision
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.IPRANativeTheory DiophantineConsistency.IPRATheoryHilbertBridge
open DiophantineConsistency.IPRANativeAtomStability DiophantineConsistency.IPRANativeAtomCoverage
open DiophantineConsistency.IPRANativeFormula
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance
local instance : Entailment.Int (extended nativeTheory) where
  efq := HilbertProofᵢ.eaxm (Or.inl (by simp [Hilbertᵢ.Intuitionistic]))

def decNeg (a : Propositionᵢ language) :
    extended nativeTheory ⊢! (a ⋎ ∼a) 🡒 (∼a ⋎ ∼∼a) := by
  apply Classical.choice
  change extended nativeTheory ⊢ _
  int_prover
def decAnd (a b : Propositionᵢ language) :
    extended nativeTheory ⊢! (a ⋎ ∼a) 🡒 (b ⋎ ∼b) 🡒 ((a ⋏ b) ⋎ ∼(a ⋏ b)) := by
  apply Classical.choice
  change extended nativeTheory ⊢ _
  int_prover
def decOr (a b : Propositionᵢ language) :
    extended nativeTheory ⊢! (a ⋎ ∼a) 🡒 (b ⋎ ∼b) 🡒 ((a ⋎ b) ⋎ ∼(a ⋎ b)) := by
  apply Classical.choice
  change extended nativeTheory ⊢ _
  int_prover
def atomDec (h : nativeTheory ⊢! eqDecSentence) {k : ℕ}
    (r : language.Rel k) (v : Fin k → Term language ℕ) :
    extended nativeTheory ⊢! native (Semiformula.rel r v) ⋎ ∼native (Semiformula.rel r v) := by
  cases r with
  | eq =>
    change extended nativeTheory ⊢! (Semiformulaᵢ.rel Language.ORing.Rel.eq v) ⋎ ∼(Semiformulaᵢ.rel Language.ORing.Rel.eq v)
    have hh := eqDecOpen h (v 0) (v 1)
    rw [Matrix.fun_eq_vec_two v]
    exact hh
  | lt =>
    change extended nativeTheory ⊢! (Semiformulaᵢ.rel Language.ORing.Rel.lt v) ⋎ ∼(Semiformulaᵢ.rel Language.ORing.Rel.lt v)
    have hh := orderDecOpen h (v 0) (v 1)
    rw [Matrix.fun_eq_vec_two v]
    exact hh

def openDecision (heq : nativeTheory ⊢! eqDecSentence) :
    (φ : Proposition language) → φ.Open → extended nativeTheory ⊢! native φ ⋎ ∼native φ
  | .rel r v, _ => atomDec heq r v
  | .nrel r v, _ => (decNeg (native (.rel r v))) ⨀ atomDec heq r v
  | ⊤, _ => Entailment.A_intro_left HilbertProofᵢ.verum
  | ⊥, _ => Entailment.A_intro_right Entailment.C_id
  | φ ⋏ ψ, h => by
    simp only [Semiformula.open_and] at h
    exact decAnd (native φ) (native ψ) ⨀ openDecision heq φ h.1 ⨀ openDecision heq ψ h.2
  | φ ⋎ ψ, h => by
    simp only [Semiformula.open_or] at h
    exact decOr (native φ) (native ψ) ⨀ openDecision heq φ h.1 ⨀ openDecision heq ψ h.2
  | ∀⁰ φ, h => by simp at h
  | ∃⁰ φ, h => by simp at h
  termination_by φ _ => φ.complexity

def openStability (heq : nativeTheory ⊢! eqDecSentence) (φ : Proposition language) (h : φ.Open) :
    extended nativeTheory ⊢! ∼∼native φ 🡒 native φ :=
  stableOfDec (native φ) (openDecision heq φ h)
end DiophantineConsistency.IPRANativeOpenDecision
