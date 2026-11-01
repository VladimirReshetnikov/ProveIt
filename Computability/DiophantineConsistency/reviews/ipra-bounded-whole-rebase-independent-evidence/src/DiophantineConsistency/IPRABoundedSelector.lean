import DiophantineConsistency.PRABoundedSelector
import DiophantineConsistency.IPRANativeOpenDecidable
import DiophantineConsistency.IPRAOpenAtomDecision
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRABoundedSelector
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRABoundedSelector
open IPRANativeTheory IPRANativeFormula IPRANativeOpenDecision IPRANativeEqualityDecidable
open IPRAOpenAtomDecision IPRATheoryHilbertBridge IPRATheoryInstantiation
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

theorem openAtoms : (φ : Proposition language) → φ.Open → AtomDecisions φ
  | .rel r v, _ => by
    rw [AtomDecisions.eq_1]
    exact ⟨atomDec equalityDecidable r v⟩
  | .nrel r v, _ => by
    rw [AtomDecisions.eq_2]
    exact ⟨atomDec equalityDecidable r v⟩
  | ⊤, _ => by change AtomDecisions .verum; rw [AtomDecisions.eq_3]; trivial
  | ⊥, _ => by change AtomDecisions .falsum; rw [AtomDecisions.eq_4]; trivial
  | φ ⋏ ψ, h => by
    simp only [Semiformula.open_and] at h
    change AtomDecisions (.and φ ψ)
    rw [AtomDecisions.eq_5]
    exact ⟨openAtoms φ h.1, openAtoms ψ h.2⟩
  | φ ⋎ ψ, h => by
    simp only [Semiformula.open_or] at h
    change AtomDecisions (.or φ ψ)
    rw [AtomDecisions.eq_6]
    exact ⟨openAtoms φ h.1, openAtoms ψ h.2⟩
  | ∀⁰ φ, h => by simp at h
  | ∃⁰ φ, h => by simp at h
  termination_by φ _ => φ.complexity

def selectorOpen {n : ℕ} (good : Code (n+1)) (v : Fin (n+2) → Term language ℕ) :
    extended nativeTheory ⊢! native (Rew.embSubsts v ▹ matrix good) := by
  have ht := IPRAFullGGTransfer.from_classical (PRA_proves_selector good)
  have hgg : nativeTheory ⊢! ∀⁰* (matrix good)ᴺ := by
    have h := Classical.choice ht
    simpa only [sentence, IPRAQuantifierFree.gg_allClosure] using h
  have hs := instantiateTheory (T := nativeTheory) ((matrix good)ᴺ) hgg v
  have ho : (Rew.embSubsts v ▹ matrix good).Open := by simpa using matrix_open good
  have hr := backward (Rew.embSubsts v ▹ matrix good) (openAtoms _ ho)
  apply hr ⨀ ?_
  simpa only [Semiformula.rew_doubleNegation] using hs
end DiophantineConsistency.IPRABoundedSelector
