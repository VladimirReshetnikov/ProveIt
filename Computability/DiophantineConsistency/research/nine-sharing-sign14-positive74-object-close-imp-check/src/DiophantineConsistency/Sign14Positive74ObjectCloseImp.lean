import DiophantineConsistency.Sign14Positive74ObjectCloseBind

/-! SOURCE ONLY: close a native open implication under a closed antecedent. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectCloseImp
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment LO.Entailment.FiniteContext
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage PRATheory IPRANativeTheory IPRATheoryHilbertBridge
open Sign14Positive74ObjectCloseBind
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (PRAFiniteFunctionCodes.Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

def closeContext (Γ : List (Propositionᵢ language)) (hΓ : Γ⁺ = Γ)
    {p : Propositionᵢ language} (h : Γ ⊢[extended nativeTheory]! p) :
    (m : ℕ) → Γ ⊢[extended nativeTheory]! ∀⁰* (Rew.fixitr 0 m ▹ p)
  | 0 => by simpa using h
  | m+1 => by
      simp only [LawfulSyntacticRewriting.allClosure_fixitr]
      apply HilbertProofᵢ.geNOverFiniteContext
      rw [hΓ]
      simpa using closeContext Γ hΓ h m

def closeImp14 (σ : Sentenceᵢ language) (φ : Semisentenceᵢ language 14)
    (h : extended nativeTheory ⊢! (Rewriting.emb σ 🡒 (Rew.embSubsts freeVec ▹ φ))) :
    nativeTheory ⊢! (σ 🡒 ∀⁰* φ) := by
  let P : Propositionᵢ language := Rewriting.emb σ
  have hc : [P] ⊢[extended nativeTheory]! (Rew.embSubsts freeVec ▹ φ) :=
    (FiniteContext.of h) ⨀ FiniteContext.byAxm₀
  have hshift : ([P] : List (Propositionᵢ language))⁺ = [P] := by
    simp [P, Rewriting.shifts, Rewriting.rew_emb_eq_emb]
  have hall := closeContext [P] hshift hc 14
  rw [bindSentence14 φ] at hall
  have himp : extended nativeTheory ⊢! P 🡒 Rewriting.emb (∀⁰* φ) := by
    simpa [List.conj₂] using FiniteContext.toDef hall
  apply extendedToTheory (T := nativeTheory)
  simpa only [P, LogicalConnective.HomClass.map_imply] using himp
end DiophantineConsistency.Sign14Positive74ObjectCloseImp
#print axioms DiophantineConsistency.Sign14Positive74ObjectCloseImp.closeImp14
