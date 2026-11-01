import DiophantineConsistency.FoundationTheoryGG
import DiophantineConsistency.PRATheory
/-! Conditional negative-translation bridge over the full PR language. -/
set_option autoImplicit false
namespace DiophantineConsistency.IntuitionisticPRABridge
open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
open PRALanguage PRATheory

local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (PRAFiniteFunctionCodes.Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

theorem from_classical (T : Theoryᵢ language (𝗜𝗻𝘁¹ : Hilbertᵢ language))
    (hax : ∀ σ ∈ PRA, T ⊢ σᴺ) {φ : Sentence language} (h : PRA ⊢ φ) : T ⊢ φᴺ := by
  obtain ⟨p⟩ := FoundationTheoryGG.theory_intuitionistic h
  let Γ : Set (Propositionᵢ language) := Rewriting.emb '' T.theory
  have himp : Γ *⊢[𝗜𝗻𝘁¹] (⋀p.ctx 🡒 Rewriting.emb φᴺ) :=
    ⟨Context.of (FiniteContext.toDef p.prf)⟩
  have hconj : Γ *⊢[𝗜𝗻𝘁¹] ⋀p.ctx := by
    apply Conj₂!_iff_forall_provable.mpr
    intro ψ hψ
    obtain ⟨τ, hτ, rfl⟩ := p.subset ψ hψ
    obtain ⟨σ, hσ, rfl⟩ := hτ
    exact hax σ hσ
  change Γ *⊢[𝗜𝗻𝘁¹] Rewriting.emb φᴺ
  exact mdp! himp hconj
theorem from_classical_with_target (T : Theoryᵢ language (𝗜𝗻𝘁¹ : Hilbertᵢ language))
    (hax : ∀ σ ∈ PRA, T ⊢ σᴺ) {φ : Sentence language} (h : PRA ⊢ φ)
    (target : Sentenceᵢ language) (hstable : T ⊢ (φᴺ 🡒 target)) : T ⊢ target := by
  exact mdp! hstable (from_classical T hax h)
end DiophantineConsistency.IntuitionisticPRABridge
