import Foundation.FirstOrder.Intuitionistic.Deduction
set_option autoImplicit false
namespace DiophantineConsistency.IPRATheoryHilbertBridge
open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
open Rewriting HilbertProofᵢ
variable {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L} (T : Theoryᵢ L Λ)

/-- Add exactly the embeddings of the closed theory axioms. -/
def extended : Hilbertᵢ L where
  axiomSet := (Λ : Set (Propositionᵢ L)) ∪ (Rewriting.emb '' T.theory)
  rewrite_closed := by
    intro φ h f
    rcases h with h | ⟨ψ, hψ, rfl⟩
    · exact Or.inl (Λ.rewrite_closed h f)
    · right
      refine ⟨ψ, hψ, ?_⟩
      symm
      change (Rew.rewrite f ▹ (Rew.emb ▹ ψ)) = Rew.emb ▹ ψ
      rw [← TransitiveRewriting.comp_app, Rew.rewrite_comp_emb]

omit [L.DecidableEq] in
theorem le_extended : Λ ≤ extended T := by intro φ h; exact Or.inl h

/-- A finite-context theory proof becomes a proof in the extended calculus. -/
def theoryToExtended {φ : Sentenceᵢ L} (b : T ⊢! φ) : extended T ⊢! Rewriting.emb φ := by
  have hp : extended T ⊢! ⋀b.ctx 🡒 Rewriting.emb φ := HilbertProofᵢ.ofLE (le_extended T) b.prf
  have hc : extended T ⊢! ⋀b.ctx := Entailment.Conj₂_intro b.ctx (fun ψ hψ =>
    HilbertProofᵢ.eaxm (Or.inr (b.subset ψ hψ)))
  exact hp ⨀ hc
/-- Interpret each extended-calculus proof in the closed theory context. -/
noncomputable def extendedToContext {φ : Propositionᵢ L} :
    extended T ⊢! φ → (Rewriting.emb '' T.theory) *⊢[Λ]! φ
  | .eaxm h => by
    classical
    by_cases hΛ : φ ∈ Λ
    · exact Entailment.Context.of (HilbertProofᵢ.eaxm hΛ)
    · exact Entailment.Context.byAxm (Or.resolve_left h hΛ)
  | .mdp b d => (extendedToContext b) ⨀ (extendedToContext d)
  | .gen b => by
    let c := extendedToContext b
    have hclosed : ∀ ψ ∈ c.ctx, shift ψ = ψ := by
      intro ψ hψ
      rcases c.subset ψ hψ with ⟨σ, _, rfl⟩
      change (Rew.shift ▹ (Rew.emb ▹ σ)) = Rew.emb ▹ σ
      rw [← TransitiveRewriting.comp_app, Rew.shift_comp_emb]
    have heq : c.ctx⁺ = c.ctx := by
      unfold shifts
      have hm : c.ctx.map (⇑shift) = c.ctx.map id := by
        apply List.map_congr_left
        intro ψ hψ
        exact hclosed ψ hψ
      simpa only [List.map_id] using hm
    exact ⟨c.ctx, c.subset, HilbertProofᵢ.geNOverFiniteContext (by simpa only [heq] using c.prf)⟩
  | .verum => Entailment.Context.of HilbertProofᵢ.verum
  | .implyK φ ψ => Entailment.Context.of (HilbertProofᵢ.implyK φ ψ)
  | .implyS φ ψ χ => Entailment.Context.of (HilbertProofᵢ.implyS φ ψ χ)
  | .and₁ φ ψ => Entailment.Context.of (HilbertProofᵢ.and₁ φ ψ)
  | .and₂ φ ψ => Entailment.Context.of (HilbertProofᵢ.and₂ φ ψ)
  | .and₃ φ ψ => Entailment.Context.of (HilbertProofᵢ.and₃ φ ψ)
  | .or₁ φ ψ => Entailment.Context.of (HilbertProofᵢ.or₁ φ ψ)
  | .or₂ φ ψ => Entailment.Context.of (HilbertProofᵢ.or₂ φ ψ)
  | .or₃ φ ψ χ => Entailment.Context.of (HilbertProofᵢ.or₃ φ ψ χ)
  | .all₁ φ t => Entailment.Context.of (HilbertProofᵢ.all₁ φ t)
  | .all₂ φ ψ => Entailment.Context.of (HilbertProofᵢ.all₂ φ ψ)
  | .ex₁ t φ => Entailment.Context.of (HilbertProofᵢ.ex₁ t φ)
  | .ex₂ φ ψ => Entailment.Context.of (HilbertProofᵢ.ex₂ φ ψ)

/-- Interpret an extended proof of a sentence as a theory proof. -/
noncomputable def extendedToTheory {φ : Sentenceᵢ L} (b : extended T ⊢! Rewriting.emb φ) : T ⊢! φ :=
  extendedToContext T b
end DiophantineConsistency.IPRATheoryHilbertBridge
