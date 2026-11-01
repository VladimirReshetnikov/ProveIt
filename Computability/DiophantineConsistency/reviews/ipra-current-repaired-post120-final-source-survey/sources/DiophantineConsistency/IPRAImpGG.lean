import Foundation.FirstOrder.NegationTranslation.GoedelGentzen
/-! Intuitionistic elimination of the GG image of classical implication. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRAImpGG
open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
variable {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L}
theorem sentence_imp_doubleNegation (T : Theoryᵢ L Λ) (φ ψ : Sentence L) :
    T ⊢ (φᴺ 🡒 ψᴺ) 🡘 (φ 🡒 ψ)ᴺ := by
  obtain ⟨h⟩ := Derivation.imply_doubleNegation (Λ := Λ) (Rewriting.emb φ) (Rewriting.emb ψ)
  exact ⟨Theoryᵢ.ofHilbert (Entailment.cast h (by simp [Semiformula.emb_doubleNegation]))⟩
theorem unpack_imp_image (T : Theoryᵢ L Λ) (φ ψ : Sentence L)
    (h : T ⊢ (φ 🡒 ψ)ᴺ) : T ⊢ φᴺ 🡒 ψᴺ :=
  Entailment.mdp! (Entailment.K!_right (sentence_imp_doubleNegation T φ ψ)) h
end DiophantineConsistency.IPRAImpGG
