import Foundation.FirstOrder.NegationTranslation.GoedelGentzen
/-! The Gödel–Gentzen translation of a classical iff is equivalent, in
intuitionistic logic, to the iff between the translated sides. -/
open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
set_option autoImplicit false
namespace DiophantineConsistency.IPRAIffGG
variable {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L}
theorem iff_doubleNegation (φ ψ : Proposition L) :
    Λ ⊢ (φᴺ 🡘 ψᴺ) 🡘 (φ 🡘 ψ)ᴺ := by
  obtain ⟨h₁⟩ := Derivation.imply_doubleNegation (Λ := Λ) φ ψ
  obtain ⟨h₂⟩ := Derivation.imply_doubleNegation (Λ := Λ) ψ φ
  apply Nonempty.intro
  simpa only [LogicalConnective.iff, Semiformula.doubleNegation_and] using
    (Entailment.EKK_of_E_of_E h₁ h₂)
theorem sentence_iff_doubleNegation (T : Theoryᵢ L Λ) (φ ψ : Sentence L) :
    T ⊢ (φᴺ 🡘 ψᴺ) 🡘 (φ 🡘 ψ)ᴺ := by
  obtain ⟨h⟩ := iff_doubleNegation (Λ := Λ) (Rewriting.emb φ) (Rewriting.emb ψ)
  exact ⟨Theoryᵢ.ofHilbert (Entailment.cast h (by simp [Semiformula.emb_doubleNegation]))⟩
theorem unpack_iff_image (T : Theoryᵢ L Λ) (φ ψ : Sentence L)
    (h : T ⊢ (φ 🡘 ψ)ᴺ) : T ⊢ φᴺ 🡘 ψᴺ :=
  Entailment.mdp! (Entailment.K!_right (sentence_iff_doubleNegation T φ ψ)) h
theorem sentence_neg_doubleNegation (T : Theoryᵢ L Λ) (φ : Sentence L) :
    T ⊢ (∼φᴺ) 🡘 (∼φ)ᴺ := by
  obtain ⟨h⟩ := Derivation.neg_doubleNegation (Λ := Λ) (Rewriting.emb φ)
  exact ⟨Theoryᵢ.ofHilbert (Entailment.cast h (by simp [Semiformula.emb_doubleNegation]))⟩

theorem unpack_neg_image (T : Theoryᵢ L Λ) (φ : Sentence L)
    (h : T ⊢ (∼φ)ᴺ) : T ⊢ ∼φᴺ :=
  Entailment.mdp! (Entailment.K!_right (sentence_neg_doubleNegation T φ)) h
/-- Unpack the GG image of a comparison with classical negation. The right
side remains `∼ψᴺ`; this does not replace it by `∼ψ` in intuitionistic logic. -/
theorem unpack_iff_neg_image (T : Theoryᵢ L Λ) (φ ψ : Sentence L)
    (h : T ⊢ (φ 🡘 ∼ψ)ᴺ) : T ⊢ φᴺ 🡘 ∼ψᴺ :=
  Entailment.E!_trans (unpack_iff_image T φ (∼ψ) h)
    (Entailment.E!_symm (sentence_neg_doubleNegation T ψ))
end DiophantineConsistency.IPRAIffGG
