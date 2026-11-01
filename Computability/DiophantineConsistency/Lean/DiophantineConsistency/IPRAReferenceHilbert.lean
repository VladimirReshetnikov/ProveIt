import DiophantineConsistency.IPRAReferenceRew

/-! Preliminary mapping of intuitionistic Hilbert proofs under the embedding.
Theory-axiom and finite-context transport are not included here. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAReferenceHilbert
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open IPRAOrderErasure IPRAReferenceRew

def embedHilbert {φ : Propositionᵢ IPRAEqualityOnlyReference.language}
    (d : (𝗜𝗻𝘁¹ : Hilbertᵢ IPRAEqualityOnlyReference.language) ⊢! φ) :
    (𝗜𝗻𝘁¹ : Hilbertᵢ PRALanguage.language) ⊢! embed φ := by
  induction d with
  | @eaxm φ h =>
    let ψ := Classical.choose h
    have he := Classical.choose_spec h
    rw [← he]
    exact HilbertProofᵢ.eaxm ⟨embed ψ, rfl⟩
  | mdp d e ihd ihe => exact HilbertProofᵢ.mdp ihd ihe
  | @gen φ d ih =>
    change HilbertProofᵢ (𝗜𝗻𝘁¹ : Hilbertᵢ PRALanguage.language)
      (embed (Rewriting.free φ)) at ih
    exact HilbertProofᵢ.gen (by rw [← embed_free]; exact ih)
  | verum => exact HilbertProofᵢ.verum
  | implyK φ ψ => exact HilbertProofᵢ.implyK (embed φ) (embed ψ)
  | implyS φ ψ χ => exact HilbertProofᵢ.implyS (embed φ) (embed ψ) (embed χ)
  | and₁ φ ψ => exact HilbertProofᵢ.and₁ (embed φ) (embed ψ)
  | and₂ φ ψ => exact HilbertProofᵢ.and₂ (embed φ) (embed ψ)
  | and₃ φ ψ => exact HilbertProofᵢ.and₃ (embed φ) (embed ψ)
  | or₁ φ ψ => exact HilbertProofᵢ.or₁ (embed φ) (embed ψ)
  | or₂ φ ψ => exact HilbertProofᵢ.or₂ (embed φ) (embed ψ)
  | or₃ φ ψ χ => exact HilbertProofᵢ.or₃ (embed φ) (embed ψ) (embed χ)
  | all₁ φ t =>
    change HilbertProofᵢ (𝗜𝗻𝘁¹ : Hilbertᵢ PRALanguage.language)
      (∀⁰ embed φ 🡒 embed (φ/[t]))
    rw [embed_subst_one]
    exact HilbertProofᵢ.all₁ (embed φ) (Semiterm.lMap toNative t)
  | all₂ φ ψ =>
    change HilbertProofᵢ (𝗜𝗻𝘁¹ : Hilbertᵢ PRALanguage.language)
      (∀⁰ (embed (φ/[]) 🡒 embed ψ) 🡒 embed φ 🡒 ∀⁰ embed ψ)
    rw [embed_subst_zero]
    exact HilbertProofᵢ.all₂ (embed φ) (embed ψ)
  | ex₁ t φ =>
    change HilbertProofᵢ (𝗜𝗻𝘁¹ : Hilbertᵢ PRALanguage.language)
      (embed (φ/[t]) 🡒 ∃⁰ embed φ)
    rw [embed_subst_one]
    exact HilbertProofᵢ.ex₁ (Semiterm.lMap toNative t) (embed φ)
  | ex₂ φ ψ =>
    change HilbertProofᵢ (𝗜𝗻𝘁¹ : Hilbertᵢ PRALanguage.language)
      (∀⁰ (embed φ 🡒 embed (ψ/[])) 🡒 ∃⁰ embed φ 🡒 embed ψ)
    rw [embed_subst_zero]
    exact HilbertProofᵢ.ex₂ (embed φ) (embed ψ)

end DiophantineConsistency.IPRAReferenceHilbert
