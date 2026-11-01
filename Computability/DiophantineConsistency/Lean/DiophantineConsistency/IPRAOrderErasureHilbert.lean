import DiophantineConsistency.IPRAOrderErasureRew

/-! Preliminary erasure of intuitionistic Hilbert proof trees. Theory-axiom
images and finite-context transport are not included here. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAOrderErasureHilbert
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open IPRAOrderErasure IPRAOrderErasureRew

def eraseHilbert {φ : Propositionᵢ PRALanguage.language}
    (d : (𝗜𝗻𝘁¹ : Hilbertᵢ PRALanguage.language) ⊢! φ) :
    (𝗜𝗻𝘁¹ : Hilbertᵢ IPRAEqualityOnlyReference.language) ⊢! erase φ := by
  induction d with
  | @eaxm φ h =>
    let ψ := Classical.choose h
    have he := Classical.choose_spec h
    rw [← he]
    exact HilbertProofᵢ.eaxm ⟨erase ψ, rfl⟩
  | mdp d e ihd ihe => exact HilbertProofᵢ.mdp ihd ihe
  | @gen φ d ih =>
    change HilbertProofᵢ (𝗜𝗻𝘁¹ : Hilbertᵢ IPRAEqualityOnlyReference.language)
      (erase (Rewriting.free φ)) at ih
    exact HilbertProofᵢ.gen (by rw [← erase_free]; exact ih)
  | verum => exact HilbertProofᵢ.verum
  | implyK φ ψ => exact HilbertProofᵢ.implyK (erase φ) (erase ψ)
  | implyS φ ψ χ => exact HilbertProofᵢ.implyS (erase φ) (erase ψ) (erase χ)
  | and₁ φ ψ => exact HilbertProofᵢ.and₁ (erase φ) (erase ψ)
  | and₂ φ ψ => exact HilbertProofᵢ.and₂ (erase φ) (erase ψ)
  | and₃ φ ψ => exact HilbertProofᵢ.and₃ (erase φ) (erase ψ)
  | or₁ φ ψ => exact HilbertProofᵢ.or₁ (erase φ) (erase ψ)
  | or₂ φ ψ => exact HilbertProofᵢ.or₂ (erase φ) (erase ψ)
  | or₃ φ ψ χ => exact HilbertProofᵢ.or₃ (erase φ) (erase ψ) (erase χ)
  | all₁ φ t =>
    change HilbertProofᵢ (𝗜𝗻𝘁¹ : Hilbertᵢ IPRAEqualityOnlyReference.language)
      (∀⁰ erase φ 🡒 erase (φ/[t]))
    rw [erase_subst_one]
    exact HilbertProofᵢ.all₁ (erase φ) (Semiterm.lMap termsToReference t)
  | all₂ φ ψ =>
    change HilbertProofᵢ (𝗜𝗻𝘁¹ : Hilbertᵢ IPRAEqualityOnlyReference.language)
      (∀⁰ (erase (φ/[]) 🡒 erase ψ) 🡒 erase φ 🡒 ∀⁰ erase ψ)
    rw [erase_subst_zero]
    exact HilbertProofᵢ.all₂ (erase φ) (erase ψ)
  | ex₁ t φ =>
    change HilbertProofᵢ (𝗜𝗻𝘁¹ : Hilbertᵢ IPRAEqualityOnlyReference.language)
      (erase (φ/[t]) 🡒 ∃⁰ erase φ)
    rw [erase_subst_one]
    exact HilbertProofᵢ.ex₁ (Semiterm.lMap termsToReference t) (erase φ)
  | ex₂ φ ψ =>
    change HilbertProofᵢ (𝗜𝗻𝘁¹ : Hilbertᵢ IPRAEqualityOnlyReference.language)
      (∀⁰ (erase φ 🡒 erase (ψ/[])) 🡒 ∃⁰ erase φ 🡒 erase ψ)
    rw [erase_subst_zero]
    exact HilbertProofᵢ.ex₂ (erase φ) (erase ψ)

end DiophantineConsistency.IPRAOrderErasureHilbert
