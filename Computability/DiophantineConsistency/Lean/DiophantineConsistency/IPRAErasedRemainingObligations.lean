import DiophantineConsistency.IPRAErasedOrderImage
import DiophantineConsistency.IPRAOrderErasureTheoryTransfer

/-! The native-to-reference transfer premise, reduced to successor
injectivity and the addition-step induction schema. This remains conditional;
the two hypotheses and a coherent replay are not supplied here. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAErasedRemainingObligations
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open IPRAOrderErasure IPRAEqualityOnlyReference

local instance : IPRAEqualityOnlyReference.language.DecidableEq where
  func := fun k => by change DecidableEq (PRAFiniteFunctionCodes.Code k); infer_instance
  rel := fun k => by change DecidableEq (EqualityRel k); infer_instance

theorem axiom_images
    (hs : referenceTheory ⊢ erase IPRANativeTheory.succInjectiveI)
    (hi : ∀ {n : ℕ} (φ : Semisentenceᵢ PRALanguage.language (n+1)),
      IPRAQuantifierFree.OpenI φ → referenceTheory ⊢ erase (IPRANativeInduction.inductionAxiom φ))
    (σ : Sentenceᵢ PRALanguage.language) (h : σ ∈ IPRANativeTheory.nativeTheory.theory) :
    referenceTheory ⊢ erase σ := by
  change IPRANativeTheory.NativeAxiom σ at h
  cases h with
  | equality he =>
    exact ⟨Axiomatized.prfAxm (IPRAErasedEqualityImages.equality_images he)⟩
  | defining hd =>
    exact ⟨Axiomatized.prfAxm (IPRAErasedDefiningImages.defining_images hd)⟩
  | basic hb =>
    cases hb with
    | succNonzero =>
      rw [IPRAErasedEqualityImages.erase_successorNonzero]
      exact ⟨Axiomatized.prfAxm ReferenceAxiom.successorNonzero⟩
    | succInjective => exact hs
    | orderDefinition => exact ⟨IPRAErasedOrderImage.order_image_provable⟩
  | induction hind =>
    rcases hind with ⟨n, φ, hopen, rfl⟩
    exact hi φ hopen

theorem transfer
    (hs : referenceTheory ⊢ erase IPRANativeTheory.succInjectiveI)
    (hi : ∀ {n : ℕ} (φ : Semisentenceᵢ PRALanguage.language (n+1)),
      IPRAQuantifierFree.OpenI φ → referenceTheory ⊢ erase (IPRANativeInduction.inductionAxiom φ))
    {σ : Sentenceᵢ PRALanguage.language} (h : IPRANativeTheory.nativeTheory ⊢ σ) :
    referenceTheory ⊢ erase σ :=
  IPRAOrderErasureTheoryTransfer.transfer_provable (axiom_images hs hi) h

end DiophantineConsistency.IPRAErasedRemainingObligations
