import DiophantineConsistency.IPRAReferenceTheoryTransfer
import DiophantineConsistency.IPRAReferenceEqualityImages
import DiophantineConsistency.IPRAReferenceInductionTransfer
import DiophantineConsistency.IPRAReferenceInductionConversion

/-! Uncompiled draft of provability comparison for equality-only sentences.
The imported reference-induction wrapper is itself uncompiled. Even a
successful replay would not alone show native formulas equivalent to their
embedded erasures, identify the endpoint consistency coding, or verify the
equation proof. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAReferenceRoundtrip
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open IPRAOrderErasure IPRAEqualityOnlyReference IPRANativeTheory

local instance : PRALanguage.language.DecidableEq where
  func := fun k => by change DecidableEq (PRAFiniteFunctionCodes.Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

theorem axiom_images (σ : Sentenceᵢ IPRAEqualityOnlyReference.language)
    (h : σ ∈ referenceTheory.theory) : nativeTheory ⊢ embed σ := by
  change ReferenceAxiom σ at h
  cases h with
  | equality he =>
    exact ⟨Axiomatized.prfAxm (NativeAxiom.equality (IPRAReferenceEqualityImages.equality_images he))⟩
  | defining hd =>
    exact ⟨Axiomatized.prfAxm (NativeAxiom.defining (IPRAReferenceImages.defining_images hd))⟩
  | successorNonzero =>
    rw [IPRAReferenceEqualityImages.embed_successorNonzero]
    exact ⟨Axiomatized.prfAxm (NativeAxiom.basic BasicAxiomI.succNonzero)⟩
  | induction φ hopen =>
    exact ⟨IPRAReferenceInductionTransfer.induction_image φ hopen⟩

theorem referenceToNative {σ : Sentenceᵢ IPRAEqualityOnlyReference.language}
    (h : referenceTheory ⊢ σ) : nativeTheory ⊢ embed σ :=
  IPRAReferenceTheoryTransfer.transfer_provable axiom_images h

theorem provability_iff {σ : Sentenceᵢ IPRAEqualityOnlyReference.language} :
    (nativeTheory ⊢ embed σ) ↔ (referenceTheory ⊢ σ) := by
  constructor
  · intro h
    simpa only [erase_embed] using IPRAReferenceInductionConversion.nativeToReference h
  · exact referenceToNative

end DiophantineConsistency.IPRAReferenceRoundtrip
