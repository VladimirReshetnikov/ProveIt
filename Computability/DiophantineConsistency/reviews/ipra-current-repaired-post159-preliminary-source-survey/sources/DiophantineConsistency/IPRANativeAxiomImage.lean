import DiophantineConsistency.IPRANativeTheory
set_option autoImplicit false
namespace DiophantineConsistency.IPRANativeAxiomImage
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open PRALanguage PRATheory IPRANativeTheory
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (PRAFiniteFunctionCodes.Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

theorem native_axiom {σ : Sentenceᵢ language} (h : σ ∈ nativeTheory.theory) : nativeTheory ⊢ σ := by
  exact ⟨Entailment.byAxm h⟩
theorem succNonzero_image : nativeTheory ⊢ succNonzeroᴺ := by
  have h : nativeTheory ⊢ succNonzeroI :=
    native_axiom (NativeAxiom.basic BasicAxiomI.succNonzero)
  simpa [succNonzero, succNonzeroI, IPRAQuantifierFree.gg_allClosure] using h
end DiophantineConsistency.IPRANativeAxiomImage
