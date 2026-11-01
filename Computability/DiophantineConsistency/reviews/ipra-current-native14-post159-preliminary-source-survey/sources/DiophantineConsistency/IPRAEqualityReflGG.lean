import DiophantineConsistency.IPRANativeEquationImages
/-! The actual classical equality-reflexivity axiom has a GG proof in native
intuitionistic PRA. Other equality axiom families remain separate. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRAEqualityImage
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

theorem refl_image : nativeTheory ⊢ (Theory.Eq.refl language)ᴺ := by
  have h : nativeTheory ⊢ eqReflI := IPRANativeAxiomImage.native_axiom (NativeAxiom.equality EqualityAxiomI.refl)
  have hh := IPRANativeEquationImages.equality_image (#0 : TermN 1) #0
  have hgg := Entailment.mdp! hh h
  change nativeTheory ⊢ (equalClosure (#0 : TermN 1) #0)ᴺ
  exact hgg
end DiophantineConsistency.IPRAEqualityImage
