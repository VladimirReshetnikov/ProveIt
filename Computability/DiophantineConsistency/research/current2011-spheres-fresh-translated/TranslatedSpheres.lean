import FreshCarrierSpheres

/-! Current-port sphere endpoints with Foundation's GG-translated consistency sentence. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.FreshTranslatedSpheres
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage FoundationZFCConsistencyNat AdaptiveEquationSyntax2011

theorem standard_translated_equivalence71 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero
      (positiveShift (FreshCarrierSpheres.expressionAt71 CurrentWindowCarry2011.ports)) 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ := by
  apply (IPRAStandardTheory.provable_iff _).2
  obtain ⟨h⟩ := (IPRAStandardTheory.provable_iff _).1 FreshCarrierSpheres.standard_equivalence71
  have z := IPRABoundedRhoZFC.zfcEquiv
  exact ⟨Entailment.K_intro
    (Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z))
    (Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h))⟩

theorem standard_translated_equivalence72 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero
      (positiveShift (FreshCarrierSpheres.expressionAt72 CurrentWindowCarry2011.ports)) 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ := by
  apply (IPRAStandardTheory.provable_iff _).2
  obtain ⟨h⟩ := (IPRAStandardTheory.provable_iff _).1 FreshCarrierSpheres.standard_equivalence72
  have z := IPRABoundedRhoZFC.zfcEquiv
  exact ⟨Entailment.K_intro
    (Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z))
    (Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h))⟩

#print axioms standard_translated_equivalence71
#print axioms standard_translated_equivalence72
end DiophantineConsistency.FreshTranslatedSpheres
