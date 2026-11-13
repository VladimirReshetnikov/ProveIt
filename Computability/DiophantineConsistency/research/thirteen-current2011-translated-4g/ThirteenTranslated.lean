import DiophantineConsistency.ModelThirteenForms
/-! Mapped Gödel–Gentzen consistency endpoints for both thirteen-variable forms. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ThirteenTranslated
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage FoundationZFCConsistencyNat AdaptiveEquationSyntax2011

/-- The 13/70 endpoint with mapped translated ZFC consistency. -/
theorem standard_translated_equivalence70 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero
      (positiveShift (ModelThirteenForms.expressionAt70 CurrentWindowCarry2011.ports)) 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ := by
  apply (IPRAStandardTheory.provable_iff _).2
  obtain ⟨h⟩ := (IPRAStandardTheory.provable_iff _).1 ModelThirteenForms.standard_equivalence70
  have z := IPRABoundedRhoZFC.zfcEquiv
  exact ⟨Entailment.K_intro
    (Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z))
    (Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h))⟩

/-- The 13/71 endpoint with mapped translated ZFC consistency. -/
theorem standard_translated_equivalence71 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero
      (positiveShift (ModelThirteenForms.expressionAt71 CurrentWindowCarry2011.ports)) 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ := by
  apply (IPRAStandardTheory.provable_iff _).2
  obtain ⟨h⟩ := (IPRAStandardTheory.provable_iff _).1 ModelThirteenForms.standard_equivalence71
  have z := IPRABoundedRhoZFC.zfcEquiv
  exact ⟨Entailment.K_intro
    (Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z))
    (Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h))⟩

#print axioms standard_translated_equivalence70
#print axioms standard_translated_equivalence71
end DiophantineConsistency.ThirteenTranslated
