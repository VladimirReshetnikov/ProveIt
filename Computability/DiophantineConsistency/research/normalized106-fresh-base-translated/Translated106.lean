import FreshModel106

/-! The same 67/106 endpoint with Foundation's mapped and Gödel–Gentzen
translated ZFC consistency sentence. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.FreshTranslated106
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage FoundationZFCConsistencyNat ModelCarrierCurrent AdaptiveEquationSyntax2011

theorem standard_translated_equivalence106 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero
      (positiveShift (expressionAt106 CurrentWindowCarry2011.ports)) 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ := by
  apply (IPRAStandardTheory.provable_iff _).2
  obtain ⟨h⟩ := FreshModel106.native_equivalence106
  have z := IPRABoundedRhoZFC.zfcEquiv
  exact ⟨Entailment.K_intro
    (Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z))
    (Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h))⟩

#print axioms standard_translated_equivalence106
end DiophantineConsistency.FreshTranslated106
