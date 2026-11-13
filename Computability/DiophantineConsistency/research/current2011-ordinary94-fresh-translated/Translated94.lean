import FreshCarrier94

/-! Fresh-base 67/94 endpoint with the mapped Gödel–Gentzen ZFC consistency sentence. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.FreshTranslated94
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage FoundationZFCConsistencyNat AdaptiveEquationSyntax2011

theorem standard_translated_equivalence94 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero Carrier94Syntax.naturalExpression94 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ := by
  apply (IPRAStandardTheory.provable_iff _).2
  obtain ⟨h⟩ := (IPRAStandardTheory.provable_iff _).1 FreshCarrier94.standard_equivalence94
  have z := IPRABoundedRhoZFC.zfcEquiv
  exact ⟨Entailment.K_intro
    (Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z))
    (Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h))⟩

#print axioms standard_translated_equivalence94
end DiophantineConsistency.FreshTranslated94
