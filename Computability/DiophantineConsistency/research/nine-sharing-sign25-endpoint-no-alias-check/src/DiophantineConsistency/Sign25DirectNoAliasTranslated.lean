import DiophantineConsistency.Sign25DirectNoAliasStandard

/-! SOURCE-ONLY candidate: translated standard endpoint. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign25DirectNoAlias
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing PRALanguage IPRANativeTheory
  IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat

theorem standard_translated_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero Sign25CurrentExpression.expression 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ := by
  apply (IPRAStandardTheory.provable_iff _).2
  obtain ⟨h⟩ := (IPRAStandardTheory.provable_iff _).1 standard_equivalence
  have z := IPRABoundedRhoZFC.zfcEquiv
  exact ⟨Entailment.K_intro
    (Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z))
    (Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h))⟩
end DiophantineConsistency.Sign25DirectNoAlias
#print axioms DiophantineConsistency.Sign25DirectNoAlias.standard_translated_equivalence
