import DiophantineConsistency.Sign17DirectNoAliasStandard

/-! SOURCE-ONLY candidate: translated standard endpoint. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17DirectNoAlias
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing PRALanguage IPRANativeTheory
  IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat

attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  Sign17CurrentExpression.expression SharingSeed17Degree96.seed
  CurrentWindowCarry2011.ports IPRAExpressionNative.nativeNoZero

theorem standard_translated_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero Sign17CurrentExpression.expression 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ := by
  apply (IPRAStandardTheory.provable_iff _).2
  obtain ⟨h⟩ := (IPRAStandardTheory.provable_iff _).1 standard_equivalence
  have z := IPRABoundedRhoZFC.zfcEquiv
  exact ⟨Entailment.K_intro
    (Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z))
    (Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h))⟩
end DiophantineConsistency.Sign17DirectNoAlias
#print axioms DiophantineConsistency.Sign17DirectNoAlias.standard_translated_equivalence
