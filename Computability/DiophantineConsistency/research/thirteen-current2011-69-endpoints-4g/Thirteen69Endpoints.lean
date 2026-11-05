import DiophantineConsistency.ModelThirteenCarrier
/-! Focused standard and mapped translated 13/69/174 endpoints. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Thirteen69Endpoints
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage FoundationZFCConsistencyNat AdaptiveEquationSyntax2011 IPRAFoundationZFCMappedNegation

theorem standard_equivalence69 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero
      (positiveShift (ModelThirteenCarrier.expressionAt69 CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  ModelThirteenCarrier.standard_equivalence69

theorem standard_translated_equivalence69 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero
      (positiveShift (ModelThirteenCarrier.expressionAt69 CurrentWindowCarry2011.ports)) 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ := by
  apply (IPRAStandardTheory.provable_iff _).2
  obtain ⟨h⟩ := (IPRAStandardTheory.provable_iff _).1 standard_equivalence69
  have z := IPRABoundedRhoZFC.zfcEquiv
  exact ⟨Entailment.K_intro
    (Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z))
    (Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h))⟩

#print axioms standard_equivalence69
#print axioms standard_translated_equivalence69
end DiophantineConsistency.Thirteen69Endpoints
