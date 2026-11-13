import DiophantineConsistency.IPRAStandardTheory
import DiophantineConsistency.IPRASquareSumsNative
import DiophantineConsistency.IPRABoundedRhoZFC

/-! Standard-theory client for the 87-operation sum-of-squares literal. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAStandardSquareSums13
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRAStandardTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011

local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (PRAFiniteFunctionCodes.Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

theorem literal_equivalence : standardTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveDirectOrdinateSquareSumsLiteral.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  (provable_iff _).2 IPRASquareSumsNative.literal_equivalence

theorem selected_foundation_consistency : standardTheory ⊢
    (Semiformula.lMap embedding FoundationZFCConsistencyNat.sourceSentence)ᴺ 🡘
      ∼mappedNativeRefutation embedding :=
  (provable_iff _).2 ⟨IPRABoundedRhoZFC.zfcEquiv⟩

theorem literal_iff_translated_consistency : standardTheory ⊢
    IPRAExpressionNative.nativeNoZero
      (positiveShift (AdaptiveDirectOrdinateSquareSumsLiteral.literal CurrentWindowCarry2011.ports)) 🡘
        (Semiformula.lMap embedding FoundationZFCConsistencyNat.sourceSentence)ᴺ :=
  Entailment.E!_trans literal_equivalence
    (Entailment.E!_symm selected_foundation_consistency)

#print axioms DiophantineConsistency.IPRASquareSumsNative.sameZero
#print axioms DiophantineConsistency.IPRASquareSumsNative.bridge
#print axioms DiophantineConsistency.IPRASquareSumsNative.equivalence
#print axioms DiophantineConsistency.IPRASquareSumsNative.literal_eq
#print axioms DiophantineConsistency.IPRASquareSumsNative.literal_equivalence
#print axioms literal_equivalence
#print axioms selected_foundation_consistency
#print axioms literal_iff_translated_consistency
end DiophantineConsistency.IPRAStandardSquareSums13
