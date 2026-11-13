import DiophantineConsistency.IPRAStandardTheory
import DiophantineConsistency.IPRAExpressionNative
import DiophantineConsistency.HAAdaptiveDirectOrdinate86
import DiophantineConsistency.IPRABoundedRhoZFC

/-! Native and standard clients for the 86-operation product literal. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAStandardProduct13
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRAStandardTheory IPRANativeTheory IPRAFoundationZFCMappedNegation

local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (PRAFiniteFunctionCodes.Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

theorem native_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
    AdaptiveDirectOrdinate86Literal.naturalExpression86 🡘 ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ HAAdaptiveDirectOrdinate86.polynomialBridge

theorem literal_equivalence : standardTheory ⊢ IPRAExpressionNative.nativeNoZero
    AdaptiveDirectOrdinate86Literal.naturalExpression86 🡘 ∼mappedNativeRefutation embedding :=
  (provable_iff _).2 native_equivalence

theorem selected_foundation_consistency : standardTheory ⊢
    (Semiformula.lMap embedding FoundationZFCConsistencyNat.sourceSentence)ᴺ 🡘
      ∼mappedNativeRefutation embedding :=
  (provable_iff _).2 ⟨IPRABoundedRhoZFC.zfcEquiv⟩

theorem literal_iff_translated_consistency : standardTheory ⊢
    IPRAExpressionNative.nativeNoZero AdaptiveDirectOrdinate86Literal.naturalExpression86 🡘
      (Semiformula.lMap embedding FoundationZFCConsistencyNat.sourceSentence)ᴺ :=
  Entailment.E!_trans literal_equivalence
    (Entailment.E!_symm selected_foundation_consistency)

#print axioms DiophantineConsistency.HAAdaptiveDirectOrdinate86.polynomialBridge
#print axioms native_equivalence
#print axioms literal_equivalence
#print axioms selected_foundation_consistency
#print axioms literal_iff_translated_consistency
end DiophantineConsistency.IPRAStandardProduct13
