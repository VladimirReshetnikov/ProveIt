import P88PairModel

/-! Source-only endpoint proposal; no compilation or file binding is claimed. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.P88PairEndpoint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open IPRAOrdinary12Chain (native_of_positive standard_of_positive reference_of_positive)

theorem native_equivalence : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift P88PairModel.expression) 🡘
      ∼mappedNativeRefutation embedding :=
  native_of_positive _ P88PairModel.positiveBridge

theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift P88PairModel.expression) 🡘
      ∼mappedNativeRefutation embedding :=
  standard_of_positive _ P88PairModel.positiveBridge

theorem reference_equivalence : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero (positiveShift P88PairModel.expression)) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  reference_of_positive _ P88PairModel.positiveBridge

#print axioms native_equivalence
#print axioms standard_equivalence
#print axioms reference_equivalence
end DiophantineConsistency.P88PairEndpoint
