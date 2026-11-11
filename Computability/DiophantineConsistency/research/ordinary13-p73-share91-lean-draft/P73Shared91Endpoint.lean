import P73Shared91Model

/-! Uncompiled native, standard, and equality-only iPRA clients. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.P73Shared91Endpoint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open IPRAOrdinary12Chain (native_of_positive standard_of_positive reference_of_positive)
open P73Shared91Model (expression positiveBridge)

theorem native_equivalence : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift expression) 🡘
      ∼mappedNativeRefutation embedding :=
  native_of_positive _ positiveBridge

theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift expression) 🡘
      ∼mappedNativeRefutation embedding :=
  standard_of_positive _ positiveBridge

theorem reference_equivalence : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero (positiveShift expression)) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  reference_of_positive _ positiveBridge

end DiophantineConsistency.P73Shared91Endpoint

#print axioms DiophantineConsistency.P73Shared91Endpoint.native_equivalence
#print axioms DiophantineConsistency.P73Shared91Endpoint.standard_equivalence
#print axioms DiophantineConsistency.P73Shared91Endpoint.reference_equivalence
