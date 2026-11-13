import P65IPRAHaltReverseAdapter
import DiophantineConsistency.Compact44.P65Facts

set_option autoImplicit false
noncomputable section
namespace P65UnconditionalEndpointDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 HAExpressionAssembly
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open P65IPRAHaltReverseAdapter

theorem reverse : ReverseDirection := by
  intro V _ _
  rintro ⟨v, hv, hz⟩
  exact P65Facts.halts v hv hz

theorem native_equivalence : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift P65IPRAHaltReverseAdapter.expression) 🡘
      ∼mappedNativeRefutation embedding :=
  P65IPRAHaltReverseAdapter.native_equivalence reverse

theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift P65IPRAHaltReverseAdapter.expression) 🡘
      ∼mappedNativeRefutation embedding :=
  P65IPRAHaltReverseAdapter.standard_equivalence reverse

theorem reference_equivalence : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero (positiveShift P65IPRAHaltReverseAdapter.expression)) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  P65IPRAHaltReverseAdapter.reference_equivalence reverse

#print axioms reverse
#print axioms native_equivalence
#print axioms standard_equivalence
#print axioms reference_equivalence
end P65UnconditionalEndpointDraft
