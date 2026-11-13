import CompactSymbolicModelUnconditionalIff
import PositiveModelIPRAReferenceTranslated

/-! Proposed compact free-J iPRA endpoint. This source must be compiled only
    after its two provider chains have been rebuilt in one coherent root. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Compact12IPRAEndpoint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 Ordinary12FreeJ CompactSymbolicModelIff
open PositiveModelIPRAAdapter PositiveModelIPRAStandardAdapter
open PositiveModelIPRAReferenceTranslated
open PRALanguage IPRAStandardTheory IPRAEqualityOnlyReference IPRAOrderErasure
open IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat

theorem positive_bridge : PositiveModelBridge (literal p) := by
  intro V _ _
  exact CompactSymbolicModelUnconditionalIff.model_iff

theorem standard_consistency : standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (literal p)) 🡘
      ∼mappedNativeRefutation embedding :=
  standard_equivalence_of_positive _ positive_bridge

theorem standard_translated_consistency : standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (literal p)) 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ :=
  standard_translated_of_positive _ positive_bridge

theorem reference_consistency : referenceTheory ⊢
    erase (IPRAExpressionNative.nativeNoZero (positiveShift (literal p))) 🡘
      ∼erase (mappedNativeRefutation embedding) :=
  reference_equivalence_of_positive _ positive_bridge

theorem reference_translated_consistency : referenceTheory ⊢
    erase (IPRAExpressionNative.nativeNoZero (positiveShift (literal p))) 🡘
      erase ((Semiformula.lMap embedding sourceSentence)ᴺ) :=
  reference_translated_of_positive _ positive_bridge

#print axioms Compact12IPRAEndpoint.positive_bridge
#print axioms Compact12IPRAEndpoint.standard_consistency
#print axioms Compact12IPRAEndpoint.standard_translated_consistency
#print axioms Compact12IPRAEndpoint.reference_consistency
#print axioms Compact12IPRAEndpoint.reference_translated_consistency
end Compact12IPRAEndpoint
