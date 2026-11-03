import SumSquaresModelIff
import PositiveModelIPRAReferenceTranslated

/-! Proposed iPRA clients for the 94-operation model bridge. These imports
    must first be rebuilt in one coherent provider. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SumSquaresIPRAEndpoint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 CompactSymbolicModelIff CompactBytePortsModelIff
open FreeJSumSquares SumSquaresModelIff PositiveModelIPRAAdapter
open PositiveModelIPRAStandardAdapter PositiveModelIPRAReferenceTranslated
open PRALanguage IPRAStandardTheory IPRAEqualityOnlyReference IPRAOrderErasure
open IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat

theorem positive_bridge : PositiveModelBridge (squareLiteral p) := by
  intro V _ _
  exact SumSquaresModelIff.positive_model_iff

theorem byte_positive_bridge : PositiveModelBridge (squareLiteral byteP) := by
  rw [byteP_eq]
  exact positive_bridge

theorem standard_consistency : standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (squareLiteral byteP)) 🡘
      ∼mappedNativeRefutation embedding :=
  standard_equivalence_of_positive _ byte_positive_bridge

theorem standard_translated_consistency : standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (squareLiteral byteP)) 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ :=
  standard_translated_of_positive _ byte_positive_bridge

theorem reference_consistency : referenceTheory ⊢
    erase (IPRAExpressionNative.nativeNoZero (positiveShift (squareLiteral byteP))) 🡘
      ∼erase (mappedNativeRefutation embedding) :=
  reference_equivalence_of_positive _ byte_positive_bridge

theorem reference_translated_consistency : referenceTheory ⊢
    erase (IPRAExpressionNative.nativeNoZero (positiveShift (squareLiteral byteP))) 🡘
      erase ((Semiformula.lMap embedding sourceSentence)ᴺ) :=
  reference_translated_of_positive _ byte_positive_bridge

#print axioms SumSquaresIPRAEndpoint.positive_bridge
#print axioms SumSquaresIPRAEndpoint.byte_positive_bridge
#print axioms SumSquaresIPRAEndpoint.standard_consistency
#print axioms SumSquaresIPRAEndpoint.standard_translated_consistency
#print axioms SumSquaresIPRAEndpoint.reference_consistency
#print axioms SumSquaresIPRAEndpoint.reference_translated_consistency
end SumSquaresIPRAEndpoint
