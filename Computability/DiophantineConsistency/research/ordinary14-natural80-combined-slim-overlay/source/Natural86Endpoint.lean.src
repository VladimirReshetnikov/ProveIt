import Natural86Model
import Root74PositiveBridge
import DiophantineConsistency.HAExpressionNoZeroEquiv
import DiophantineConsistency.IPRAExpressionNative
import DiophantineConsistency.IPRAStandardTheory
import DiophantineConsistency.IPRAReferenceInductionConversion
import DiophantineConsistency.Compact44.IPRAOrdinary12

/-! Source-only proposed direct natural86 bridge and iPRA adapters. No Lean
elaboration, provider, physical coefficient or endpoint claim is made. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Natural86EndpointDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly HAExpressionNoZeroEquiv
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation

def expression : Expr (Fin 14) := (P86NaturalCancel.graph CompactSymbolicModelIff.p).output

/-- Every model sees the same no-zero condition as the positive-shifted 74
expression, using the same natural valuation and symbolic integer ports. -/
theorem sameNoZero : SameNoZero expression (positiveShift Root74PositiveBridgeDraft.expression) := by
  intro V _ _
  constructor
  · intro h v hz
    apply h v
    have he := Natural86ModelDraft.internalZero_iff (V:=V) CompactSymbolicModelIff.p v
    exact he.mpr hz
  · intro h v hz
    apply h v
    have he := Natural86ModelDraft.internalZero_iff (V:=V) CompactSymbolicModelIff.p v
    exact he.mp hz

/-- Proposed all-model no-zero/machine bridge; no second shift is applied. -/
theorem polynomialBridge : PolynomialBridge expression :=
  HAExpressionNoZeroEquiv.bridge expression (positiveShift Root74PositiveBridgeDraft.expression)
    sameNoZero (IPRAOrdinary12.bridge_of_positive _ Root74PositiveBridgeDraft.positiveBridge)

theorem native_equivalence : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge expression polynomialBridge

theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalence

theorem reference_equivalence : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero expression) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  IPRAReferenceInductionConversion.nativeToReference native_equivalence

end DiophantineConsistency.Natural86EndpointDraft

#print axioms DiophantineConsistency.Natural86EndpointDraft.sameNoZero
#print axioms DiophantineConsistency.Natural86EndpointDraft.polynomialBridge
#print axioms DiophantineConsistency.Natural86EndpointDraft.native_equivalence
#print axioms DiophantineConsistency.Natural86EndpointDraft.standard_equivalence
#print axioms DiophantineConsistency.Natural86EndpointDraft.reference_equivalence
