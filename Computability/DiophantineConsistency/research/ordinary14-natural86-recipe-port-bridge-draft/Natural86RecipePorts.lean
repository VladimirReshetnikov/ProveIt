import Natural86Endpoint
import DiophantineConsistency.Compact44.CompactBytePortsModelIff

/-! Source-only bridge to closed Lean byte recipes, not external file bytes. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Natural86RecipePortsDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionNoZeroEquiv
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation

def expression : Expr (Fin 14) :=
  (P86NaturalCancel.graph CompactBytePortsModelIff.byteP).output

/-- The input tuple is decoded from four closed Lean lists. -/
theorem expression_eq : expression = Natural86EndpointDraft.expression := by
  unfold expression Natural86EndpointDraft.expression
  rw [CompactBytePortsModelIff.byteP_eq]

theorem polynomialBridge : PolynomialBridge expression := by
  rw [expression_eq]
  exact Natural86EndpointDraft.polynomialBridge

theorem native_equivalence : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding := by
  rw [expression_eq]
  exact Natural86EndpointDraft.native_equivalence

theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding := by
  rw [expression_eq]
  exact Natural86EndpointDraft.standard_equivalence

theorem reference_equivalence : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero expression) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) := by
  rw [expression_eq]
  exact Natural86EndpointDraft.reference_equivalence

end DiophantineConsistency.Natural86RecipePortsDraft
