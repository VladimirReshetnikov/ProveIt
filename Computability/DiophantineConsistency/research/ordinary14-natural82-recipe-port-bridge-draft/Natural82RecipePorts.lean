import Natural82Endpoint
import DiophantineConsistency.Compact44.CompactBytePortsModelIff

/-! Source-only bridge to closed Lean byte recipes, not external file bytes. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Natural82RecipePortsDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly HAExpressionNoZeroEquiv
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation

def expression : Expr (Fin 14) :=
  (P82NaturalForced.graph CompactBytePortsModelIff.byteP).output

/-- The input tuple is decoded from four closed Lean lists. -/
theorem expression_eq : expression = Natural82EndpointDraft.expression := by
  unfold expression Natural82EndpointDraft.expression
  rw [CompactBytePortsModelIff.byteP_eq]

theorem polynomialBridge : PolynomialBridge expression := by
  rw [expression_eq]
  exact Natural82EndpointDraft.polynomialBridge

theorem native_equivalence : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding := by
  rw [expression_eq]
  exact Natural82EndpointDraft.native_equivalence

theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding := by
  rw [expression_eq]
  exact Natural82EndpointDraft.standard_equivalence

theorem reference_equivalence : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero expression) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) := by
  rw [expression_eq]
  exact Natural82EndpointDraft.reference_equivalence

end DiophantineConsistency.Natural82RecipePortsDraft

#print axioms DiophantineConsistency.Natural82RecipePortsDraft.expression_eq
#print axioms DiophantineConsistency.Natural82RecipePortsDraft.polynomialBridge
#print axioms DiophantineConsistency.Natural82RecipePortsDraft.native_equivalence
#print axioms DiophantineConsistency.Natural82RecipePortsDraft.standard_equivalence
#print axioms DiophantineConsistency.Natural82RecipePortsDraft.reference_equivalence
