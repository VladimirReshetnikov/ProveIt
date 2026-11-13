import Natural81Endpoint
import P81NaturalForcedJ
import DiophantineConsistency.AdaptiveEquationSyntax2011
import DiophantineConsistency.HAExpressionAssembly
import DiophantineConsistency.HAExpressionNoZeroEquiv
import DiophantineConsistency.PRALanguage
import DiophantineConsistency.IPRANativeTheory
import DiophantineConsistency.IPRAFoundationZFCMappedNegation
import DiophantineConsistency.IPRAExpressionNative
import DiophantineConsistency.IPRAStandardTheory
import DiophantineConsistency.IPRAOrderErasure
import DiophantineConsistency.IPRAReferenceInductionConversion
import DiophantineConsistency.Compact44.CompactBytePortsModelIff

/-! Source-only bridge to closed Lean byte recipes, not external file bytes. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Natural81RecipePortsDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly HAExpressionNoZeroEquiv
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation

def expression : Expr (Fin 14) :=
  (P81NaturalForcedJ.graph CompactBytePortsModelIff.byteP).output

/-- The input tuple is decoded from four closed Lean lists. -/
theorem expression_eq : expression = Natural81EndpointDraft.expression := by
  unfold expression Natural81EndpointDraft.expression
  rw [CompactBytePortsModelIff.byteP_eq]

theorem polynomialBridge : PolynomialBridge expression := by
  rw [expression_eq]
  exact Natural81EndpointDraft.polynomialBridge

theorem native_equivalence : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding := by
  rw [expression_eq]
  exact Natural81EndpointDraft.native_equivalence

theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding := by
  rw [expression_eq]
  exact Natural81EndpointDraft.standard_equivalence

theorem reference_equivalence : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero expression) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) := by
  rw [expression_eq]
  exact Natural81EndpointDraft.reference_equivalence

end DiophantineConsistency.Natural81RecipePortsDraft

#print axioms DiophantineConsistency.Natural81RecipePortsDraft.expression_eq
#print axioms DiophantineConsistency.Natural81RecipePortsDraft.polynomialBridge
#print axioms DiophantineConsistency.Natural81RecipePortsDraft.native_equivalence
#print axioms DiophantineConsistency.Natural81RecipePortsDraft.standard_equivalence
#print axioms DiophantineConsistency.Natural81RecipePortsDraft.reference_equivalence
