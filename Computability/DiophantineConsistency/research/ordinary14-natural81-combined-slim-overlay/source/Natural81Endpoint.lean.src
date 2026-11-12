import Natural81JShift
import StrictK0Symbolic
import Natural82Endpoint
import DiophantineConsistency.HAExpressionNoZeroEquiv
import DiophantineConsistency.IPRAExpressionNative
import DiophantineConsistency.IPRAStandardTheory
import DiophantineConsistency.IPRAReferenceInductionConversion

/-! Source-only proposed natural-81 endpoint clients; all imported drafts and
the proof scripts below remain unelaborated. No byte or PDF binding. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Natural81EndpointDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly HAExpressionNoZeroEquiv
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open CompactSymbolicKernel CompactSymbolicKernelOpaque
open Natural81JShiftDraft StrictK0SymbolicDraft
attribute [local irreducible] rho paramKernel

def expression : Expr (Fin 14) := (P81NaturalForcedJ.graph CompactSymbolicModelIff.p).output

/-- Proposed no-zero comparison uses a related J valuation and the
represented positive symbolic K0, not an identity at the same valuation. -/
theorem sameNoZero : SameNoZero expression Natural82EndpointDraft.expression := by
  intro V _ _
  have he := Natural81JShiftDraft.exists_zero_iff (V:=V) CompactSymbolicModelIff.p
    (paramKernel rho : V) port_one_representation kernel_model_pos
  change (∃ v : Fin 14 → V, InternalZero expression v) ↔
    ∃ w : Fin 14 → V, InternalZero Natural82EndpointDraft.expression w at he
  constructor
  · intro h w hw
    obtain ⟨v, hv⟩ := he.mpr ⟨w, hw⟩
    exact h v hv
  · intro h v hv
    obtain ⟨w, hw⟩ := he.mp ⟨v, hv⟩
    exact h w hw

theorem polynomialBridge : PolynomialBridge expression :=
  HAExpressionNoZeroEquiv.bridge expression Natural82EndpointDraft.expression
    sameNoZero Natural82EndpointDraft.polynomialBridge

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

end DiophantineConsistency.Natural81EndpointDraft

#print axioms DiophantineConsistency.Natural81EndpointDraft.sameNoZero
#print axioms DiophantineConsistency.Natural81EndpointDraft.polynomialBridge
#print axioms DiophantineConsistency.Natural81EndpointDraft.native_equivalence
#print axioms DiophantineConsistency.Natural81EndpointDraft.standard_equivalence
#print axioms DiophantineConsistency.Natural81EndpointDraft.reference_equivalence
