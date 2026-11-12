import GraphPredecessors82
import Natural86Endpoint
import DiophantineConsistency.HAExpressionNoZeroEquiv
import DiophantineConsistency.IPRAExpressionNative
import DiophantineConsistency.IPRAStandardTheory
import DiophantineConsistency.IPRAReferenceInductionConversion

/-! Source-only proposed no-zero and endpoint clients. None of these proofs,
their imported draft dependencies, or the predecessor bridge is elaborated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Natural82EndpointDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly HAExpressionNoZeroEquiv
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open ModelDifferenceRing Natural82ModelDraft GraphPredecessors82Draft
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat lowNat highNat

def expression : Expr (Fin 14) := (P82NaturalForced.graph CompactSymbolicModelIff.p).output

/-- The selected symbolic port zero is the image of the natural beta cast.
No expansion or physical coefficient-byte binding is asserted here. -/
theorem symbolic_beta_representation {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    (CompactSymbolicModelIff.p 0 : DiffRing V) = ι (CompactFixedBeta.betaNat : V) := by
  change ((CompactFixedBeta.betaNat : ℤ) : DiffRing V) = ι (CompactFixedBeta.betaNat : V)
  simp only [Int.cast_natCast, map_natCast]

/-- Symbolic beta is positive in every model used by `SameNoZero`. -/
theorem symbolic_beta_positive {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : 0 < (CompactFixedBeta.betaNat : V) := by
  exact (CompactFixedBeta.bounds (V:=V) 1 (by simp)).1

/-- Transfer no-zero via related valuations, using the proposed predecessor
proof in one direction and explicit coordinate increments in the other. -/
theorem sameNoZero : SameNoZero expression Natural86EndpointDraft.expression := by
  intro V _ _
  have he := exists_zero_iff_of_predecessors (V:=V) CompactSymbolicModelIff.p
    (fun v hv => predecessors_of_zero CompactSymbolicModelIff.p
      (CompactFixedBeta.betaNat : V) v symbolic_beta_representation symbolic_beta_positive hv)
  change (∃ v : Fin 14 → V, InternalZero expression v) ↔
    ∃ w : Fin 14 → V, InternalZero Natural86EndpointDraft.expression w at he
  constructor
  · intro h w hw
    obtain ⟨v, hv⟩ := he.mpr ⟨w, hw⟩
    exact h v hv
  · intro h v hv
    obtain ⟨w, hw⟩ := he.mp ⟨v, hv⟩
    exact h w hw

/-- Proposed transport across the existing natural86 polynomial bridge. -/
theorem polynomialBridge : PolynomialBridge expression :=
  HAExpressionNoZeroEquiv.bridge expression Natural86EndpointDraft.expression
    sameNoZero Natural86EndpointDraft.polynomialBridge

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

end DiophantineConsistency.Natural82EndpointDraft

#print axioms DiophantineConsistency.Natural82EndpointDraft.sameNoZero
#print axioms DiophantineConsistency.Natural82EndpointDraft.polynomialBridge
#print axioms DiophantineConsistency.Natural82EndpointDraft.native_equivalence
#print axioms DiophantineConsistency.Natural82EndpointDraft.standard_equivalence
#print axioms DiophantineConsistency.Natural82EndpointDraft.reference_equivalence
