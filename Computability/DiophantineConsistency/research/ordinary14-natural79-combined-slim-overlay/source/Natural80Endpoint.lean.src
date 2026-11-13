import Natural80GammaShift
import Natural81Endpoint
import CompactPortBoundsSlim
import StrictK0Symbolic
import DiophantineConsistency.HAExpressionNoZeroEquiv
import DiophantineConsistency.IPRAExpressionNative
import DiophantineConsistency.IPRAStandardTheory
import DiophantineConsistency.IPRAReferenceInductionConversion

/-! Source-only proposed natural-80 endpoint clients. Every new graph,
model, positivity and endpoint dependency remains unelaborated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Natural80EndpointDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly HAExpressionNoZeroEquiv
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation ModelDifferenceRing
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open Natural80GammaShiftDraft StrictK0SymbolicDraft
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat lowNat highNat

def expression : Expr (Fin 14) := (P80NaturalForcedGamma.graph CompactSymbolicModelIff.p).output

/-- Symbolic low port representation; no external byte binding is asserted. -/
theorem port_two_representation {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    (CompactSymbolicModelIff.p 2 : DiffRing V)=ι (lowNat : V) := by
  change ((lowNat : ℤ) : DiffRing V)=ι (lowNat : V)
  simp only [Int.cast_natCast,map_natCast]

/-- Symbolic fourth port is beta plus the high-mask natural. -/
theorem port_three_representation {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    (CompactSymbolicModelIff.p 3 : DiffRing V)=ι ((CompactFixedBeta.betaNat+highNat : ℕ) : V) := by
  change (((CompactFixedBeta.betaNat+highNat : ℕ) : ℤ) : DiffRing V)=
    ι ((CompactFixedBeta.betaNat+highNat : ℕ) : V)
  simp only [Int.cast_natCast,map_natCast]

/-- Proposed no-zero transport through the gamma shift at the selected
symbolic ports. The witness valuations differ at coordinate 12. -/
theorem sameNoZero : SameNoZero expression Natural81EndpointDraft.expression := by
  intro V _ _
  have hbnds := CompactPortBoundsSlimDraft.port_bounds (V:=V) CompactFixedBeta.betaNat
    (paramKernel rho) lowNat highNat CompactFixedBeta.beta_identity rfl rfl
  have hb : 0<(CompactFixedBeta.betaNat : V) := by
    simpa [ports] using hbnds.1
  have hMC : (lowNat : V)<(CompactFixedBeta.betaNat : V) := by
    simpa [ports] using hbnds.2.1
  have hMF : ((CompactFixedBeta.betaNat+highNat : ℕ) : V)<2*(CompactFixedBeta.betaNat : V) := by
    simpa [ports] using hbnds.2.2.1
  have he := Natural80GammaShiftDraft.exists_zero_iff (V:=V) CompactSymbolicModelIff.p
    (CompactFixedBeta.betaNat : V) (paramKernel rho : V) (lowNat : V)
    ((CompactFixedBeta.betaNat+highNat : ℕ) : V)
    Natural82EndpointDraft.symbolic_beta_representation port_one_representation
    port_two_representation port_three_representation hb kernel_model_pos hMC hMF
  change (∃ v : Fin 14 → V, InternalZero expression v) ↔
    ∃ w : Fin 14 → V, InternalZero Natural81EndpointDraft.expression w at he
  constructor
  · intro h w hw
    obtain ⟨v,hv⟩ := he.mpr ⟨w,hw⟩
    exact h v hv
  · intro h v hv
    obtain ⟨w,hw⟩ := he.mp ⟨v,hv⟩
    exact h w hw

theorem polynomialBridge : PolynomialBridge expression :=
  HAExpressionNoZeroEquiv.bridge expression Natural81EndpointDraft.expression
    sameNoZero Natural81EndpointDraft.polynomialBridge

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

end DiophantineConsistency.Natural80EndpointDraft

#print axioms DiophantineConsistency.Natural80EndpointDraft.port_two_representation
#print axioms DiophantineConsistency.Natural80EndpointDraft.port_three_representation
#print axioms DiophantineConsistency.Natural80EndpointDraft.sameNoZero
#print axioms DiophantineConsistency.Natural80EndpointDraft.polynomialBridge
#print axioms DiophantineConsistency.Natural80EndpointDraft.native_equivalence
#print axioms DiophantineConsistency.Natural80EndpointDraft.standard_equivalence
#print axioms DiophantineConsistency.Natural80EndpointDraft.reference_equivalence
