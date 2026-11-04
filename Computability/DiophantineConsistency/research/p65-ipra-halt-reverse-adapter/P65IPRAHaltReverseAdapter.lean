import P65CanonicalHaltConverse
import DiophantineConsistency.IPRAExpressionNative
import DiophantineConsistency.IPRAStandardTheory
import DiophantineConsistency.IPRAReferenceInductionConversion
import DiophantineConsistency.HAExpressionAssembly

/-! Conditional iPRA endpoint for package 65, pending the zero-to-halt side. -/
set_option autoImplicit false
noncomputable section
namespace P65IPRAHaltReverseAdapter
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 HAExpressionAssembly
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
attribute [local irreducible] paramKernel rho CompactFixedBeta.betaNat lowNat highNat

def expression : Expr (Fin 14) :=
  (P65Graph.graph (CompactSymbolicPortProjections.portsInt (paramKernel rho))).output

/-- Remaining zero-to-halt direction for this fixed expression, in every
IΣ₁ model. The converse is already supplied by the canonical construction. -/
def ReverseDirection : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    (∃ v : Fin 14 → V, (∀ j, 0 < v j) ∧ InternalZero expression v) →
      ∃ time : V, first (ArithmeticMachineRun215.run time) = 0

theorem polynomialBridge (h : ReverseDirection) : PolynomialBridge (positiveShift expression) := by
  intro V _ _
  rw [classicalNoZero_iff]
  constructor
  · intro hn hh
    obtain ⟨T, hT⟩ := hh
    obtain ⟨v, hv, hz⟩ := P65CanonicalHaltConverse.halt_positive_zero T hT
    let x : Fin 14 → V := fun j => v j - 1
    have hx : (fun j => x j + 1) = v := by
      funext j
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (hv j))
    have hz' : InternalZero (positiveShift expression) x := by
      rw [internalZero_positiveShift, hx]
      exact hz
    exact hn x hz'
  · intro hn v hz
    apply hn
    apply h V
    refine ⟨fun j => v j + 1, ?_, ?_⟩
    · intro j
      simp
    · exact (internalZero_positiveShift expression v).mp hz

theorem native_equivalence (h : ReverseDirection) : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift expression) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ (polynomialBridge h)

theorem standard_equivalence (h : ReverseDirection) : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift expression) 🡘
      ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 (native_equivalence h)

theorem reference_equivalence (h : ReverseDirection) : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero (positiveShift expression)) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  IPRAReferenceInductionConversion.nativeToReference (native_equivalence h)

#print axioms polynomialBridge
#print axioms native_equivalence
#print axioms standard_equivalence
#print axioms reference_equivalence
end P65IPRAHaltReverseAdapter
