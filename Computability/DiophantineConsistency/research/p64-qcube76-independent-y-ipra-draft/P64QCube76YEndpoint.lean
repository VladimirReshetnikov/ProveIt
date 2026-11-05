import IndependentYFullJoinDraft
import P64QCube77Endpoint

/-! Draft: compose the 76Y/77 zero equivalence with the 77 iPRA endpoint. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace P64QCube76YEndpoint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 HAExpressionAssembly
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open IPRAOrdinary12 (PositiveModelBridge)
open IPRAOrdinary12Chain (native_of_positive standard_of_positive reference_of_positive)
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
attribute [local irreducible] paramKernel rho CompactFixedBeta.betaNat lowNat highNat

def expression : Expr (Fin 14) :=
  (P64QCube76Y.graph (CompactSymbolicPortProjections.portsInt (paramKernel rho))).output

theorem positiveBridge : PositiveModelBridge expression := by
  intro V _ _
  exact (IndependentYFullJoinDraft.positive_zero_iff
    (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat)).trans
      (P64QCube77Endpoint.positiveBridge V)

theorem native_equivalence : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift expression) 🡘
      ∼mappedNativeRefutation embedding :=
  native_of_positive _ positiveBridge

theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift expression) 🡘
      ∼mappedNativeRefutation embedding :=
  standard_of_positive _ positiveBridge

theorem reference_equivalence : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero (positiveShift expression)) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  reference_of_positive _ positiveBridge

#print axioms positiveBridge
#print axioms native_equivalence
#print axioms standard_equivalence
#print axioms reference_equivalence
end P64QCube76YEndpoint
