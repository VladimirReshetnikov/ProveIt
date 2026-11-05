import CompactFourPortByteAssembly2
import DiophantineConsistency.Compact44.IPRAPositive64

/-! P64 iPRA endpoints for four closed Lean byte recipes. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace P64ByteEndpoint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 HAExpressionAssembly
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open CompactFourPortByteAssembly2 CompactSymbolicKernel CompactSymbolicKernelOpaque

/-- Pointwise base-256 decoding of the four closed Lean byte lists. -/
def bytePortsInt : Fin 4 → ℤ := fun j => (Nat.ofDigits 256 (bytePorts j) : ℤ)

theorem bytePortsInt_eq :
    bytePortsInt = CompactSymbolicPortProjections.portsInt (paramKernel rho) := by
  funext j
  unfold bytePortsInt CompactSymbolicPortProjections.portsInt
  exact congrArg (fun n : ℕ => (n : ℤ)) (congrFun decode_ports j)

def expression : Expr (Fin 14) := (P64Graph.graph bytePortsInt).output

theorem expression_eq : expression = IPRAPositive64.expression := by
  unfold expression IPRAPositive64.expression
  rw [bytePortsInt_eq]

theorem native_equivalence : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift expression) 🡘
      ∼mappedNativeRefutation embedding := by
  rw [expression_eq]
  exact IPRAPositive64.native_equivalence

theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift expression) 🡘
      ∼mappedNativeRefutation embedding := by
  rw [expression_eq]
  exact IPRAPositive64.standard_equivalence

theorem reference_equivalence : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero (positiveShift expression)) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) := by
  rw [expression_eq]
  exact IPRAPositive64.reference_equivalence

#print axioms bytePortsInt_eq
#print axioms expression_eq
#print axioms native_equivalence
#print axioms standard_equivalence
#print axioms reference_equivalence
end P64ByteEndpoint
