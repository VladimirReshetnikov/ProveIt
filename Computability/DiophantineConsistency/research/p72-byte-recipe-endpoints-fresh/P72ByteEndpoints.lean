import P72Translated
import DiophantineConsistency.Compact44.CompactBytePortsModelIff

/-! Fresh P13/P14 endpoint statements at the four closed Lean byte recipes. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.P72ByteEndpoints
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage FoundationZFCConsistencyNat AdaptiveEquationSyntax2011
open CompactSymbolicKernel CompactSymbolicKernelOpaque
attribute [local irreducible] Nat.ofDigits CompactFourPortByteAssembly2.bytePorts
  CompactFixedBeta.betaNat paramKernel rho CompactSymbolicPorts.lowNat CompactSymbolicPorts.highNat

/-- The decoded byte-recipe tuple is exactly the P72 symbolic tuple. -/
theorem byteP_eq_ports : CompactBytePortsModelIff.byteP =
    CompactSymbolicPortProjections.portsInt (paramKernel rho) := by
  exact CompactBytePortsModelIff.byteP_eq

def expression13 : Expr (Fin 13) := (P72Graph.graph CompactBytePortsModelIff.byteP).output
def expression14 : Expr (Fin 14) := (P72P14.graph CompactBytePortsModelIff.byteP).output

theorem translated_p13 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift expression13) 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ := by
  unfold expression13
  rw [byteP_eq_ports]
  exact P72Translated.standard_translated_p13

theorem translated_p14 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift expression14) 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ := by
  unfold expression14
  rw [byteP_eq_ports]
  exact P72Translated.standard_translated_p14

#print axioms byteP_eq_ports
#print axioms translated_p13
#print axioms translated_p14
end DiophantineConsistency.P72ByteEndpoints
