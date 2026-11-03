import Trace75BFSIPRA

/-! Unchecked draft: fixed symbolic direct-BFS ports for the trace75 client. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace75BFSFixedIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open CompactFixedBeta CompactSymbolicPorts CompactSymbolicKernel
open Trace75BFSSyntax Trace75BFSIPRA
open PRALanguage IPRANativeTheory IPRAStandardTheory IPRAEqualityOnlyReference IPRAOrderErasure
open IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat
attribute [local irreducible] rho DirectBFSSymbolicKernel.paramKernel CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat

def fixedPorts : Fin 4 → ℕ :=
  CompactSymbolicPorts.ports betaNat (DirectBFSSymbolicKernel.paramKernel rho) lowNat highNat

theorem port_zero (beta kernel lo hi : ℕ) :
    CompactSymbolicPorts.ports beta kernel lo hi 0=beta := rfl
theorem port_one (beta kernel lo hi : ℕ) :
    CompactSymbolicPorts.ports beta kernel lo hi 1=kernel := rfl
theorem port_two (beta kernel lo hi : ℕ) :
    CompactSymbolicPorts.ports beta kernel lo hi 2=lo := rfl
theorem port_three (beta kernel lo hi : ℕ) :
    CompactSymbolicPorts.ports beta kernel lo hi 3=beta+hi := rfl

theorem native_consistency : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (literal fixedPorts)) 🡘
      ∼mappedNativeRefutation embedding :=
  Trace75BFSIPRA.native_consistency fixedPorts
    (port_zero _ _ _ _) (port_one _ _ _ _) (port_two _ _ _ _) (port_three _ _ _ _)

theorem standard_consistency : standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (literal fixedPorts)) 🡘
      ∼mappedNativeRefutation embedding :=
  Trace75BFSIPRA.standard_consistency fixedPorts
    (port_zero _ _ _ _) (port_one _ _ _ _) (port_two _ _ _ _) (port_three _ _ _ _)

theorem standard_translated_consistency : standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (literal fixedPorts)) 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ :=
  Trace75BFSIPRA.standard_translated_consistency fixedPorts
    (port_zero _ _ _ _) (port_one _ _ _ _) (port_two _ _ _ _) (port_three _ _ _ _)

theorem reference_consistency : referenceTheory ⊢
    erase (IPRAExpressionNative.nativeNoZero (positiveShift (literal fixedPorts))) 🡘
      ∼erase (mappedNativeRefutation embedding) :=
  Trace75BFSIPRA.reference_consistency fixedPorts
    (port_zero _ _ _ _) (port_one _ _ _ _) (port_two _ _ _ _) (port_three _ _ _ _)

theorem reference_translated_consistency : referenceTheory ⊢
    erase (IPRAExpressionNative.nativeNoZero (positiveShift (literal fixedPorts))) 🡘
      erase ((Semiformula.lMap embedding sourceSentence)ᴺ) :=
  Trace75BFSIPRA.reference_translated_consistency fixedPorts
    (port_zero _ _ _ _) (port_one _ _ _ _) (port_two _ _ _ _) (port_three _ _ _ _)

#print axioms Trace75BFSFixedIPRA.native_consistency
#print axioms Trace75BFSFixedIPRA.standard_consistency
#print axioms Trace75BFSFixedIPRA.standard_translated_consistency
#print axioms Trace75BFSFixedIPRA.reference_consistency
#print axioms Trace75BFSFixedIPRA.reference_translated_consistency
end Trace75BFSFixedIPRA
