import Direct80SymbolicIPRA

/-! Specialize the parameterized result via generic finite-port projections. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Direct80SymbolicFixedIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open CompactFixedBeta CompactSymbolicPorts CompactSymbolicKernel CompactSymbolicKernelOpaque
open TenPositive80Graph TenPositive80Factors Direct80SymbolicIPRA
open PRALanguage IPRAStandardTheory IPRAEqualityOnlyReference IPRAOrderErasure
open IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat

theorem port_zero (beta kernel lo hi : ℕ) : ports beta kernel lo hi 0=beta := rfl
theorem port_one (beta kernel lo hi : ℕ) : ports beta kernel lo hi 1=kernel := rfl
theorem port_two (beta kernel lo hi : ℕ) : ports beta kernel lo hi 2=lo := rfl
theorem port_three (beta kernel lo hi : ℕ) : ports beta kernel lo hi 3=beta+hi := rfl

def fixedPorts : Fin 4 → ℕ := ports betaNat (paramKernel rho) lowNat highNat

theorem standard_consistency : standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (graph (integerPorts fixedPorts)).output) 🡘
      ∼mappedNativeRefutation embedding :=
  Direct80SymbolicIPRA.standard_consistency fixedPorts
    (port_zero _ _ _ _) (port_one _ _ _ _) (port_two _ _ _ _) (port_three _ _ _ _)

theorem standard_translated_consistency : standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (graph (integerPorts fixedPorts)).output) 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ :=
  Direct80SymbolicIPRA.standard_translated_consistency fixedPorts
    (port_zero _ _ _ _) (port_one _ _ _ _) (port_two _ _ _ _) (port_three _ _ _ _)

theorem reference_consistency : referenceTheory ⊢
    erase (IPRAExpressionNative.nativeNoZero (positiveShift (graph (integerPorts fixedPorts)).output)) 🡘
      ∼erase (mappedNativeRefutation embedding) :=
  Direct80SymbolicIPRA.reference_consistency fixedPorts
    (port_zero _ _ _ _) (port_one _ _ _ _) (port_two _ _ _ _) (port_three _ _ _ _)

theorem reference_translated_consistency : referenceTheory ⊢
    erase (IPRAExpressionNative.nativeNoZero (positiveShift (graph (integerPorts fixedPorts)).output)) 🡘
      erase ((Semiformula.lMap embedding sourceSentence)ᴺ) :=
  Direct80SymbolicIPRA.reference_translated_consistency fixedPorts
    (port_zero _ _ _ _) (port_one _ _ _ _) (port_two _ _ _ _) (port_three _ _ _ _)

#print axioms Direct80SymbolicFixedIPRA.standard_consistency
#print axioms Direct80SymbolicFixedIPRA.standard_translated_consistency
#print axioms Direct80SymbolicFixedIPRA.reference_consistency
#print axioms Direct80SymbolicFixedIPRA.reference_translated_consistency
end Direct80SymbolicFixedIPRA
