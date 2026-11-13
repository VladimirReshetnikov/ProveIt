import DirectBFS80IPRA

/-! Specialize the parameterized result via generic finite-port projections. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFS80FixedIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open CompactFixedBeta CompactSymbolicPorts CompactSymbolicKernel
open TenPositive80Graph TenPositive80Factors DirectBFS80IPRA
open PRALanguage IPRAStandardTheory IPRAEqualityOnlyReference IPRAOrderErasure
open IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat
attribute [local irreducible] rho DirectBFSSymbolicKernel.paramKernel CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat

theorem port_zero (beta kernel lo hi : ℕ) : ports beta kernel lo hi 0=beta := rfl
theorem port_one (beta kernel lo hi : ℕ) : ports beta kernel lo hi 1=kernel := rfl
theorem port_two (beta kernel lo hi : ℕ) : ports beta kernel lo hi 2=lo := rfl
theorem port_three (beta kernel lo hi : ℕ) : ports beta kernel lo hi 3=beta+hi := rfl

def fixedPorts : Fin 4 → ℕ := ports betaNat (DirectBFSSymbolicKernel.paramKernel rho) lowNat highNat

theorem standard_consistency : standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (graph (integerPorts fixedPorts)).output) 🡘
      ∼mappedNativeRefutation embedding :=
  DirectBFS80IPRA.standard_consistency fixedPorts
    (port_zero _ _ _ _) (port_one _ _ _ _) (port_two _ _ _ _) (port_three _ _ _ _)

theorem standard_translated_consistency : standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (graph (integerPorts fixedPorts)).output) 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ :=
  DirectBFS80IPRA.standard_translated_consistency fixedPorts
    (port_zero _ _ _ _) (port_one _ _ _ _) (port_two _ _ _ _) (port_three _ _ _ _)

theorem reference_consistency : referenceTheory ⊢
    erase (IPRAExpressionNative.nativeNoZero (positiveShift (graph (integerPorts fixedPorts)).output)) 🡘
      ∼erase (mappedNativeRefutation embedding) :=
  DirectBFS80IPRA.reference_consistency fixedPorts
    (port_zero _ _ _ _) (port_one _ _ _ _) (port_two _ _ _ _) (port_three _ _ _ _)

theorem reference_translated_consistency : referenceTheory ⊢
    erase (IPRAExpressionNative.nativeNoZero (positiveShift (graph (integerPorts fixedPorts)).output)) 🡘
      erase ((Semiformula.lMap embedding sourceSentence)ᴺ) :=
  DirectBFS80IPRA.reference_translated_consistency fixedPorts
    (port_zero _ _ _ _) (port_one _ _ _ _) (port_two _ _ _ _) (port_three _ _ _ _)

#print axioms DirectBFS80FixedIPRA.standard_consistency
#print axioms DirectBFS80FixedIPRA.standard_translated_consistency
#print axioms DirectBFS80FixedIPRA.reference_consistency
#print axioms DirectBFS80FixedIPRA.reference_translated_consistency
end DirectBFS80FixedIPRA
