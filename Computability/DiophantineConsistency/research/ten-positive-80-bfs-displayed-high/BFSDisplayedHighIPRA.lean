import BFSDisplayedBetaIPRAV2
import BFSHighSymbolic

/-! iPRA client using the displayed decimal-list kernel recipe. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace BFSDisplayedHighIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open CompactFixedBeta CompactSymbolicPorts CompactSymbolicKernel
open TenPositive80Graph TenPositive80Factors
open PRALanguage IPRAStandardTheory IPRAEqualityOnlyReference IPRAOrderErasure
open IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat
attribute [local irreducible] rho DirectBFSSymbolicKernel.paramKernel BFSDisplayedSlots.displayedKernel CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat

theorem high_eq : BFSHighSymbolic.displayedHigh rho = highNat := by
  have hh : Nat.ofDigits rho CompactHighPopulation.highDigits = highNat := by
    unfold rho CompactSymbolicPorts.highNat
    rfl
  exact (BFSHighSymbolic.high_recipe rho).symm.trans hh

def displayedPorts : Fin 4 → ℕ :=
  ports BFSDisplayedBetaIPRA.displayedBeta (BFSDisplayedSlots.displayedKernel rho) lowNat (BFSHighSymbolic.displayedHigh rho)

theorem ports_eq : displayedPorts = BFSDisplayedBetaIPRA.displayedPorts :=
  congrArg (fun hi => ports BFSDisplayedBetaIPRA.displayedBeta (BFSDisplayedSlots.displayedKernel rho) lowNat hi) high_eq

theorem standard_consistency : standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (graph (integerPorts displayedPorts)).output) 🡘
      ∼mappedNativeRefutation embedding := by
  rw [ports_eq]
  exact BFSDisplayedBetaIPRA.standard_consistency

theorem standard_translated_consistency : standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (graph (integerPorts displayedPorts)).output) 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ := by
  rw [ports_eq]
  exact BFSDisplayedBetaIPRA.standard_translated_consistency

theorem reference_consistency : referenceTheory ⊢
    erase (IPRAExpressionNative.nativeNoZero (positiveShift (graph (integerPorts displayedPorts)).output)) 🡘
      ∼erase (mappedNativeRefutation embedding) := by
  rw [ports_eq]
  exact BFSDisplayedBetaIPRA.reference_consistency

theorem reference_translated_consistency : referenceTheory ⊢
    erase (IPRAExpressionNative.nativeNoZero (positiveShift (graph (integerPorts displayedPorts)).output)) 🡘
      erase ((Semiformula.lMap embedding sourceSentence)ᴺ) := by
  rw [ports_eq]
  exact BFSDisplayedBetaIPRA.reference_translated_consistency

#print axioms BFSDisplayedHighIPRA.standard_consistency
#print axioms BFSDisplayedHighIPRA.standard_translated_consistency
#print axioms BFSDisplayedHighIPRA.reference_consistency
#print axioms BFSDisplayedHighIPRA.reference_translated_consistency
end BFSDisplayedHighIPRA
