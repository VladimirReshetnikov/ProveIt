import BFSDisplayedSlots
import DirectBFS80FixedIPRA

/-! iPRA client using the displayed decimal-list kernel recipe. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace BFSDisplayed80IPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open CompactFixedBeta CompactSymbolicPorts CompactSymbolicKernel
open TenPositive80Graph TenPositive80Factors
open PRALanguage IPRAStandardTheory IPRAEqualityOnlyReference IPRAOrderErasure
open IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat
attribute [local irreducible] rho DirectBFSSymbolicKernel.paramKernel BFSDisplayedSlots.displayedKernel CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat

theorem ports_eq_generic (beta lo hi r : ℕ) :
    ports beta (BFSDisplayedSlots.displayedKernel r) lo hi =
      ports beta (DirectBFSSymbolicKernel.paramKernel r) lo hi :=
  congrArg (fun k => ports beta k lo hi) (BFSDisplayedSlots.kernel_eq_displayed r).symm

def displayedPorts : Fin 4 → ℕ := ports betaNat (BFSDisplayedSlots.displayedKernel rho) lowNat highNat

theorem ports_eq : displayedPorts = DirectBFS80FixedIPRA.fixedPorts :=
  ports_eq_generic betaNat lowNat highNat rho

theorem standard_consistency : standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (graph (integerPorts displayedPorts)).output) 🡘
      ∼mappedNativeRefutation embedding := by
  rw [ports_eq]
  exact DirectBFS80FixedIPRA.standard_consistency

theorem standard_translated_consistency : standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (graph (integerPorts displayedPorts)).output) 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ := by
  rw [ports_eq]
  exact DirectBFS80FixedIPRA.standard_translated_consistency

theorem reference_consistency : referenceTheory ⊢
    erase (IPRAExpressionNative.nativeNoZero (positiveShift (graph (integerPorts displayedPorts)).output)) 🡘
      ∼erase (mappedNativeRefutation embedding) := by
  rw [ports_eq]
  exact DirectBFS80FixedIPRA.reference_consistency

theorem reference_translated_consistency : referenceTheory ⊢
    erase (IPRAExpressionNative.nativeNoZero (positiveShift (graph (integerPorts displayedPorts)).output)) 🡘
      erase ((Semiformula.lMap embedding sourceSentence)ᴺ) := by
  rw [ports_eq]
  exact DirectBFS80FixedIPRA.reference_translated_consistency

#print axioms BFSDisplayed80IPRA.standard_consistency
#print axioms BFSDisplayed80IPRA.standard_translated_consistency
#print axioms BFSDisplayed80IPRA.reference_consistency
#print axioms BFSDisplayed80IPRA.reference_translated_consistency
end BFSDisplayed80IPRA
