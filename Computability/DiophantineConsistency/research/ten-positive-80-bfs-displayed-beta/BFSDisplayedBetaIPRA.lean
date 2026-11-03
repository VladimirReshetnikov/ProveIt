import BFSDisplayed80IPRA

/-! iPRA client using the displayed decimal-list kernel recipe. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace BFSDisplayedBetaIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open CompactFixedBeta CompactSymbolicPorts CompactSymbolicKernel
open TenPositive80Graph TenPositive80Factors
open PRALanguage IPRAStandardTheory IPRAEqualityOnlyReference IPRAOrderErasure
open IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat
attribute [local irreducible] rho DirectBFSSymbolicKernel.paramKernel BFSDisplayedSlots.displayedKernel CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat

def displayedBeta : ℕ := ((2:ℕ)^67)^8807 - 1

theorem beta_generic (a m n : ℕ) : (a^m)^n - 1 = a^(m*n) - 1 := by
  rw [← pow_mul]

theorem beta_eq : displayedBeta = CompactFixedBeta.betaNat :=
  beta_generic 2 67 8807

def displayedPorts : Fin 4 → ℕ :=
  ports displayedBeta (BFSDisplayedSlots.displayedKernel rho) lowNat highNat

theorem ports_eq : displayedPorts = BFSDisplayed80IPRA.displayedPorts :=
  congrArg (fun beta => ports beta (BFSDisplayedSlots.displayedKernel rho) lowNat highNat) beta_eq

theorem standard_consistency : standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (graph (integerPorts displayedPorts)).output) 🡘
      ∼mappedNativeRefutation embedding := by
  rw [ports_eq]
  exact BFSDisplayed80IPRA.standard_consistency

theorem standard_translated_consistency : standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (graph (integerPorts displayedPorts)).output) 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ := by
  rw [ports_eq]
  exact BFSDisplayed80IPRA.standard_translated_consistency

theorem reference_consistency : referenceTheory ⊢
    erase (IPRAExpressionNative.nativeNoZero (positiveShift (graph (integerPorts displayedPorts)).output)) 🡘
      ∼erase (mappedNativeRefutation embedding) := by
  rw [ports_eq]
  exact BFSDisplayed80IPRA.reference_consistency

theorem reference_translated_consistency : referenceTheory ⊢
    erase (IPRAExpressionNative.nativeNoZero (positiveShift (graph (integerPorts displayedPorts)).output)) 🡘
      erase ((Semiformula.lMap embedding sourceSentence)ᴺ) := by
  rw [ports_eq]
  exact BFSDisplayed80IPRA.reference_translated_consistency

#print axioms BFSDisplayedBetaIPRA.standard_consistency
#print axioms BFSDisplayedBetaIPRA.standard_translated_consistency
#print axioms BFSDisplayedBetaIPRA.reference_consistency
#print axioms BFSDisplayedBetaIPRA.reference_translated_consistency
end BFSDisplayedBetaIPRA
