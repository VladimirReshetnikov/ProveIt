import BFSDisplayedBetaIPRAV2
import BFSDisplayedLowGeneric

/-! iPRA client using the displayed decimal-list kernel recipe. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace BFSDisplayedLowIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open CompactFixedBeta CompactSymbolicPorts CompactSymbolicKernel
open TenPositive80Graph TenPositive80Factors
open PRALanguage IPRAStandardTheory IPRAEqualityOnlyReference IPRAOrderErasure
open IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat
attribute [local irreducible] rho DirectBFSSymbolicKernel.paramKernel BFSDisplayedSlots.displayedKernel CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat

open Finset
open scoped BigOperators

def displayedSupport : Finset ℕ :=
  ((range 943 ∪ Ico 983 993 ∪ Ico 1003 1012 ∪ Ico 1013 1032 ∪
    {1063,1064,1095,2195,3296}) \ {1})

theorem support_eq : displayedSupport = CompactConcreteMask.support := rfl

theorem beta_radix : rho^8807 - 1 = BFSDisplayedBetaIPRA.displayedBeta := by
  unfold rho BFSDisplayedBetaIPRA.displayedBeta
  rfl

def displayedLow : ℕ :=
  rho^8807 - 1 - (∑ j ∈ displayedSupport, rho^j) - 2*rho^1063

theorem low_eq : displayedLow = CompactSymbolicPorts.lowNat := by
  have hB : 4 ≤ rho := by unfold rho; norm_num
  have hg : displayedLow = Nat.ofDigits rho (CompactListMask.digits rho 8807 1063 CompactConcreteMask.support) := by
    unfold displayedLow
    rw [support_eq]
    exact (BFSDisplayedLowGeneric.low_recipe rho 8807 1063
      CompactConcreteMask.support hB CompactConcreteMask.support_bounded
      CompactConcreteMask.special_mem).symm
  have hh : Nat.ofDigits rho (CompactListMask.digits rho 8807 1063 CompactConcreteMask.support) = CompactSymbolicPorts.lowNat := by
    unfold rho CompactSymbolicPorts.lowNat
    rfl
  exact hg.trans hh

def displayedPorts : Fin 4 → ℕ :=
  ports BFSDisplayedBetaIPRA.displayedBeta (BFSDisplayedSlots.displayedKernel rho) displayedLow highNat

theorem ports_eq : displayedPorts = BFSDisplayedBetaIPRA.displayedPorts :=
  congrArg (fun lo => ports BFSDisplayedBetaIPRA.displayedBeta (BFSDisplayedSlots.displayedKernel rho) lo highNat) low_eq

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

#print axioms BFSDisplayedLowIPRA.standard_consistency
#print axioms BFSDisplayedLowIPRA.standard_translated_consistency
#print axioms BFSDisplayedLowIPRA.reference_consistency
#print axioms BFSDisplayedLowIPRA.reference_translated_consistency
end BFSDisplayedLowIPRA
