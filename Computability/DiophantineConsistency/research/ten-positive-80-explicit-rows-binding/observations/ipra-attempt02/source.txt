import DisplayedRows
import Direct80SymbolicFixedIPRA

/-! Internal proof-existence endpoints for the explicitly listed 80 rows. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace TenPositive80DisplayedRowsIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open CompactFixedBeta CompactSymbolicPorts CompactSymbolicKernel CompactSymbolicKernelOpaque
open TenPositive80Graph TenPositive80Factors Direct80SymbolicFixedIPRA TenPositive80DisplayedRows
open PRALanguage IPRAStandardTheory IPRAEqualityOnlyReference IPRAOrderErasure
open IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat

theorem standard_consistency : standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (output_by_rows (integerPorts fixedPorts))) 🡘
      ∼mappedNativeRefutation embedding := by
  rw [output_eq]
  exact Direct80SymbolicFixedIPRA.standard_consistency

theorem standard_translated_consistency : standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (output_by_rows (integerPorts fixedPorts))) 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ := by
  rw [output_eq]
  exact Direct80SymbolicFixedIPRA.standard_translated_consistency

theorem reference_consistency : referenceTheory ⊢
    erase (IPRAExpressionNative.nativeNoZero (positiveShift (output_by_rows (integerPorts fixedPorts)))) 🡘
      ∼erase (mappedNativeRefutation embedding) := by
  rw [output_eq]
  exact Direct80SymbolicFixedIPRA.reference_consistency

theorem reference_translated_consistency : referenceTheory ⊢
    erase (IPRAExpressionNative.nativeNoZero (positiveShift (output_by_rows (integerPorts fixedPorts)))) 🡘
      erase ((Semiformula.lMap embedding sourceSentence)ᴺ) := by
  rw [output_eq]
  exact Direct80SymbolicFixedIPRA.reference_translated_consistency

#print axioms TenPositive80DisplayedRowsIPRA.standard_consistency
#print axioms TenPositive80DisplayedRowsIPRA.standard_translated_consistency
#print axioms TenPositive80DisplayedRowsIPRA.reference_consistency
#print axioms TenPositive80DisplayedRowsIPRA.reference_translated_consistency
end TenPositive80DisplayedRowsIPRA
