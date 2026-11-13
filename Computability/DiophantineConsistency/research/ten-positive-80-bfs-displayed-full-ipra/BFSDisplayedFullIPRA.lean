import BFSDisplayedLowInferredV4
import BFSDisplayedHighIPRA

/-! Transport the checked high client across the inferred low-mask equality. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace BFSDisplayedFullIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open CompactFixedBeta CompactSymbolicPorts CompactSymbolicKernel
open TenPositive80Graph TenPositive80Factors
open PRALanguage IPRAStandardTheory IPRAEqualityOnlyReference IPRAOrderErasure
open IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat
attribute [local irreducible] rho DirectBFSSymbolicKernel.paramKernel BFSDisplayedSlots.displayedKernel CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat

set_option linter.defProp false in
def ports_eq := congrArg
  (fun lo => ports BFSDisplayedBetaIPRA.displayedBeta (BFSDisplayedSlots.displayedKernel rho) lo (BFSHighSymbolic.displayedHigh rho))
  BFSDisplayedLowInferred.low_formula

set_option linter.defProp false in
def standard_consistency := Eq.mp (congrArg (fun p => standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (graph (integerPorts p)).output) 🡘
      ∼mappedNativeRefutation embedding) ports_eq) BFSDisplayedHighIPRA.standard_consistency

set_option linter.defProp false in
def standard_translated_consistency := Eq.mp (congrArg (fun p => standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (graph (integerPorts p)).output) 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ) ports_eq) BFSDisplayedHighIPRA.standard_translated_consistency

set_option linter.defProp false in
def reference_consistency := Eq.mp (congrArg (fun p => referenceTheory ⊢
    erase (IPRAExpressionNative.nativeNoZero (positiveShift (graph (integerPorts p)).output)) 🡘
      ∼erase (mappedNativeRefutation embedding)) ports_eq) BFSDisplayedHighIPRA.reference_consistency

set_option linter.defProp false in
def reference_translated_consistency := Eq.mp (congrArg (fun p => referenceTheory ⊢
    erase (IPRAExpressionNative.nativeNoZero (positiveShift (graph (integerPorts p)).output)) 🡘
      erase ((Semiformula.lMap embedding sourceSentence)ᴺ)) ports_eq) BFSDisplayedHighIPRA.reference_translated_consistency

#check BFSDisplayedFullIPRA.standard_consistency
#check BFSDisplayedFullIPRA.standard_translated_consistency
#check BFSDisplayedFullIPRA.reference_consistency
#check BFSDisplayedFullIPRA.reference_translated_consistency
#print axioms BFSDisplayedFullIPRA.standard_consistency
#print axioms BFSDisplayedFullIPRA.standard_translated_consistency
#print axioms BFSDisplayedFullIPRA.reference_consistency
#print axioms BFSDisplayedFullIPRA.reference_translated_consistency
end BFSDisplayedFullIPRA
