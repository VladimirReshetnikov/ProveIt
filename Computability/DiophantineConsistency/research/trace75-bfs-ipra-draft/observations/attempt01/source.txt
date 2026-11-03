import Trace75BFSModelIff
import Trace75BFSSyntax
import PositiveModelIPRAReferenceTranslated

/-! Draft only: literal-expression bridge and iPRA client for trace75.

This file depends on the separately proposed trace75 model iff.  It has not
been Lean checked and does not authenticate any external equation file. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace Trace75BFSIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open CompactFixedBeta CompactSymbolicPorts CompactSymbolicKernel
open TenPositiveTrace75 Trace75BFSModelIff Trace75BFSSyntax
open PositiveModelIPRAAdapter PositiveModelIPRAStandardAdapter PositiveModelIPRAReferenceTranslated
open PRALanguage IPRANativeTheory IPRAStandardTheory IPRAEqualityOnlyReference IPRAOrderErasure
open IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] rho DirectBFSSymbolicKernel.paramKernel CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat

theorem positive_bridge (p : Fin 4 → ℕ)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho)
    (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat) :
    PositiveModelBridge (literal p) := by
  intro V _ _
  constructor
  · rintro ⟨v,hv,hz⟩
    exact (Trace75BFSModelIff.positive_model_iff p hp0 hp1 hp2 hp3).mp
      ⟨v,hv,(literal_zero_iff p v).mp hz⟩
  · intro h
    obtain ⟨v,hv,hz⟩ := (Trace75BFSModelIff.positive_model_iff p hp0 hp1 hp2 hp3).mpr h
    exact ⟨v,hv,(literal_zero_iff p v).mpr hz⟩

theorem native_consistency (p : Fin 4 → ℕ)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho)
    (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat) : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (literal p)) 🡘
      ∼mappedNativeRefutation embedding :=
  native_equivalence_of_positive _ (positive_bridge p hp0 hp1 hp2 hp3)

theorem standard_consistency (p : Fin 4 → ℕ)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho)
    (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat) : standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (literal p)) 🡘
      ∼mappedNativeRefutation embedding :=
  standard_equivalence_of_positive _ (positive_bridge p hp0 hp1 hp2 hp3)

theorem standard_translated_consistency (p : Fin 4 → ℕ)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho)
    (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat) : standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (literal p)) 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ :=
  standard_translated_of_positive _ (positive_bridge p hp0 hp1 hp2 hp3)

theorem reference_consistency (p : Fin 4 → ℕ)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho)
    (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat) : referenceTheory ⊢
    erase (IPRAExpressionNative.nativeNoZero (positiveShift (literal p))) 🡘
      ∼erase (mappedNativeRefutation embedding) :=
  reference_equivalence_of_positive _ (positive_bridge p hp0 hp1 hp2 hp3)

theorem reference_translated_consistency (p : Fin 4 → ℕ)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho)
    (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat) : referenceTheory ⊢
    erase (IPRAExpressionNative.nativeNoZero (positiveShift (literal p))) 🡘
      erase ((Semiformula.lMap embedding sourceSentence)ᴺ) :=
  reference_translated_of_positive _ (positive_bridge p hp0 hp1 hp2 hp3)

#print axioms Trace75BFSIPRA.positive_bridge
#print axioms Trace75BFSIPRA.native_consistency
#print axioms Trace75BFSIPRA.standard_consistency
#print axioms Trace75BFSIPRA.standard_translated_consistency
#print axioms Trace75BFSIPRA.reference_consistency
#print axioms Trace75BFSIPRA.reference_translated_consistency
end Trace75BFSIPRA
