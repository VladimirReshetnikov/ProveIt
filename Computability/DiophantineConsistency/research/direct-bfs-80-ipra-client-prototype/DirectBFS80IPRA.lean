import DirectBFS80ModelIffCorrected
import PositiveModelIPRAReferenceTranslated

/-! Client of the generic iPRA adapters for the symbolic 80-operation graph. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFS80IPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open CompactFixedBeta CompactSymbolicPorts CompactSymbolicKernel
open TenPositive80Graph TenPositive80Factors DirectBFS80ModelIffCorrected
open PositiveModelIPRAAdapter PositiveModelIPRAStandardAdapter PositiveModelIPRAReferenceTranslated
open PRALanguage IPRAStandardTheory IPRAEqualityOnlyReference IPRAOrderErasure
open IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat
attribute [local irreducible] rho DirectBFSSymbolicKernel.paramKernel CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat

theorem positive_bridge (p : Fin 4 → ℕ)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho)
    (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat) :
    PositiveModelBridge (graph (integerPorts p)).output := by
  intro V _ _
  exact positive_model_iff (V:=V) p hp0 hp1 hp2 hp3

theorem standard_consistency (p : Fin 4 → ℕ)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho)
    (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat) : standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (graph (integerPorts p)).output) 🡘
      ∼mappedNativeRefutation embedding :=
  standard_equivalence_of_positive _ (positive_bridge p hp0 hp1 hp2 hp3)

theorem standard_translated_consistency (p : Fin 4 → ℕ)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho)
    (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat) : standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (graph (integerPorts p)).output) 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ :=
  standard_translated_of_positive _ (positive_bridge p hp0 hp1 hp2 hp3)

theorem reference_consistency (p : Fin 4 → ℕ)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho)
    (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat) : referenceTheory ⊢
    erase (IPRAExpressionNative.nativeNoZero (positiveShift (graph (integerPorts p)).output)) 🡘
      ∼erase (mappedNativeRefutation embedding) :=
  reference_equivalence_of_positive _ (positive_bridge p hp0 hp1 hp2 hp3)

theorem reference_translated_consistency (p : Fin 4 → ℕ)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho)
    (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat) : referenceTheory ⊢
    erase (IPRAExpressionNative.nativeNoZero (positiveShift (graph (integerPorts p)).output)) 🡘
      erase ((Semiformula.lMap embedding sourceSentence)ᴺ) :=
  reference_translated_of_positive _ (positive_bridge p hp0 hp1 hp2 hp3)

#print axioms DirectBFS80IPRA.positive_bridge
#print axioms DirectBFS80IPRA.standard_consistency
#print axioms DirectBFS80IPRA.standard_translated_consistency
#print axioms DirectBFS80IPRA.reference_consistency
#print axioms DirectBFS80IPRA.reference_translated_consistency
end DirectBFS80IPRA
