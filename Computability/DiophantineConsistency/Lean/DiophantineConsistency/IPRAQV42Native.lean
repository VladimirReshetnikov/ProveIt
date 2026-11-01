import DiophantineConsistency.AdaptiveVSignMachine43

/-! Fixed-port native endpoint after constructing an oriented witness. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAQV42Native
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open AdaptiveEquationSyntax2011

theorem literal_equivalence : IPRANativeTheory.nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveQV42Context.literal CurrentWindowCarry2011.ports)) 🡘
      ∼IPRAFoundationZFCMappedNegation.mappedNativeRefutation PRALanguage.embedding :=
  IPRAQV42ConditionalBridge.conditional_native AdaptiveVSignMachine43.machineOrients
#print axioms literal_equivalence
end DiophantineConsistency.IPRAQV42Native
