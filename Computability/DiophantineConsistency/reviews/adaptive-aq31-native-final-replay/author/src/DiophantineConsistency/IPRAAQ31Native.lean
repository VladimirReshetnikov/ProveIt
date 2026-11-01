import DiophantineConsistency.AdaptiveVSignMachine32
import DiophantineConsistency.IPRAAQ31ConditionalBridge

/-! Native endpoint for the fixed-port thirty-one-variable degree-six literal. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAAQ31Native
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011

theorem machineOrients : IPRAAQ31ConditionalBridge.MachineOrients := by
  intro V _ _ h
  obtain ⟨T,hT⟩ := h
  exact AdaptiveVSignMachine32.from_run T hT

theorem literal_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveAQ31Literal.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAAQ31ConditionalBridge.conditional_native machineOrients
#print axioms machineOrients
#print axioms literal_equivalence
end DiophantineConsistency.IPRAAQ31Native
