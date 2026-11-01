import DiophantineConsistency.AdaptiveQF41Model
import DiophantineConsistency.IPRAQV42Native

/-! Fixed-port native endpoint for the positive first-root quotient graph. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAQF41Native
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011

def literalNatural : Expr (Fin 41) := positiveShift
  (AdaptiveQF41Context.literal CurrentWindowCarry2011.ports)

theorem sameNoZero41 : HAExpressionNoZeroEquiv.SameNoZero literalNatural
    (positiveShift (AdaptiveQV42Context.literal CurrentWindowCarry2011.ports)) := by
  intro V _ _
  exact AdaptiveQF41Model.shifted_no_zero_iff CurrentWindowCarry2011.ports

theorem bridge41 : HAExpressionAssembly.PolynomialBridge literalNatural :=
  HAExpressionNoZeroEquiv.bridge literalNatural
    (positiveShift (AdaptiveQV42Context.literal CurrentWindowCarry2011.ports))
    sameNoZero41
    (IPRAQV42ConditionalBridge.bridge42_of_machineOrients AdaptiveVSignMachine43.machineOrients)

theorem literal_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveQF41Context.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge literalNatural bridge41
end DiophantineConsistency.IPRAQF41Native
