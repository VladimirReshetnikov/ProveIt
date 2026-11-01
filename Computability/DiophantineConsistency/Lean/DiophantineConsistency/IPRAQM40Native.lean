import DiophantineConsistency.AdaptiveQM40Model
import DiophantineConsistency.IPRAQF41Native

/-! Fixed-port native endpoint for the positive two-root quotient graph. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAQM40Native
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011

def literalNatural : Expr (Fin 40) := positiveShift
  (AdaptiveQM40Context.literal CurrentWindowCarry2011.ports)

theorem sameNoZero40 : HAExpressionNoZeroEquiv.SameNoZero literalNatural
    (positiveShift (AdaptiveQF41Context.literal CurrentWindowCarry2011.ports)) := by
  intro V _ _
  exact AdaptiveQM40Model.shifted_no_zero_iff CurrentWindowCarry2011.ports

theorem bridge40 : HAExpressionAssembly.PolynomialBridge literalNatural :=
  HAExpressionNoZeroEquiv.bridge literalNatural
    (positiveShift (AdaptiveQF41Context.literal CurrentWindowCarry2011.ports))
    sameNoZero40
    IPRAQF41Native.bridge41

theorem literal_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveQM40Context.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge literalNatural bridge40
end DiophantineConsistency.IPRAQM40Native
