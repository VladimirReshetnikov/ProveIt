import DiophantineConsistency.IPRASquareWitnessDirect14Native
import DiophantineConsistency.HAExpressionNoZeroEquiv
import DiophantineConsistency.AdaptiveScaleWitness15

/-! Native endpoint for the fixed-port fifteen-variable scale-witness literal. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAScaleWitness15Native
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011

def literalNatural : Expr (Fin 15) := positiveShift
  (AdaptiveScaleWitness15.literal CurrentWindowCarry2011.ports)

theorem sameNoZero15 : HAExpressionNoZeroEquiv.SameNoZero literalNatural
    IPRASquareWitnessDirect14Native.literalNatural := by
  intro V _ _
  simpa only [literalNatural, IPRASquareWitnessDirect14Native.literalNatural] using
    (AdaptiveScaleWitness15.current_no_zero_iff (V := V))

theorem bridge15 : HAExpressionAssembly.PolynomialBridge literalNatural :=
  HAExpressionNoZeroEquiv.bridge literalNatural IPRASquareWitnessDirect14Native.literalNatural
    sameNoZero15 IPRASquareWitnessDirect14Native.bridge14

theorem literal_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveScaleWitness15.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge literalNatural bridge15

end DiophantineConsistency.IPRAScaleWitness15Native
