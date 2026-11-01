import DiophantineConsistency.IPRAScaleWitness15Native
import DiophantineConsistency.HAExpressionNoZeroEquiv
import DiophantineConsistency.AdaptiveMainScaleWitness16

/-! Native endpoint for the fixed-port sixteen-variable main-scale witness literal. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAMainScaleWitness16Native
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011

def literalNatural : Expr (Fin 16) := positiveShift
  (AdaptiveMainScaleWitness16.literal CurrentWindowCarry2011.ports)

theorem sameNoZero16 : HAExpressionNoZeroEquiv.SameNoZero literalNatural
    IPRAScaleWitness15Native.literalNatural := by
  intro V _ _
  simpa only [literalNatural, IPRAScaleWitness15Native.literalNatural] using
    (AdaptiveMainScaleWitness16.current_no_zero_iff (V := V))

theorem bridge16 : HAExpressionAssembly.PolynomialBridge literalNatural :=
  HAExpressionNoZeroEquiv.bridge literalNatural IPRAScaleWitness15Native.literalNatural
    sameNoZero16 IPRAScaleWitness15Native.bridge15

theorem literal_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveMainScaleWitness16.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge literalNatural bridge16

end DiophantineConsistency.IPRAMainScaleWitness16Native
