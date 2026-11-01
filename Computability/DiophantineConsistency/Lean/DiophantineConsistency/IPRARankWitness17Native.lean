import DiophantineConsistency.IPRAMainScaleWitness16Native
import DiophantineConsistency.HAExpressionNoZeroEquiv
import DiophantineConsistency.AdaptiveRankWitness17

/-! Native endpoint for the fixed-port seventeen-variable rank witness literal. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRARankWitness17Native
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011

def literalNatural : Expr (Fin 17) := positiveShift
  (AdaptiveRankWitness17.literal CurrentWindowCarry2011.ports)

theorem sameNoZero17 : HAExpressionNoZeroEquiv.SameNoZero literalNatural
    IPRAMainScaleWitness16Native.literalNatural := by
  intro V _ _
  simpa only [literalNatural, IPRAMainScaleWitness16Native.literalNatural] using
    (AdaptiveRankWitness17.current_no_zero_iff (V := V))

theorem bridge17 : HAExpressionAssembly.PolynomialBridge literalNatural :=
  HAExpressionNoZeroEquiv.bridge literalNatural IPRAMainScaleWitness16Native.literalNatural
    sameNoZero17 IPRAMainScaleWitness16Native.bridge16

theorem literal_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveRankWitness17.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge literalNatural bridge17

end DiophantineConsistency.IPRARankWitness17Native
