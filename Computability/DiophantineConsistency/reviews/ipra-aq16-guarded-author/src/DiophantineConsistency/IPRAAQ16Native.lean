import DiophantineConsistency.IPRAAQ17Native
import DiophantineConsistency.AdaptiveAQ16

/-! Native endpoint for the fixed-port 22-variable degree-ten literal. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAAQ16Native
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011

def literalNatural : Expr (Fin 16) := positiveShift
  (AdaptiveAQ16Literal.literal CurrentWindowCarry2011.ports)

theorem sameNoZero : HAExpressionNoZeroEquiv.SameNoZero literalNatural
    IPRAAQ17Native.literalNatural := by
  intro V _ _
  simpa only [literalNatural,IPRAAQ17Native.literalNatural] using
    (AdaptiveAQ16.current_no_zero_iff (V := V))

theorem bridge16 : HAExpressionAssembly.PolynomialBridge literalNatural :=
  HAExpressionNoZeroEquiv.bridge literalNatural IPRAAQ17Native.literalNatural
    sameNoZero IPRAAQ17Native.bridge17

theorem literal_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveAQ16Literal.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge literalNatural bridge16
#print axioms sameNoZero
#print axioms bridge16
#print axioms literal_equivalence
end DiophantineConsistency.IPRAAQ16Native
