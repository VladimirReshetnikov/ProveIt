import DiophantineConsistency.IPRANamedValues26Native
import DiophantineConsistency.HAExpressionNoZeroEquiv
import DiophantineConsistency.AdaptiveNamedValues33

/-! Native endpoint for the fixed-port thirty-three-variable named-value literal. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRANamedValues33Native
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011

def literalNatural : Expr (Fin 33) := positiveShift
  (AdaptiveNamedValues33.literal CurrentWindowCarry2011.ports)

theorem sameNoZero33 : HAExpressionNoZeroEquiv.SameNoZero literalNatural
    IPRANamedValues26Native.literalNatural := by
  intro V _ _
  simpa only [literalNatural, IPRANamedValues26Native.literalNatural] using
    (AdaptiveNamedValues33.shifted_no_zero_iff (V := V) CurrentWindowCarry2011.ports)

theorem bridge33 : HAExpressionAssembly.PolynomialBridge literalNatural :=
  HAExpressionNoZeroEquiv.bridge literalNatural IPRANamedValues26Native.literalNatural
    sameNoZero33 IPRANamedValues26Native.bridge26

theorem literal_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveNamedValues33.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge literalNatural bridge33

end DiophantineConsistency.IPRANamedValues33Native
