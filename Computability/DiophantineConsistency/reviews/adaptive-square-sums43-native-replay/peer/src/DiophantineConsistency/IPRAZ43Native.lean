import DiophantineConsistency.IPRAZ44Native
import DiophantineConsistency.AdaptiveZ43FixedPort

/-! Native endpoint for the fixed-port positive-main-root 43-variable literal. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAZ43Native
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveScaledNorms2011

def literalNatural : Expr (Fin 43) := positiveShift
  (AdaptiveZ43Context.literal CurrentWindowCarry2011.ports)

theorem sameNoZero43 : HAExpressionNoZeroEquiv.SameNoZero literalNatural
    IPRAZ44Native.literalNatural := by
  intro V _ _
  have hb : (2:V) ≤ (currentPorts 0:V) := AdaptiveZ43FixedPort.fixed_port_bound
  simpa only [literalNatural, IPRAZ44Native.literalNatural, currentPorts_cast] using
    (AdaptiveZ43Model.shifted_no_zero_iff (V := V) currentPorts hb)

theorem bridge43 : HAExpressionAssembly.PolynomialBridge literalNatural :=
  HAExpressionNoZeroEquiv.bridge literalNatural IPRAZ44Native.literalNatural
    sameNoZero43 IPRAZ44Native.bridge44

theorem literal_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveZ43Context.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge literalNatural bridge43
end DiophantineConsistency.IPRAZ43Native
