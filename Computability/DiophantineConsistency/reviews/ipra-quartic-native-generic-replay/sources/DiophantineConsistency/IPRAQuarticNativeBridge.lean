import DiophantineConsistency.IPRAQuarticPositiveBridge
import DiophantineConsistency.HAExpressionNoZeroEquiv
import DiophantineConsistency.IPRAExpressionNative
/-! Transfer an existing expression bridge to the positive-coordinate tree quartic.
The original expression bridge is an explicit premise. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAQuarticNativeBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011 IPRAQuarticPositiveBridge

theorem sameNoZero {m : ℕ} (e : Expr (Fin m)) :
    HAExpressionNoZeroEquiv.SameNoZero (positiveShift (rawQuartic e)) e := by
  intro V _ _
  exact shifted_no_zero_iff e

theorem bridge {m : ℕ} (e : Expr (Fin m)) (h : HAExpressionAssembly.PolynomialBridge e) :
    HAExpressionAssembly.PolynomialBridge (positiveShift (rawQuartic e)) :=
  HAExpressionNoZeroEquiv.bridge (positiveShift (rawQuartic e)) e (sameNoZero e) h

theorem native_equivalence {m : ℕ} (e : Expr (Fin m)) (h : HAExpressionAssembly.PolynomialBridge e) :
    nativeTheory ⊢ IPRAExpressionNative.nativeNoZero (positiveShift (rawQuartic e)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ (bridge e h)
#print axioms native_equivalence
end DiophantineConsistency.IPRAQuarticNativeBridge
