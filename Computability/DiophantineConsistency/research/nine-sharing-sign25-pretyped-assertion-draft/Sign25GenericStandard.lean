import DiophantineConsistency.IPRAExpressionNative
import DiophantineConsistency.IPRAStandardTheory

/-! SOURCE-ONLY candidate: standard endpoint for an arbitrary bridged expression. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign25GenericStandard
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory
  IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat
attribute [local irreducible] IPRAExpressionNative.nativeNoZero

theorem standard_of_bridge {n : ℕ} (e : Expr (Fin n))
    (hp : HAExpressionAssembly.PolynomialBridge e) :
    IPRAStandardTheory.standardTheory ⊢
      IPRAExpressionNative.nativeNoZero e 🡘 ∼mappedNativeRefutation embedding :=
  IPRAStandardTheory.transfer IPRAStandardTheory.native_axiom
    (IPRAExpressionNative.equivalence_of_bridge e hp)

theorem standard_of_bridge_eq {n : ℕ} (e : Expr (Fin n))
    (hp : HAExpressionAssembly.PolynomialBridge e) (φ : Sentenceᵢ language)
    (hφ : φ = (IPRAExpressionNative.nativeNoZero e 🡘 ∼mappedNativeRefutation embedding)) :
    IPRAStandardTheory.standardTheory ⊢ φ := by
  rw [hφ]
  exact standard_of_bridge e hp
end DiophantineConsistency.Sign25GenericStandard
#print axioms DiophantineConsistency.Sign25GenericStandard.standard_of_bridge
#print axioms DiophantineConsistency.Sign25GenericStandard.standard_of_bridge_eq
