import DiophantineConsistency.Sign32DirectExpression
import DiophantineConsistency.HACurrentEquation2011
import DiophantineConsistency.IPRAExpressionNative
import DiophantineConsistency.IPRAStandardTheory

/-! UNCOMPILED direct 32-coordinate endpoint; no Jones reduction is used. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign32DirectIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing PRALanguage IPRANativeTheory
  IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat

abbrev expression := Sign32DirectExpression.expression

theorem polynomialBridge : HAExpressionAssembly.PolynomialBridge expression := by
  intro V _ _
  have currentBridge : HAExpressionAssembly.PolynomialBridge ObjectCurrentEquation2011.naturalExpression :=
    fun W _ _ => HACurrentEquation2011.polynomialBridge W
  have hB := currentBridge V
  rw [HAExpressionAssembly.classicalNoZero_iff] at hB ⊢
  rw [← hB]
  simpa only [InternalZero, not_exists, ne_eq] using not_congr (Sign32DirectExpression.zero_iff_current (V := V))

theorem native_equivalence : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ polynomialBridge

theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalence

theorem standard_translated_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero expression 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ := by
  apply (IPRAStandardTheory.provable_iff _).2
  obtain ⟨h⟩ := (IPRAStandardTheory.provable_iff _).1 standard_equivalence
  have z := IPRABoundedRhoZFC.zfcEquiv
  exact ⟨Entailment.K_intro
    (Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z))
    (Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h))⟩
end DiophantineConsistency.Sign32DirectIPRA
#print axioms DiophantineConsistency.Sign32DirectIPRA.polynomialBridge
#print axioms DiophantineConsistency.Sign32DirectIPRA.native_equivalence
#print axioms DiophantineConsistency.Sign32DirectIPRA.standard_equivalence
#print axioms DiophantineConsistency.Sign32DirectIPRA.standard_translated_equivalence
