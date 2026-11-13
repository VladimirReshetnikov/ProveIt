import OrdinarySphere7084Model
import FreshCarrier94

/-! Standard-iPRA and mapped GG-consistency endpoints for the literal 70/84 sphere. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.OrdinarySphere7084IPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat
open HAExpressionAssembly FoundationHANoZero

theorem bridge70 : PolynomialBridge
    (positiveShift (OrdinarySphere7084Literal.expressionAt CurrentWindowCarry2011.ports)) := by
  intro V _ _
  have eqv : (classicalNoZero (positiveShift
      (OrdinarySphere7084Literal.expressionAt CurrentWindowCarry2011.ports))).Evalb (M := V) ![] ↔
      (classicalNoZero Carrier94Syntax.naturalExpression94).Evalb (M := V) ![] := by
    rw [classicalNoZero_iff, classicalNoZero_iff]
    simpa only [InternalZero, ne_eq] using
      (forall_congr' fun v : Fin 14 → V => not_congr (OrdinarySphere7084Model.sameZero94 v))
  exact eqv.trans (FreshCarrier94.bridge94 V)

theorem native_equivalence70 : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero
      (positiveShift (OrdinarySphere7084Literal.expressionAt CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ bridge70

theorem standard_equivalence70 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero
      (positiveShift (OrdinarySphere7084Literal.expressionAt CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalence70

theorem standard_translated_equivalence70 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero
      (positiveShift (OrdinarySphere7084Literal.expressionAt CurrentWindowCarry2011.ports)) 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ := by
  apply (IPRAStandardTheory.provable_iff _).2
  obtain ⟨h⟩ := native_equivalence70
  have z := IPRABoundedRhoZFC.zfcEquiv
  exact ⟨Entailment.K_intro
    (Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z))
    (Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h))⟩

#print axioms bridge70
#print axioms standard_equivalence70
#print axioms standard_translated_equivalence70
end DiophantineConsistency.OrdinarySphere7084IPRA
