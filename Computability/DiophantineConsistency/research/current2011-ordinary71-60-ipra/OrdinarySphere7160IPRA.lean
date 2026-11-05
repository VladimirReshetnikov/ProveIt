import OrdinarySphere7160Model
import FreshCarrier94

/-! Standard-iPRA and mapped GG-consistency endpoints for the literal 71/60 sphere. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.OrdinarySphere7160IPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat
open HAExpressionAssembly FoundationHANoZero

theorem bridge71 : PolynomialBridge
    (positiveShift (OrdinarySphere7160Literal.expressionAt CurrentWindowCarry2011.ports)) := by
  intro V _ _
  have eqv : (classicalNoZero (positiveShift
      (OrdinarySphere7160Literal.expressionAt CurrentWindowCarry2011.ports))).Evalb (M := V) ![] ↔
      (classicalNoZero Carrier94Syntax.naturalExpression94).Evalb (M := V) ![] := by
    rw [classicalNoZero_iff, classicalNoZero_iff]
    simpa only [InternalZero, ne_eq] using
      (forall_congr' fun v : Fin 14 → V => not_congr (OrdinarySphere7160Model.sameZero94 v))
  exact eqv.trans (FreshCarrier94.bridge94 V)

theorem native_equivalence71 : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero
      (positiveShift (OrdinarySphere7160Literal.expressionAt CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ bridge71

theorem standard_equivalence71 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero
      (positiveShift (OrdinarySphere7160Literal.expressionAt CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalence71

theorem standard_translated_equivalence71 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero
      (positiveShift (OrdinarySphere7160Literal.expressionAt CurrentWindowCarry2011.ports)) 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ := by
  apply (IPRAStandardTheory.provable_iff _).2
  obtain ⟨h⟩ := native_equivalence71
  have z := IPRABoundedRhoZFC.zfcEquiv
  exact ⟨Entailment.K_intro
    (Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z))
    (Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h))⟩

#print axioms bridge71
#print axioms standard_equivalence71
#print axioms standard_translated_equivalence71
end DiophantineConsistency.OrdinarySphere7160IPRA
