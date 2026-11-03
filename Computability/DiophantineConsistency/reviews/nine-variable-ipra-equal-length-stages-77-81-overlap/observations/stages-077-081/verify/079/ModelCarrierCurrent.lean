import DiophantineConsistency.ModelArithmetic
import DiophantineConsistency.ModelCarrierScaled
import DiophantineConsistency.ModelCarrierSyntax
import DiophantineConsistency.HACurrentEquation2011
import DiophantineConsistency.HAExpressionSameZero
import DiophantineConsistency.IPRAExpressionNative
import DiophantineConsistency.IPRAStandardTheory
import DiophantineConsistency.IPRAReferenceInductionConversion
/-! # iPRA endpoints for the scaled fourteen-variable carrier forms

The 14-variable 67-operation degree-106 form (`CarrierNormalizedProduct106`)
and the 66/118 form it is derived from (`CarrierScaledAuxiliary118`) keep the
maintained equation's fourteen coordinates and four ports. Their positive zero
sets coincide with the maintained Carrier65 zero set in every model of `𝗜𝚺₁`:
the integer argument runs unchanged in the model's ring of differences
(`ModelDifferenceRing`), using discreteness, the units `±1` and reduction
modulo four. The maintained all-model bridge then transfers, giving native,
standard and equality-only iPRA proofs of each form's no-zero sentence iff
Foundation's ZFC consistency predicate. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiophantineConsistency.ModelCarrierCurrent
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing DiscreteOrderedRingFacts ModelArithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation

section Eval
variable {R : Type*} [CommRing R]

theorem evalRing_expressionAt65 (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (ObjectCurrentEquation2011.expressionAt p).evalRing v =
      Carrier65.value (fun j => (p j : R)) v := by
  simp only [ObjectCurrentEquation2011.expressionAt, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_pow, Expr.evalRing_var,
    Expr.evalRing_constant, Expr.evalRing_ofNat, Nat.cast_ofNat, Nat.cast_one,
    Carrier65.value, Carrier65.core]

end Eval

/-! ### The ring of differences of a model -/

section Model
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem shifted_pos (v : Fin 14 → V) (j : Fin 14) : (0 : DiffRing V) < ι (v j + 1) := by
  rw [← map_zero ι, ι_lt_ι]; exact lt_of_lt_of_le _root_.zero_lt_one le_add_self

theorem beta_pos : (0 : DiffRing V) < ((CurrentWindowCarry2011.ports 0 : ℤ) : DiffRing V) := by
  have hp : 1 < CurrentMasks2011.radix ^ 2011 :=
    one_lt_pow₀ (by decide : 1 < CurrentMasks2011.radix) (by decide)
  have hb : 0 < CurrentMasks2011.beta := by unfold CurrentMasks2011.beta; omega
  have h0 : CurrentWindowCarry2011.ports 0 = (CurrentMasks2011.beta : ℤ) := rfl
  rw [h0]
  exact_mod_cast hb

/-- In every model of `𝗜𝚺₁`, the 67/106 form has exactly the maintained zeros. -/
theorem sameZero106 (v : Fin 14 → V) :
    InternalZero (positiveShift (expressionAt106 CurrentWindowCarry2011.ports)) v ↔
      InternalZero ObjectCurrentEquation2011.naturalExpression v := by
  change InternalZero (positiveShift (expressionAt106 CurrentWindowCarry2011.ports)) v ↔
    InternalZero (positiveShift ObjectCurrentEquation2011.expression) v
  rw [internalZero_positiveShift, internalZero_positiveShift, internalZero_iff, internalZero_iff,
    evalRing_expressionAt106, ObjectCurrentEquation2011.expression, evalRing_expressionAt65]
  exact ModelCarrierScaled.zero_iff106 model_discrete mod4 _ _ beta_pos (shifted_pos v)

/-- In every model of `𝗜𝚺₁`, the 66/118 form has exactly the maintained zeros. -/
theorem sameZero118 (v : Fin 14 → V) :
    InternalZero (positiveShift (expressionAt118 CurrentWindowCarry2011.ports)) v ↔
      InternalZero ObjectCurrentEquation2011.naturalExpression v := by
  change InternalZero (positiveShift (expressionAt118 CurrentWindowCarry2011.ports)) v ↔
    InternalZero (positiveShift ObjectCurrentEquation2011.expression) v
  rw [internalZero_positiveShift, internalZero_positiveShift, internalZero_iff, internalZero_iff,
    evalRing_expressionAt118, ObjectCurrentEquation2011.expression, evalRing_expressionAt65]
  exact ModelCarrierScaled.zero_iff118 model_discrete mod4 _ _ beta_pos (shifted_pos v)

end Model

/-! ### Bridges and iPRA endpoints -/

theorem currentBridge :
    HAExpressionAssembly.PolynomialBridge ObjectCurrentEquation2011.naturalExpression :=
  fun V _ _ => HACurrentEquation2011.polynomialBridge V

theorem bridge106 : HAExpressionAssembly.PolynomialBridge
    (positiveShift (expressionAt106 CurrentWindowCarry2011.ports)) :=
  HAExpressionSameZero.bridge _ _ (fun _ _ _ v => sameZero106 v) currentBridge

theorem bridge118 : HAExpressionAssembly.PolynomialBridge
    (positiveShift (expressionAt118 CurrentWindowCarry2011.ports)) :=
  HAExpressionSameZero.bridge _ _ (fun _ _ _ v => sameZero118 v) currentBridge

/-- **Native iPRA: the 67/106 form has no positive zero iff ZFC is consistent.** -/
theorem native_equivalence106 : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt106 CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ bridge106

theorem standard_equivalence106 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt106 CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalence106

theorem reference_equivalence106 : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero
      (positiveShift (expressionAt106 CurrentWindowCarry2011.ports))) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  IPRAReferenceInductionConversion.nativeToReference native_equivalence106

/-- **Native iPRA: the 66/118 form has no positive zero iff ZFC is consistent.** -/
theorem native_equivalence118 : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt118 CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ bridge118

theorem standard_equivalence118 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt118 CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalence118

theorem reference_equivalence118 : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero
      (positiveShift (expressionAt118 CurrentWindowCarry2011.ports))) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  IPRAReferenceInductionConversion.nativeToReference native_equivalence118

end DiophantineConsistency.ModelCarrierCurrent
