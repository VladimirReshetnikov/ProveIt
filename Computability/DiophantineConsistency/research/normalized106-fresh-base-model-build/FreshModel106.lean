import DiophantineConsistency.ModelArithmetic
import DiophantineConsistency.ModelCarrierScaled
import DiophantineConsistency.ModelCarrierSyntax
import DiophantineConsistency.HACurrentEquation2011
import DiophantineConsistency.IPRAExpressionNative
import DiophantineConsistency.IPRAStandardTheory

/-! Same-zero and iPRA endpoint for the 67-operation expression, using
the current14 source-built provider and a local generic bridge. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.FreshModel106
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing DiscreteOrderedRingFacts ModelArithmetic
open ModelCarrierCurrent
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open HAExpressionAssembly FoundationHANoZero

theorem evalRing_expressionAt65 {R : Type*} [CommRing R]
    (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (ObjectCurrentEquation2011.expressionAt p).evalRing v =
      Carrier65.value (fun j => (p j : R)) v := by
  simp only [ObjectCurrentEquation2011.expressionAt, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_pow, Expr.evalRing_var,
    Expr.evalRing_constant, Expr.evalRing_ofNat, Nat.cast_ofNat, Nat.cast_one,
    Carrier65.value, Carrier65.core]

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

theorem sameZero106 (v : Fin 14 → V) :
    InternalZero (positiveShift (expressionAt106 CurrentWindowCarry2011.ports)) v ↔
      InternalZero ObjectCurrentEquation2011.naturalExpression v := by
  change InternalZero (positiveShift (expressionAt106 CurrentWindowCarry2011.ports)) v ↔
    InternalZero (positiveShift ObjectCurrentEquation2011.expression) v
  rw [internalZero_positiveShift, internalZero_positiveShift, internalZero_iff, internalZero_iff,
    evalRing_expressionAt106, ObjectCurrentEquation2011.expression, evalRing_expressionAt65]
  exact ModelCarrierScaled.zero_iff106 model_discrete mod4 _ _ beta_pos (shifted_pos v)
end Model

theorem bridge106 : PolynomialBridge
    (positiveShift (expressionAt106 CurrentWindowCarry2011.ports)) := by
  intro V _ _
  have eqv : (classicalNoZero (positiveShift
      (expressionAt106 CurrentWindowCarry2011.ports))).Evalb (M := V) ![] ↔
      (classicalNoZero ObjectCurrentEquation2011.naturalExpression).Evalb (M := V) ![] := by
    rw [classicalNoZero_iff, classicalNoZero_iff]
    simpa only [InternalZero, ne_eq] using
      (forall_congr' fun v : Fin 14 → V => not_congr (sameZero106 v))
  exact eqv.trans (HACurrentEquation2011.polynomialBridge V)

theorem native_equivalence106 : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt106 CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ bridge106

theorem standard_equivalence106 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt106 CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalence106

#print axioms sameZero106
#print axioms bridge106
#print axioms standard_equivalence106
end DiophantineConsistency.FreshModel106
