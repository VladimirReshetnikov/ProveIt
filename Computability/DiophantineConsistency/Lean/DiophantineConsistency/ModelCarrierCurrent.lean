import DiophantineConsistency.ModelArithmetic
import DiophantineConsistency.ModelCarrierScaled
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

/-! ### Literal syntax -/

/-- The 67/106 polynomial: the Carrier65 front with the normalized product. -/
def expressionAt106 (p : Fin 4 → ℤ) : Expr (Fin 14) :=
  let J : Expr (Fin 14) := .var 0
  let F : Expr (Fin 14) := .var 1
  let alpha : Expr (Fin 14) := .var 2
  let z : Expr (Fin 14) := .var 3
  let f : Expr (Fin 14) := .var 4
  let i : Expr (Fin 14) := .var 5
  let T : Expr (Fin 14) := .var 6
  let s : Expr (Fin 14) := .var 7
  let w : Expr (Fin 14) := .var 8
  let n : Expr (Fin 14) := .var 9
  let eta : Expr (Fin 14) := .var 10
  let zeta : Expr (Fin 14) := .var 11
  let y : Expr (Fin 14) := .var 12
  let gamma : Expr (Fin 14) := .var 13
  let b := Expr.constant (p 0) * J
  let q := b + 1
  let C := q - F - alpha
  let X := w * q
  let Y := s * q ^ 3
  let E := X * Y
  let k := eta + zeta
  let ell := E * k * Y
  let c := k * Y + eta
  let a := E + Y
  let H := 4 * a + 3
  let delta := a ^ 2 + H
  let D := X + a * c + gamma * H
  let rank := (b * (q - F) + alpha) * (q ^ 2 - 1) +
    (Expr.constant (p 2) + q * Expr.constant (p 3)) * J
  let tau := E * n + k - rank
  let V := f ^ 2 * (c * T - rank) - c
  let P := tau ^ 2 - ell * (ell + k)
  let Q := D ^ 2 - delta * c ^ 2
  let W := (Expr.constant (p 1) + w) * C + (q - F) - z * b
  P * Q * (delta * (f ^ 2 - 1) * (V ^ 2 - y ^ 2) + y ^ 2) * W *
    (f ^ 2 - delta * (i * c ^ 2) ^ 2) - 1

/-- The 66/118 polynomial: the Carrier65 front with the scaled auxiliary factor. -/
def expressionAt118 (p : Fin 4 → ℤ) : Expr (Fin 14) :=
  let J : Expr (Fin 14) := .var 0
  let F : Expr (Fin 14) := .var 1
  let alpha : Expr (Fin 14) := .var 2
  let z : Expr (Fin 14) := .var 3
  let f : Expr (Fin 14) := .var 4
  let i : Expr (Fin 14) := .var 5
  let T : Expr (Fin 14) := .var 6
  let s : Expr (Fin 14) := .var 7
  let w : Expr (Fin 14) := .var 8
  let n : Expr (Fin 14) := .var 9
  let eta : Expr (Fin 14) := .var 10
  let zeta : Expr (Fin 14) := .var 11
  let y : Expr (Fin 14) := .var 12
  let gamma : Expr (Fin 14) := .var 13
  let b := Expr.constant (p 0) * J
  let q := b + 1
  let C := q - F - alpha
  let X := w * q
  let Y := s * q ^ 3
  let E := X * Y
  let k := eta + zeta
  let ell := E * k * Y
  let c := k * Y + eta
  let a := E + Y
  let H := 4 * a + 3
  let delta := a ^ 2 + H
  let D := X + a * c + gamma * H
  let rank := (b * (q - F) + alpha) * (q ^ 2 - 1) +
    (Expr.constant (p 2) + q * Expr.constant (p 3)) * J
  let tau := E * n + k - rank
  let V := f ^ 2 * (c * T - rank) - c
  let S := i * delta * c ^ 2
  let P := tau ^ 2 - ell * (ell + k)
  let Q := D ^ 2 - delta * c ^ 2
  let W := (Expr.constant (p 1) + w) * C + (q - F) - z * b
  let Z := delta * f ^ 2 - S ^ 2
  P * Q * ((delta * f ^ 2 - delta) * (V ^ 2 - y ^ 2) + y ^ 2) * W * Z - delta

section Eval
variable {R : Type*} [CommRing R]

theorem evalRing_expressionAt106 (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (expressionAt106 p).evalRing v = ModelCarrierScaled.value106 (fun j => (p j : R)) v := by
  simp only [expressionAt106, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_pow, Expr.evalRing_var,
    Expr.evalRing_constant, Expr.evalRing_ofNat, Nat.cast_ofNat, Nat.cast_one,
    ModelCarrierScaled.value106, Carrier65.strong, Carrier65.core]

theorem evalRing_expressionAt118 (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (expressionAt118 p).evalRing v = ModelCarrierScaled.value118 (fun j => (p j : R)) v := by
  simp only [expressionAt118, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_pow, Expr.evalRing_var,
    Expr.evalRing_constant, Expr.evalRing_ofNat, Nat.cast_ofNat, Nat.cast_one,
    ModelCarrierScaled.value118, Carrier65.core]

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
