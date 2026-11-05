import DiophantineConsistency.ModelThirteenCarrier
/-! # iPRA endpoints for the thirteen-variable 70/140 and 71/128 carrier forms

`ThirteenCarrier.positive_zero_sets` proves over `ℤ` that the 69, 70 and 71
forms have the same positive zeros. The argument (a scaled identity, positivity
of the discriminant and the mod-4 exclusion of the negative unit) is replayed
over any discretely ordered ring with the carrier facts, so in every model of
`𝗜𝚺₁` the 70 and 71 forms have exactly the 69 zeros, and `ModelThirteenCarrier.bridge69`
transfers. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace DiophantineConsistency.ModelThirteenForms
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
open AdaptiveEquationSyntax2011 ModelDifferenceRing DiscreteOrderedRingFacts FreshCarrierSpheres
open ModelThirteenCarrier

/-! ### The zero-set equivalences in a discretely ordered ring -/

section Generic
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem scaled_identity (m a f t gap y : R) :
    let δ := (a + 2) ^ 2 - 1
    m * (δ ^ 2 * t ^ 2 * gap + y ^ 2) * (δ * f ^ 2 - δ ^ 2 * t ^ 2) - δ =
      δ * ModelCarrierScaled.product m (δ ^ 2 * t ^ 2) gap y (f ^ 2 - δ * t ^ 2) := by
  dsimp only [ModelCarrierScaled.product]
  ring

theorem scaled_zero_iff_reduced (F : Facts R) {m a f t gap y : R}
    (hδ : (a + 2) ^ 2 - 1 ≠ 0) :
    let δ := (a + 2) ^ 2 - 1
    m * (δ ^ 2 * t ^ 2 * gap + y ^ 2) * (δ * f ^ 2 - δ ^ 2 * t ^ 2) - δ = 0 ↔
      ModelCarrierScaled.product m (δ * (f ^ 2 - 1)) gap y (f ^ 2 - δ * t ^ 2) = 0 := by
  obtain ⟨φ⟩ := F.mod4
  dsimp only
  rw [scaled_identity, mul_eq_zero]
  simp only [hδ, false_or]
  exact ModelCarrierScaled.replace_coefficient F.discrete (ModelCarrierScaled.strong_ne_neg_one φ a f t)

theorem delta_pos (F : Facts R) (p : Fin 4 → R) (v : Fin 13 → R)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) : 0 < (ThirteenCarrier.core p v).delta := by
  have hq : 0 < p 0 * v 0 + 1 := by have := mul_pos hb (hv 0); linarith
  have hX : 0 < v 7 * (p 0 * v 0 + 1) := mul_pos (hv 7) hq
  have hY : 0 < v 6 * (p 0 * v 0 + 1) ^ 3 := mul_pos (hv 6) (pow_pos hq _)
  have ha : 0 < (ThirteenCarrier.core p v).a := add_pos (mul_pos hX hY) hY
  rw [ThirteenCarrier.delta_shape]
  nlinarith

theorem zero69_iff71 (F : Facts R) (p : Fin 4 → R) (v : Fin 13 → R)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) :
    ThirteenCarrier.value69 p v = 0 ↔ ThirteenCarrier.value71 p v = 0 := by
  have hd := (delta_pos F p v hb hv).ne'
  have he := scaled_zero_iff_reduced F
    (m := (ThirteenCarrier.core p v).P * (ThirteenCarrier.core p v).Q)
    (f := (ThirteenCarrier.core p v).f) (t := (ThirteenCarrier.core p v).t)
    (gap := (ThirteenCarrier.core p v).gap) (y := (ThirteenCarrier.core p v).y)
    (a := (ThirteenCarrier.core p v).a)
    (by rwa [← ThirteenCarrier.delta_shape] : ((ThirteenCarrier.core p v).a + 2) ^ 2 - 1 ≠ 0)
  dsimp only at he
  rw [← ThirteenCarrier.delta_shape] at he
  have hleft : ThirteenCarrier.value69 p v =
      ((ThirteenCarrier.core p v).P * (ThirteenCarrier.core p v).Q) *
        ((ThirteenCarrier.core p v).delta ^ 2 * (ThirteenCarrier.core p v).t ^ 2 *
          (ThirteenCarrier.core p v).gap + (ThirteenCarrier.core p v).y ^ 2) *
        ((ThirteenCarrier.core p v).delta * (ThirteenCarrier.core p v).f ^ 2 -
          (ThirteenCarrier.core p v).delta ^ 2 * (ThirteenCarrier.core p v).t ^ 2) -
        (ThirteenCarrier.core p v).delta := by
    dsimp only [ThirteenCarrier.value69]
    ring
  rw [hleft, he]
  unfold ModelCarrierScaled.product ThirteenCarrier.value71
  constructor <;> intro h <;> linear_combination h

theorem zero70_iff71 (F : Facts R) (p : Fin 4 → R) (v : Fin 13 → R)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) :
    ThirteenCarrier.value70 p v = 0 ↔ ThirteenCarrier.value71 p v = 0 := by
  rw [ThirteenCarrier.scaled_identity, mul_eq_zero]
  simp only [(delta_pos F p v hb hv).ne', false_or]

end Generic

/-! ### Literal syntax -/

/-- The 13/70/140 polynomial. -/
def expressionAt70 (p : Fin 4 → ℤ) : Expr (Fin 13) :=
  front13 p fun P Q _ f delta gap y t =>
    P * Q * (delta * (f ^ 2 - 1) * gap + y ^ 2) * (delta * f ^ 2 - (delta * t) ^ 2) - delta

/-- The 13/71/128 polynomial. -/
def expressionAt71 (p : Fin 4 → ℤ) : Expr (Fin 13) :=
  front13 p fun P Q _ f delta gap y t =>
    P * Q * (delta * (f ^ 2 - 1) * gap + y ^ 2) * (f ^ 2 - delta * t ^ 2) - 1

theorem evalRing_expressionAt70 {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (expressionAt70 p).evalRing v = ThirteenCarrier.value70 (fun j => (p j : R)) v := by
  simp only [expressionAt70, front13, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_pow, Expr.evalRing_var,
    Expr.evalRing_constant, Expr.evalRing_ofNat, Nat.cast_ofNat, Nat.cast_one,
    ThirteenCarrier.value70, ThirteenCarrier.core]

theorem evalRing_expressionAt71 {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (expressionAt71 p).evalRing v = ThirteenCarrier.value71 (fun j => (p j : R)) v := by
  simp only [expressionAt71, front13, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_pow, Expr.evalRing_var,
    Expr.evalRing_constant, Expr.evalRing_ofNat, Nat.cast_ofNat, Nat.cast_one,
    ThirteenCarrier.value71, ThirteenCarrier.core]

/-! ### Models of `𝗜𝚺₁` -/

section Model
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem shifted13_pos (u : Fin 13 → V) (j : Fin 13) : (0 : DiffRing V) < ι (u j + 1) :=
  ι_pos (lt_of_lt_of_le _root_.zero_lt_one le_add_self)

theorem sameZero70 (u : Fin 13 → V) :
    InternalZero (positiveShift (expressionAt70 CurrentWindowCarry2011.ports)) u ↔
      InternalZero (positiveShift (expressionAt69 CurrentWindowCarry2011.ports)) u := by
  rw [internalZero_positiveShift, internalZero_positiveShift, internalZero_iff, internalZero_iff,
    evalRing_expressionAt70, evalRing_expressionAt69]
  exact (zero70_iff71 modelFacts ringPorts (fun i => ι (u i + 1)) FreshModel106.beta_pos (shifted13_pos u)).trans
    (zero69_iff71 modelFacts ringPorts (fun i => ι (u i + 1)) FreshModel106.beta_pos (shifted13_pos u)).symm

theorem sameZero71 (u : Fin 13 → V) :
    InternalZero (positiveShift (expressionAt71 CurrentWindowCarry2011.ports)) u ↔
      InternalZero (positiveShift (expressionAt69 CurrentWindowCarry2011.ports)) u := by
  rw [internalZero_positiveShift, internalZero_positiveShift, internalZero_iff, internalZero_iff,
    evalRing_expressionAt71, evalRing_expressionAt69]
  exact (zero69_iff71 modelFacts ringPorts (fun i => ι (u i + 1)) FreshModel106.beta_pos (shifted13_pos u)).symm

end Model

/-! ### Bridges and iPRA endpoints -/

open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation

theorem bridge70 : HAExpressionAssembly.PolynomialBridge
    (positiveShift (expressionAt70 CurrentWindowCarry2011.ports)) :=
  HAExpressionSameZero.bridge _ _ (fun _ _ _ u => sameZero70 u) bridge69

theorem bridge71 : HAExpressionAssembly.PolynomialBridge
    (positiveShift (expressionAt71 CurrentWindowCarry2011.ports)) :=
  HAExpressionSameZero.bridge _ _ (fun _ _ _ u => sameZero71 u) bridge69

/-- **Native iPRA: the 13/70/140 form has no positive zero iff ZFC is consistent.** -/
theorem native_equivalence70 : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt70 CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ bridge70

theorem standard_equivalence70 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt70 CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalence70


/-- **Native iPRA: the 13/71/128 form has no positive zero iff ZFC is consistent.** -/
theorem native_equivalence71 : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt71 CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ bridge71

theorem standard_equivalence71 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt71 CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalence71


end DiophantineConsistency.ModelThirteenForms
