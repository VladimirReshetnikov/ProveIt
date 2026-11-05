import FreshModel106
import DiophantineConsistency.Carrier94Value
import DiophantineConsistency.ArithmeticCarrier94Extraction
/-! # iPRA endpoints for the 14-positive 67/94 equation

Package 188's ordinary 14-positive equation (`Carrier94Syntax.expression94`,
67 operations, exact degree 94 by the package's finite check) uses the
maintained coordinates and ports with the ordinary strong norm. In every model
of `𝗜𝚺₁`:

* **soundness** (`halts_of_zero94`): a positive zero satisfies the five ordinary
  equations (`ArithmeticCarrier94Extraction.current94_equations`), which make the
  decimal215 machine halt (`ArithmeticCarrier94Soundness.ordinary_halts`);
* **completeness** (`zero94_of_zero`): a zero of the maintained equation gives a
  zero of this one, replacing only the strong multiplier `i` by `Delta i`
  (`Carrier94Value.zero94_of_maintained`).

So the two no-zero sentences agree in every model (`sameNoZero94`), and the
maintained all-model bridge transfers. This gives native and standard iPRA proofs that the no-zero sentence is
equivalent to the negation of the mapped native ZFC-refutation sentence. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiophantineConsistency.FreshCarrier94
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing DiscreteOrderedRingFacts ModelArithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open Carrier94Syntax
open SetTheory.BusyBeaver.ZFC

section Model
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **Soundness.** A natural zero of the 67/94 equation makes the machine halt. -/
theorem halts_of_zero94 (w : Fin 14 → V) (hz : InternalZero naturalExpression94 w) :
    ∃ t : V, ArithmeticCantor.first (ArithmeticMachineRun215.run t) = 0 := by
  have hz' := (ObjectCurrentEquation2011.internalZero_positiveShift expression94 w).mp hz
  have hpos : ∀ j, 0 < w j + 1 := fun j =>
    lt_of_le_of_lt (Arithmetic.zero_le (w j)) (lt_add_one _)
  exact ArithmeticCarrier94Soundness.ordinary_halts _ hpos
    (ArithmeticCarrier94Extraction.current94_equations _ hpos hz')

/-- **Completeness.** A natural zero of the maintained equation gives one of the 67/94
equation, by `i ↦ Delta i`. -/
theorem zero94_of_zero (v : Fin 14 → V)
    (hz : InternalZero ObjectCurrentEquation2011.naturalExpression v) :
    ∃ w : Fin 14 → V, InternalZero naturalExpression94 w := by
  have hz' : InternalZero ObjectCurrentEquation2011.expression (fun j => v j + 1) :=
    (ObjectCurrentEquation2011.internalZero_positiveShift _ v).mp hz
  rw [internalZero_iff, ObjectCurrentEquation2011.expression,
    FreshModel106.evalRing_expressionAt65] at hz'
  let P : Fin 4 → DiffRing V := fun j => ((CurrentWindowCarry2011.ports j : ℤ) : DiffRing V)
  let u : Fin 14 → DiffRing V := fun j => ι (v j + 1)
  have h94 := Carrier94Value.zero94_of_maintained model_discrete mod4 P u
    FreshModel106.beta_pos (FreshModel106.shifted_pos v) hz'
  have hm := Carrier94Value.multiplier_pos model_discrete P u
    FreshModel106.beta_pos (FreshModel106.shifted_pos v)
  obtain ⟨m, hm'⟩ := nonneg_iff.mp hm.le
  have hm0 : 0 < m := by
    rw [← ι_lt_ι, map_zero, ← hm']
    exact hm
  refine ⟨fun j => if j = 5 then m - 1 else v j, ?_⟩
  apply (ObjectCurrentEquation2011.internalZero_positiveShift _ _).mpr
  show InternalZero expression94 _
  rw [internalZero_iff, expression94, Carrier94Value.evalRing_expressionAt94]
  convert h94 using 2
  funext j
  by_cases hj : j = 5
  · subst hj
    simp only [Function.update_apply, ↓reduceIte]
    rw [tsub_add_cancel_of_le (pos_iff_one_le.mp hm0), hm']
  · simp only [Function.update_apply, hj, ↓reduceIte]
    rfl

end Model

/-- Fresh-base model bridge, without a separate no-zero bridge provider. -/
theorem bridge94 : HAExpressionAssembly.PolynomialBridge naturalExpression94 := by
  intro V _ _
  have eqv : (FoundationHANoZero.classicalNoZero naturalExpression94).Evalb (M := V) ![] ↔
      (FoundationHANoZero.classicalNoZero ObjectCurrentEquation2011.naturalExpression).Evalb (M := V) ![] := by
    rw [HAExpressionAssembly.classicalNoZero_iff, HAExpressionAssembly.classicalNoZero_iff]
    constructor
    · intro h v hz
      obtain ⟨w,hw⟩ := zero94_of_zero v hz
      exact h w hw
    · intro h w hz
      obtain ⟨t,ht⟩ := halts_of_zero94 w hz
      have hno : (FoundationHANoZero.classicalNoZero
          ObjectCurrentEquation2011.naturalExpression).Evalb (M := V) ![] := by
        rw [HAExpressionAssembly.classicalNoZero_iff]
        exact h
      exact ((HACurrentEquation2011.polynomialBridge V).mp hno) ⟨t,ht⟩
  exact eqv.trans (HACurrentEquation2011.polynomialBridge V)

theorem native_equivalence94 : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero naturalExpression94 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ bridge94

theorem standard_equivalence94 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero naturalExpression94 🡘
      ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalence94

#print axioms halts_of_zero94
#print axioms zero94_of_zero
#print axioms bridge94
#print axioms standard_equivalence94

end DiophantineConsistency.FreshCarrier94
