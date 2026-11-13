import DiophantineConsistency.ModelCarrierCurrent
import DiophantineConsistency.Bm2963.IPRACarrier65Bm2963

/-! # iPRA endpoints for package 188's scaled 14/66/118 companion

Package 188's `native/q66_d118.json` (14 positive unknowns, 66 operations, exact
degree 118) is `ModelCarrierCurrent.expressionAt118 p` at the block-mask2963 ports
`p = fun j => (Bm2963Ports.ports j : ℤ)`. This is the counterpart of the 2011-port
endpoint in `ModelCarrierCurrent`:

* in every model of `𝗜𝚺₁` its positive zeros are exactly those of the Carrier65
  polynomial at the same ports, by the port-generic ring theorem
  `ModelCarrierScaled.zero_iff118` in the model's ring of differences;
* the Carrier65 bridge is the closed block-mask2963 calibration
  `IPRACarrier65Bm2963.positiveBridge`, via `IPRAOrdinary12.bridge_of_positive`.

Only the port-dependent part of `ModelCarrierCurrent` is restated (`beta_pos`,
`sameZero118`, the bridges and the endpoints). The binding of the Lean syntax to the
JSON (AC-normal form, signed sums, modular evaluation at the actual ports, 66/66
single-gate mutations) is the finite check
`research/block-mask2963-calibration/tools/check_forms.py`. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiophantineConsistency.Bm2963Carrier118
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing DiscreteOrderedRingFacts ModelArithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open ModelCarrierCurrent (expressionAt118 evalRing_expressionAt118 evalRing_expressionAt65
  shifted_pos)
attribute [local irreducible] Bm2963Ports.ports Bm2963Kernel.K Bm2963MaskData.radix
  Bm2963MaskData.beta Bm2963MaskData.lowPort Bm2963MaskData.highPort

/-- The block-mask2963 ports as integers. -/
abbrev intPorts : Fin 4 → ℤ := fun j => ((Bm2963Ports.ports j : ℕ) : ℤ)

section Model
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The counterpart of `ModelCarrierCurrent.beta_pos` at the block-mask2963 ports. -/
theorem beta_pos : (0 : DiffRing V) < ((intPorts 0 : ℤ) : DiffRing V) := by
  have h0 : (((Bm2963Ports.ports 0 : ℕ) : ℤ) : DiffRing V) = ι (Bm2963MaskData.beta : V) := by
    rw [Bm2963Ports.ports_zero, Int.cast_natCast, map_natCast]
  show (0 : DiffRing V) < (((Bm2963Ports.ports 0 : ℕ) : ℤ) : DiffRing V)
  rw [h0]
  obtain ⟨hβ, _, _⟩ := Bm2963Ports.current_bounds (V := V)
  exact ι_pos (lt_of_lt_of_le (by norm_num) hβ)

/-- In every model of `𝗜𝚺₁`, the 66/118 form has exactly the Carrier65 zeros. -/
theorem sameZero118 (v : Fin 14 → V) :
    InternalZero (positiveShift (expressionAt118 intPorts)) v ↔
      InternalZero Bm2963Ports.naturalExpression v := by
  change InternalZero (positiveShift (expressionAt118 intPorts)) v ↔
    InternalZero (positiveShift Bm2963Ports.expression) v
  rw [internalZero_positiveShift, internalZero_positiveShift, internalZero_iff, internalZero_iff,
    evalRing_expressionAt118, Bm2963Ports.expression, evalRing_expressionAt65]
  exact ModelCarrierScaled.zero_iff118 model_discrete mod4 _ _ beta_pos (shifted_pos v)

end Model

/-! ### Bridges and iPRA endpoints -/

/-- The Carrier65 bridge at the block-mask2963 ports. -/
theorem currentBridge :
    HAExpressionAssembly.PolynomialBridge Bm2963Ports.naturalExpression :=
  IPRAOrdinary12.bridge_of_positive _ IPRACarrier65Bm2963.positiveBridge

theorem bridge118 : HAExpressionAssembly.PolynomialBridge
    (positiveShift (expressionAt118 intPorts)) :=
  HAExpressionSameZero.bridge _ _ (fun _ _ _ v => sameZero118 v) currentBridge

/-- **Native iPRA: package 188's 66/118 form has no positive zero iff ZFC is
consistent.** -/
theorem native_equivalence118 : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt118 intPorts)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ bridge118

theorem standard_equivalence118 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt118 intPorts)) 🡘
      ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalence118

theorem reference_equivalence118 : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero
      (positiveShift (expressionAt118 intPorts))) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  IPRAReferenceInductionConversion.nativeToReference native_equivalence118

#print axioms sameZero118
#print axioms currentBridge
#print axioms native_equivalence118
#print axioms standard_equivalence118
#print axioms reference_equivalence118

end DiophantineConsistency.Bm2963Carrier118
