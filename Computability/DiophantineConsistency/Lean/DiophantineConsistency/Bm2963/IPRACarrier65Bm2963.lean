import DiophantineConsistency.Compact44.IPRAOrdinary12Chain
import DiophantineConsistency.Bm2963.Bm2963Soundness
import DiophantineConsistency.Bm2963.Bm2963Construction

/-! # iPRA endpoints for the Carrier65 polynomial at the block-mask2963 ports

The Carrier65 polynomial `ObjectCurrentEquation2011.expressionAt` (14 positive
unknowns, 65 operations, exact degree 150) at the block-mask2963 ports
`Bm2963Ports.ports` is package 188's "immediate control" and the intermediate for
both of its companions (`Bm2963Carrier118`, `Bm2963Carrier94`). In every model of `𝗜𝚺₁` it has a positive zero iff
machine 215 halts:

* `Bm2963Soundness.zero_halts` gives the forward direction (window, cell
  decoding, `ArithmeticWangSoundness.marked_halts`);
* `Bm2963Construction.halt_positive_zero_closed` gives the converse (controller,
  unit, packing under the proved Local Normalization Lemma).

The generic helpers of `IPRAOrdinary12Chain` turn this into native, standard
and equality-only iPRA equivalences with the selected Foundation ZFC
consistency predicate. The endpoints are about the Lean syntax tree. Its
ports are bound to the block-mask2963 payloads by the finite check
`research/block-mask2963-calibration/tools/check_recipe.py`. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRACarrier65Bm2963
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open IPRAOrdinary12 (PositiveModelBridge)
open IPRAOrdinary12Chain (native_of_positive standard_of_positive reference_of_positive)
attribute [local irreducible] Bm2963Ports.ports Bm2963Kernel.K Bm2963MaskData.radix
  Bm2963MaskData.beta Bm2963MaskData.lowPort Bm2963MaskData.highPort

/-- Carrier65 at the block-mask2963 ports. -/
def expression : Expr (Fin 14) := Bm2963Ports.expression

/-- In every model of `𝗜𝚺₁`, a positive zero exists iff machine 215 halts. -/
theorem positiveBridge : PositiveModelBridge expression := fun _ _ _ =>
  ⟨fun ⟨v, hv, hz⟩ => Bm2963Soundness.zero_halts v ⟨hv, hz⟩,
   fun ⟨T, hT⟩ => Bm2963Construction.halt_positive_zero_closed T hT⟩

theorem native_equivalence : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift expression) 🡘
      ∼mappedNativeRefutation embedding :=
  native_of_positive _ positiveBridge
theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift expression) 🡘
      ∼mappedNativeRefutation embedding :=
  standard_of_positive _ positiveBridge
theorem reference_equivalence : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero (positiveShift expression)) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  reference_of_positive _ positiveBridge

#print axioms positiveBridge
#print axioms native_equivalence
#print axioms standard_equivalence
#print axioms reference_equivalence

end DiophantineConsistency.IPRACarrier65Bm2963
