import DiophantineConsistency.Compact44.IPRAOrdinary12Chain
import DiophantineConsistency.Adm942.Adm942Soundness
import DiophantineConsistency.Adm942.Adm942Construction

/-! # iPRA endpoints for package 183's 14-positive, degree-150 equation

The equation is `183-pell-carrier65/equation/carrier65.json`: 14 positive
unknowns, 65 operations and exact degree 150. It is the Carrier65 polynomial
`ObjectCurrentEquation2011.expressionAt` at the admissible942 ports
`Adm942Ports.ports`. In every model of `𝗜𝚺₁` it has a positive zero iff
machine 215 halts:

* `Adm942Soundness.zero_halts` gives the forward direction (window, cell
  decoding, `ArithmeticWangSoundness.marked_halts`);
* `Adm942Construction.halt_positive_zero_closed` gives the converse (controller,
  unit, packing under the proved Local Normalization Lemma).

The generic helpers of `IPRAOrdinary12Chain` turn this into native, standard
and equality-only iPRA equivalences with the selected Foundation ZFC
consistency predicate. The endpoints are about the Lean syntax tree. Its
correspondence with the JSON (gate-identical modulo AC, pinned SHA-256, coefficient
files equal to the admissible942 payloads) is the finite check
`research/admissible942-calibration/tools/check_forms.py`. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRACarrier65Adm942
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open IPRAOrdinary12 (PositiveModelBridge)
open IPRAOrdinary12Chain (native_of_positive standard_of_positive reference_of_positive)
attribute [local irreducible] Adm942Ports.ports Adm942Kernel.K Adm942MaskData.radix
  Adm942MaskData.beta Adm942MaskData.lowPort Adm942MaskData.highPort

/-- Package 183's polynomial: Carrier65 at the admissible942 ports. -/
def expression : Expr (Fin 14) := Adm942Ports.expression

/-- In every model of `𝗜𝚺₁`, a positive zero exists iff machine 215 halts. -/
theorem positiveBridge : PositiveModelBridge expression := fun _ _ _ =>
  ⟨fun ⟨v, hv, hz⟩ => Adm942Soundness.zero_halts v ⟨hv, hz⟩,
   fun ⟨T, hT⟩ => Adm942Construction.halt_positive_zero_closed T hT⟩

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

end DiophantineConsistency.IPRACarrier65Adm942
