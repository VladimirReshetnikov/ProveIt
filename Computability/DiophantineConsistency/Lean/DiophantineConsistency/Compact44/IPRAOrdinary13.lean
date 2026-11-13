import DiophantineConsistency.Compact44.IPRAOrdinary12Chain
import DiophantineConsistency.Compact44.FreeJ13Halt

/-! # iPRA endpoints for the 13-positive, 87-operation free-J graph

Package 115's `positive13_87_degree51` circuit has 13 positive inputs,
87 operations and exact degree 51, at the compact44 ports
`CompactSymbolicModelIff.p`. `FreeJ13Halt.positive_model_iff` proves, in every
model of `𝗜𝚺₁`, that the graph has a positive zero iff machine 215 halts.
The generic helpers of `IPRAOrdinary12Chain` turn that into native, standard
and equality-only iPRA equivalences with the selected Foundation ZFC
consistency predicate. These endpoints are about the Lean graph. Its
correspondence with the JSON circuit is the check
`research/ordinary13-freej87-endpoint/generate_graph.py --check`. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAOrdinary13
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open IPRAOrdinary12 (PositiveModelBridge)
open IPRAOrdinary12Chain (native_of_positive standard_of_positive reference_of_positive)

def expression : Expr (Fin 13) := (FreeJ13.graph CompactSymbolicModelIff.p).output

theorem positiveBridge : PositiveModelBridge expression :=
  fun V _ _ => FreeJ13Halt.positive_model_iff (V := V)

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

#print axioms native_equivalence
#print axioms standard_equivalence
#print axioms reference_equivalence

end DiophantineConsistency.IPRAOrdinary13
