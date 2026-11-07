import DiophantineConsistency.Compact44.IPRAOrdinary12Chain
import DiophantineConsistency.Mixed121.P55Facts
import DiophantineConsistency.Mixed121.P55Converse

/-! # iPRA endpoints for package 55's 14-positive, degree-52 equation

The equation is `55-congruence-norms/fourteen/polynomial.json`: 14 positive
unknowns, 79 operations and exact degree 52, at the wang943-mixed-121x8801
ports `Mixed121Ports.ports` (package 31's payloads). In every model of `𝗜𝚺₁`
it has a positive zero iff machine 215 halts:

* `P55Facts.halts` gives the forward direction, through the six leaf facts and
  the 121x8801 halting chain (`Mixed121Halt.halts_of_facts`);
* `P55Converse.converse` gives the converse, from the canonical 121x8801 halt
  data (`Mixed121Seeds.halt_first_gamma`).

The generic helpers of `IPRAOrdinary12Chain` turn this into native, standard
and equality-only iPRA equivalences with the selected Foundation ZFC
consistency predicate. The endpoints are about the Lean graph; its
correspondence with the JSON is the check
`research/mixed121-calibration/tools/generate_p55.py --check`. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAPositive55
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open IPRAOrdinary12 (PositiveModelBridge)
open IPRAOrdinary12Chain (native_of_positive standard_of_positive reference_of_positive)
attribute [local irreducible] Mixed121Ports.ports

def expression : Expr (Fin 14) :=
  (P55Graph.graph (fun j => (Mixed121Ports.ports j : ℤ))).output

/-- In every model of `𝗜𝚺₁`, a positive zero exists iff machine 215 halts. -/
theorem positiveBridge : PositiveModelBridge expression := fun _ _ _ =>
  ⟨fun ⟨v, hv, hz⟩ => P55Facts.halts v hv hz, fun ⟨T, hT⟩ => P55Converse.converse T hT⟩

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

end DiophantineConsistency.IPRAPositive55
