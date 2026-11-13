import DiophantineConsistency.Compact44.IPRAOrdinary12Chain
import DiophantineConsistency.Compact44.P64Facts
import DiophantineConsistency.Compact44.P64Converse

/-! # iPRA endpoints for package 64's 14-positive, degree-30 equation

The equation is `64-structural-reductions/positive14/polynomial.json`: 14
positive unknowns, 83 operations and exact degree 30, at the compact44 ports
`CompactSymbolicPortProjections.portsInt (paramKernel rho)`. In every model of
`𝗜𝚺₁` it has a positive zero iff machine 215 halts:

* `P64Facts.halts` gives the forward direction, through the six compact44 leaf
  facts and `CompactLeafFactsHalt.halts_of_facts`;
* `P64Converse.converse` gives the converse, from the canonical halt data.

The generic helpers of `IPRAOrdinary12Chain` turn this into native, standard
and equality-only iPRA equivalences with the selected Foundation ZFC
consistency predicate. The endpoints are about the Lean graph; its
correspondence with the JSON is the check
`research/fourteen-p64-endpoint/tools/generate_p64.py --check`. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAPositive64
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open IPRAOrdinary12 (PositiveModelBridge)
open IPRAOrdinary12Chain (native_of_positive standard_of_positive reference_of_positive)
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
attribute [local irreducible] paramKernel rho CompactFixedBeta.betaNat lowNat highNat

def expression : Expr (Fin 14) :=
  (P64Graph.graph (CompactSymbolicPortProjections.portsInt (paramKernel rho))).output

/-- In every model of `𝗜𝚺₁`, a positive zero exists iff machine 215 halts. -/
theorem positiveBridge : PositiveModelBridge expression := fun _ _ _ =>
  ⟨fun ⟨v, hv, hz⟩ => P64Facts.halts v hv hz, fun ⟨T, hT⟩ => P64Converse.converse T hT⟩

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

end DiophantineConsistency.IPRAPositive64
