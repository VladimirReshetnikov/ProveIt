import DiophantineConsistency.Compact44.IPRAOrdinary12Chain
import DiophantineConsistency.Compact44.P57Facts
import DiophantineConsistency.Compact44.P57Converse

/-! # iPRA endpoints for package 57's 12-positive, degree-258 equation

The equation is `57-separated-degrees/low_degree/twelve_positive_degree258.json`:
12 positive unknowns, 89 operations and exact degree 258, at the compact44
ports `CompactSymbolicPortProjections.portsInt (paramKernel rho)`. In every
model of `𝗜𝚺₁` it has a positive zero iff machine 215 halts:

* `P57Facts.halts` gives the forward direction, through the product-unit
  guard, the fused four-root carrier and strong/auxiliary restorations, the
  early congruence modulo `4q⁴`, the ordinary-blank signed index theorem (in
  both signs) and the six compact44 leaf facts;
* `P57Converse.converse` gives the converse, from the canonical halt data.

The generic helpers of `IPRAOrdinary12Chain` turn this into native, standard
and equality-only iPRA equivalences with the selected Foundation ZFC
consistency predicate. The endpoints are about the Lean graph; its
correspondence with the JSON is the check
`research/twelve-p57-endpoint/tools/generate_p57.py --check`. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAPositive57
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open IPRAOrdinary12 (PositiveModelBridge)
open IPRAOrdinary12Chain (native_of_positive standard_of_positive reference_of_positive)
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
attribute [local irreducible] paramKernel rho CompactFixedBeta.betaNat lowNat highNat

def expression : Expr (Fin 12) :=
  (P57Graph.graph (CompactSymbolicPortProjections.portsInt (paramKernel rho))).output

/-- In every model of `𝗜𝚺₁`, a positive zero exists iff machine 215 halts. -/
theorem positiveBridge : PositiveModelBridge expression := fun _ _ _ =>
  ⟨fun ⟨v, hv, hz⟩ => P57Facts.halts v hv hz, fun ⟨T, hT⟩ => P57Converse.converse T hT⟩

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

end DiophantineConsistency.IPRAPositive57
