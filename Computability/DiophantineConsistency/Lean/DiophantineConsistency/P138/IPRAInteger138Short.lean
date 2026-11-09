import DiophantineConsistency.ZRows.IntegerDomain
import DiophantineConsistency.P138.P138ShortSyntax
import DiophantineConsistency.P138.P138Short

/-! # iPRA endpoints for package 138's eleven-integer, degree-840 equation

The equation is `138-semantic-signs/integer11/parity_saturated11_short.json`: eleven
unrestricted integer unknowns `j C z h r v w T c n s`, 108 operations (67 `mul`, 24 `add`,
17 `sub`) and exact degree 840, at the six fixed integers `beta K0 MC MF cone_A cone_B` of the
source34 tuple (`P138Ports.ports6`: `Source34Ports.ports 0 … 3`, then `2^1113` and `2^666104`).
It is the short form of the native 924/107 equation (`IPRAInteger138`): the index modulus of
`k = R + 1 + h·M_index` is `M_index = 4q⁴` instead of `E`. Its Lean syntax tree is
`P138ShortSyntax.literal`, evaluated at those six integers (`expression`).

`bridge`: in every model `V` of `𝗜𝚺₁`, `expression` has a zero in the ring of differences
`DiffRing V` iff machine 215 halts internally:

* `P138Short.sound` (soundness: the generic soundness chain at the index modulus `4q⁴`, which
  divides `E` and exceeds `3R + 1`; a zero gives the source34 leaf facts, hence a halt, through
  `Source34Converse.halt_iff_facts`);
* `P138Short.complete` (completeness: the native zero of `P138Complete.complete`, with
  `h ↦ h (3w+1)(2v+1)`, by the polynomial identity `P138Value.valueS_update`);
* `P138ShortSyntax.literal_zero_iff` identifies the literal's zeros with those of
  `P138Value.valueS`.

`IntegerDomain` turns this into iPRA statements about `signedSplit expression`, the 22-unknown
natural-number form in which each integer unknown is written as `aᵢ − bᵢ`. Proved here:

* `native_equivalence`: the native iPRA theory proves `nativeNoZero (signedSplit expression)`
  (no natural zero of the split form, i.e. no integer zero of the equation) equivalent to
  `∼mappedNativeRefutation embedding`, the selected Foundation ZFC consistency predicate, which
  is the native rendering of "machine 215 does not halt" and so of Con(ZFC);
* `standard_equivalence`: the same in the standard iPRA theory;
* `reference_equivalence`: the order-erased form of the same equivalence in the
  equality-only reference theory.

These endpoints are about the Lean syntax tree. Its correspondence with the JSON (pinned
SHA-256, node-by-node regeneration, mutation controls) is the finite check
`research/p138-integer11/tools/gen_literal.py --check`, and the binding of the six ports to the
pinned coefficient payloads is `research/p138-integer11/tools/check_ports138.py`; both check the
native and the short JSON. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAInteger138Short
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open IntegerDomain (IntegerModelBridge signedSplit native_of_integer standard_of_integer
  reference_of_integer)
open P138Ports (ports6)

/-- Package 138's 840/108 polynomial: the short literal at the six source34 ports. -/
def expression : Expr (Fin 11) := P138ShortSyntax.literal (fun i => (ports6 i : ℤ))

/-- In every model of `𝗜𝚺₁`, an integer zero exists iff machine 215 halts. -/
theorem bridge : IntegerModelBridge expression := fun _ _ _ =>
  ⟨fun ⟨x, hx⟩ => P138Short.sound x ((P138ShortSyntax.literal_zero_iff x).1 hx),
   fun ⟨T, hT⟩ =>
    let ⟨x, hx⟩ := P138Short.complete T hT
    ⟨x, (P138ShortSyntax.literal_zero_iff x).2 hx⟩⟩

theorem native_equivalence : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (signedSplit expression) 🡘
      ∼mappedNativeRefutation embedding :=
  native_of_integer _ bridge
theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (signedSplit expression) 🡘
      ∼mappedNativeRefutation embedding :=
  standard_of_integer _ bridge
theorem reference_equivalence : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero (signedSplit expression)) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  reference_of_integer _ bridge

#print axioms bridge
#print axioms native_equivalence
#print axioms standard_equivalence
#print axioms reference_equivalence

end DiophantineConsistency.IPRAInteger138Short
