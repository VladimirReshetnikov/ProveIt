import DiophantineConsistency.ZRows.IntegerDomain
import DiophantineConsistency.P172.P172Syntax
import DiophantineConsistency.LinCof.LCLeaf
import DiophantineConsistency.LinCof.LCComplete

/-! # iPRA endpoints for package 172's eleven-integer, degree-298 equation

The equation is
`172-pooled-powers-round21/part2/ConZFC_Pooled_Powers_Round21_2026-10-25/scalar/integer11/integer11_degree298_ops146.json`:
eleven unrestricted integer unknowns `j C z h r v w T c n s`, 146 operations (94 `mul`,
29 `add`, 23 `sub`) and exact degree 298, at the six fixed integers
`beta K0 MC MF cone_A cone_B` of the source34 tuple (`P138Ports.ports6`). Its Lean syntax tree is
`P172Syntax.literal`, evaluated at those six integers (`expression`).
It is the lowest-degree point of the eleven-integer row.

It is a linear-cofactor circuit (`LinCof`, `LCValue.value298`): radical weight `1024`, index
slots `k298 / kq298 / L298` (slot law of exponent 0), centre `psi298`.

`bridge`: in every model `V` of `𝗜𝚺₁`, `expression` has a zero in the ring of differences
`DiffRing V` iff machine 215 halts internally:

* `LCLeaf.sound298` (soundness: a zero gives the source34 leaf facts, hence a halt, through
  `Source34Converse.halt_iff_facts`);
* `LCComplete.complete298` (completeness: canonical data, guard Pell pair, supported-modulus
  interpolation, intersective root of `(t² + 3)(t³ − 19)`, two-radical assembly);
* `P172Syntax.literal_zero_iff` identifies the literal's zeros with those of `LCValue.value298`.

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
`research/p172-integer11/tools/gen_literal172.py --check`, and the binding of the six ports to
the pinned coefficient payloads is `research/p172-integer11/tools/check_ports172.py`. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAInteger172
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open IntegerDomain (IntegerModelBridge signedSplit native_of_integer standard_of_integer
  reference_of_integer)
open P138Ports (ports6)

/-- Package 172's 298/146 polynomial: the literal at the six source34 ports. -/
def expression : Expr (Fin 11) := P172Syntax.literal (fun i => (ports6 i : ℤ))

/-- In every model of `𝗜𝚺₁`, an integer zero exists iff machine 215 halts. -/
theorem bridge : IntegerModelBridge expression := fun _ _ _ =>
  ⟨fun ⟨x, hx⟩ => LCLeaf.sound298 x ((P172Syntax.literal_zero_iff x).1 hx),
   fun ⟨T, hT⟩ =>
    let ⟨x, hx⟩ := LCComplete.complete298 T hT
    ⟨x, (P172Syntax.literal_zero_iff x).2 hx⟩⟩

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

end DiophantineConsistency.IPRAInteger172
