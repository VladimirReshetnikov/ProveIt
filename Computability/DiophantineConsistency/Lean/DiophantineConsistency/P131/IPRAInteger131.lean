import DiophantineConsistency.ZRows.IntegerDomain
import DiophantineConsistency.P131.P131Syntax
import DiophantineConsistency.P131.P131Fold
import DiophantineConsistency.P131.P131Complete

/-! # iPRA endpoints for package 131's eleven-integer, degree-810 two-root equation

The equation is `131-shared-pell-caps-round16/scalar/two_root/two_root11_degree810.json`:
eleven unrestricted integer unknowns `j C z h r v w T c n s`, 112 operations (70 `mul`,
22 `add`, 20 `sub`) and exact degree 810, at the six fixed integers
`beta K0 MC MF cone_A cone_B` of the source34 tuple (`P138Ports.ports6`:
`Source34Ports.ports 0 … 3`, then `2^1113` and `2^666104`). Its front is the front of package
138's short form (index modulus `4q⁴`); its back end is the two-root norm
`Inner² − 4 δ · Aux · Guard` of `P131Value`, in which the strong ordinate is `U = r c²`, the
linear slot reads the strong root (`Z = S (n + V) − Ac`), and the two square conditions
`P · Df = □` and `δ · Cy = □` are fused into one equation. Its Lean syntax tree is
`P131Syntax.literal`, evaluated at those six integers (`expression`).

`bridge`: in every model `V` of `𝗜𝚺₁`, `expression` has a zero in the ring of differences
`DiffRing V` iff machine 215 halts internally:

* `P131Fold.sound` (soundness: both squares are recovered from a zero, the strong fold
  `ZRowsStrongFold.strong_fold` gives `P138Rank.Folded`, and `P138Leaf.halt_of_folded` gives the
  halt);
* `P131Complete.complete` (completeness: the canonical record and the guard Pell pair of package
  138, the supported-modulus interpolation of this back end, and `h ↦ h (3w+1)(2v+1)` by the
  polynomial identity `P131Complete.value_update`);
* `P131Syntax.literal_zero_iff` identifies the literal's zeros with those of `P131Value.value`.

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
`research/p131-integer11/tools/gen_literal131.py --check`, and the binding of the six ports to
the pinned coefficient payloads is `research/p131-integer11/tools/check_ports131.py`. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAInteger131
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open IntegerDomain (IntegerModelBridge signedSplit native_of_integer standard_of_integer
  reference_of_integer)
open P138Ports (ports6)

/-- Package 131's 810/112 polynomial: the two-root literal at the six source34 ports. -/
def expression : Expr (Fin 11) := P131Syntax.literal (fun i => (ports6 i : ℤ))

/-- In every model of `𝗜𝚺₁`, an integer zero exists iff machine 215 halts. -/
theorem bridge : IntegerModelBridge expression := fun _ _ _ =>
  ⟨fun ⟨x, hx⟩ => P131Fold.sound x ((P131Syntax.literal_zero_iff x).1 hx),
   fun ⟨T, hT⟩ =>
    let ⟨x, hx⟩ := P131Complete.complete T hT
    ⟨x, (P131Syntax.literal_zero_iff x).2 hx⟩⟩

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

end DiophantineConsistency.IPRAInteger131
