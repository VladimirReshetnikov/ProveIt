import DiophantineConsistency.ZRows.IntegerDomain
import DiophantineConsistency.P135W.P135WSyntax
import DiophantineConsistency.P135W.P135WFold
import DiophantineConsistency.P135W.P135WComplete

/-! # iPRA endpoints for package 135's eleven-integer, degree-398 weak cofactor equation

The equation is `135-cofinal-anchors-round17/scalar/weak_cofactor11_none.json`:
eleven unrestricted integer unknowns `j C z h r v w T c n s`, 121 operations (77 `mul`,
24 `add`, 20 `sub`) and exact degree 398, at the six fixed integers
`beta K0 MC MF cone_A cone_B` of the source34 tuple (`P138Ports.ports6`:
`Source34Ports.ports 0 … 3`, then `2^1113` and `2^666104`). Its front and carrier are, node for
node, the weak front of `P137Front`: the scale is read as `Y = v q` instead of package 138's
`(2v + 1) q³`, and the carrier `zc = Dcar T + M K + H (v − q²)` with `M = 2q²` restores the old
scale, because a zero forces `v = (1 + 2v') q²`. Its back end is the linear-cofactor norm form
of `P135WValue`: with `B = A r Dm`, `Df = 1 + Δ c⁴ B`, `Q = Δ² c⁴ B`, `δ = Q − 1` and the guard
`P = Dt (1 + (Budget − 4) Dt s²)`, the output is
`(δ Z² + δ S² P − 4 S² B Df Cy)² − 4 (δ Z²)(δ S² P)`. Its Lean syntax tree is
`P135WSyntax.literal`, evaluated at those six integers (`expression`).

`bridge`: in every model `V` of `𝗜𝚺₁`, `expression` has a zero in the ring of differences
`DiffRing V` iff machine 215 halts internally:

* `P135WFold.sound` (soundness: `S ≠ 0` and `S ∣ Ac` at every zero, the norm form gives
  `P = g²` and `w² = B Df (δ Cy)`, the three pairwise coprime factors `B`, `Df`, `δ Cy` are
  squares by `P135WRoots`, the scale is recovered, the strong fold
  `ZRowsStrongFold.strong_fold` gives `P138Rank.Folded`, and `P138Leaf.halt_of_folded` gives the
  halt);
* `P135WComplete.complete` (completeness: the canonical record of package 138 at the scale
  `v = (1 + 2v') q²`, the guard Pell pair of `P138Guard.guard` for the discriminant
  `Budget − 4`, the supported-modulus quartic interpolation for the linear cofactor, and a root
  of `(t² + 3)(t³ − 19)`);
* `P135WSyntax.literal_zero_iff` identifies the literal's zeros with those of
  `P135WValue.value`.

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
`research/p135w-integer11/tools/gen_literal135w.py --check`, and the binding of the six ports
to the pinned coefficient payloads is `research/p135w-integer11/tools/check_ports135w.py`. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAInteger135W
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open IntegerDomain (IntegerModelBridge signedSplit native_of_integer standard_of_integer
  reference_of_integer)
open P138Ports (ports6)

/-- Package 135's 398/121 polynomial: the weak cofactor literal at the six source34 ports. -/
def expression : Expr (Fin 11) := P135WSyntax.literal (fun i => (ports6 i : ℤ))

/-- In every model of `𝗜𝚺₁`, an integer zero exists iff machine 215 halts. -/
theorem bridge : IntegerModelBridge expression := fun _ _ _ =>
  ⟨fun ⟨x, hx⟩ => P135WFold.sound x ((P135WSyntax.literal_zero_iff x).1 hx),
   fun ⟨T, hT⟩ =>
    let ⟨x, hx⟩ := P135WComplete.complete T hT
    ⟨x, (P135WSyntax.literal_zero_iff x).2 hx⟩⟩

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

end DiophantineConsistency.IPRAInteger135W
