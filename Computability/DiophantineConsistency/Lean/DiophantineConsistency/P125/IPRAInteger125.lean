import DiophantineConsistency.ZRows.IntegerDomain
import DiophantineConsistency.P125.P125SyntaxDirect
import DiophantineConsistency.P125.P125SyntaxCentered
import DiophantineConsistency.P125.P125Fold
import DiophantineConsistency.P125.P125Complete

/-! # iPRA endpoints for package 125's eleven-integer three-root equations 488/118, 464/119

The equations are the JSON DAGs below
`con-zfc-diophantine-forms/125-unified-binomial-round15/norm/`:

* `integral_direct_paired.json`: eleven unknowns over ℤ, exact degree 488, 118 operations
  (74 `mul`, 23 `add`, 21 `sub`), `P125SyntaxDirect.literal`;
* `integral_centered_paired.json`: eleven unknowns over ℤ, exact degree 464, 119 operations
  (74 `mul`, 24 `add`, 21 `sub`), `P125SyntaxCentered.literal`;

in the unknowns `j C z h r v w T c n s`, each read at the six fixed integers
`beta K0 MC MF cone_A cone_B` of the source34 tuple (`P138Ports.ports6`:
`Source34Ports.ports 0 … 3`, then `2^1113` and `2^666104`). Their front is the front of package
138's native form (index `k = R + 1 + h X Y`); their back end is the three-root norm of
`P125Value`,

  `N(Z; A, B, G) = ((Z² + A − B − G)² − 4 (A Z² + B G))² − 64 (A Z²) (B G)`,

with the radicands `A = 9 S² Df`, `B = S² δ Cy`, `G = S² Dt (81 + (243 Budget − 324) Dt s²)`,
which vanishes exactly when `Z` is a signed sum of square roots of the three radicands, so the
three square conditions `Df = □`, `δ Cy = □`, `Dt Dg = □` are fused into one equation. The two
forms differ only in the linear slot: `Z = S n − Ac` (direct) and `Z = S (n + Q V) − Ac`
(centered; the shear `n ↦ n − Q V` lowers the degree from 488 to 464 at the cost of one
addition).

For each equation, in its own namespace `Form<degree>`:

* `bridge`: in every model `V` of `𝗜𝚺₁`, the polynomial has a zero in the ring of differences
  `DiffRing V` iff machine 215 halts internally, from
  * `P125Fold.sound_direct`, `P125Fold.sound_centered` (soundness: the three squares are
    recovered from a zero by `ZRowsThreeRoot`, the strong fold `ZRowsStrongFold.strong_fold`
    gives `P138Rank.Folded`, and `P138Leaf.halt_of_folded` gives the halt);
  * `P125Complete.complete_direct`, `P125Complete.complete_centered` (completeness: the
    canonical record of package 138, the guard Pell pair of package 137, the supported-modulus
    interpolation of this back end, and a root of `(t² + 3)(t³ − 19)` modulo `2 s r`);
  * `literal_zero_iff` of the syntax module, identifying the literal's zeros with those of
    `P125Value.valueD`, `P125Value.valueC`;
* `native_equivalence`: the native iPRA theory proves `nativeNoZero (signedSplit expression)`
  (no natural zero of the 22-unknown split form in which each integer unknown is written as
  `aᵢ − bᵢ`, i.e. no integer zero of the equation) equivalent to
  `∼mappedNativeRefutation embedding`, the selected Foundation ZFC consistency predicate, which
  is the native rendering of "machine 215 does not halt" and so of Con(ZFC);
* `standard_equivalence`: the same in the standard iPRA theory;
* `reference_equivalence`: the order-erased form of the same equivalence in the equality-only
  reference theory.

These endpoints are about the Lean syntax trees. Their correspondence with the JSONs (pinned
SHA-256, node-by-node regeneration, mutation controls) is the finite check
`research/p125-integer11/tools/gen_literal125.py --check`, and the binding of the six ports to
the pinned coefficient payloads is `research/p125-integer11/tools/check_ports125.py`. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAInteger125
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open IntegerDomain (IntegerModelBridge signedSplit native_of_integer standard_of_integer
  reference_of_integer)
open P138Ports (ports6)

namespace Form488

/-- Package 125's 488/118 polynomial: the direct three-root literal at the six source34
ports. -/
def expression : Expr (Fin 11) := P125SyntaxDirect.literal (fun i => (ports6 i : ℤ))

/-- In every model of `𝗜𝚺₁`, an integer zero exists iff machine 215 halts. -/
theorem bridge : IntegerModelBridge expression := fun _ _ _ =>
  ⟨fun ⟨x, hx⟩ => P125Fold.sound_direct x ((P125SyntaxDirect.literal_zero_iff x).1 hx),
   fun ⟨T, hT⟩ =>
    let ⟨x, hx⟩ := P125Complete.complete_direct T hT
    ⟨x, (P125SyntaxDirect.literal_zero_iff x).2 hx⟩⟩

/-- **Native iPRA proves: package 125's 488/118 equation has no integer zero iff ZFC is
consistent.** -/
theorem native_equivalence : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (signedSplit expression) 🡘
      ∼mappedNativeRefutation embedding :=
  native_of_integer _ bridge

/-- The same equivalence in standard iPRA. -/
theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (signedSplit expression) 🡘
      ∼mappedNativeRefutation embedding :=
  standard_of_integer _ bridge

/-- The same equivalence in equality-only iPRA, after order erasure. -/
theorem reference_equivalence : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero (signedSplit expression)) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  reference_of_integer _ bridge

#print axioms bridge
#print axioms native_equivalence
#print axioms standard_equivalence
#print axioms reference_equivalence

end Form488

namespace Form464

/-- Package 125's 464/119 polynomial: the centered three-root literal at the six source34
ports. -/
def expression : Expr (Fin 11) := P125SyntaxCentered.literal (fun i => (ports6 i : ℤ))

/-- In every model of `𝗜𝚺₁`, an integer zero exists iff machine 215 halts. -/
theorem bridge : IntegerModelBridge expression := fun _ _ _ =>
  ⟨fun ⟨x, hx⟩ => P125Fold.sound_centered x ((P125SyntaxCentered.literal_zero_iff x).1 hx),
   fun ⟨T, hT⟩ =>
    let ⟨x, hx⟩ := P125Complete.complete_centered T hT
    ⟨x, (P125SyntaxCentered.literal_zero_iff x).2 hx⟩⟩

/-- **Native iPRA proves: package 125's 464/119 equation has no integer zero iff ZFC is
consistent.** -/
theorem native_equivalence : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (signedSplit expression) 🡘
      ∼mappedNativeRefutation embedding :=
  native_of_integer _ bridge

/-- The same equivalence in standard iPRA. -/
theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (signedSplit expression) 🡘
      ∼mappedNativeRefutation embedding :=
  standard_of_integer _ bridge

/-- The same equivalence in equality-only iPRA, after order erasure. -/
theorem reference_equivalence : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero (signedSplit expression)) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  reference_of_integer _ bridge

#print axioms bridge
#print axioms native_equivalence
#print axioms standard_equivalence
#print axioms reference_equivalence

end Form464

end DiophantineConsistency.IPRAInteger125
