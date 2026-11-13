import DiophantineConsistency.ZRows.IntegerDomain
import DiophantineConsistency.P113.P113Syntax
import DiophantineConsistency.P113.P113Leaf
import DiophantineConsistency.P113.P113Complete

/-! # iPRA endpoints for package 113's twelve-integer, degree-1084 equation

The equation is `113-saturated-pell/integer12_saturated/rational.json`: twelve unrestricted
integer unknowns `j C z h r v w T c n t s`, 123 operations (75 `mul`, 25 `add`, 23 `sub`) and
exact degree 1084, at the six fixed integers `beta K0 MC MF cone_A cone_B` of the source34 tuple,
which are package 138's (`P138Ports.ports6`). Its Lean syntax tree is `P113Syntax.literal`,
evaluated at those six integers (`expression`).

`bridge`: in every model `V` of `𝗜𝚺₁`, `expression` has a zero in the ring of differences
`DiffRing V` iff machine 215 halts internally:

* `P113Leaf.sound` (soundness: a zero gives package 138's folded front on the weak window,
  `P113Fold`, and package 138's chain re-run over it, `P113Chain`, gives the source34 leaf facts,
  hence a halt through `Source34Converse.halt_iff_facts`);
* `P113Complete.complete` (completeness: canonical data with the strict cones, the joint
  positivity and guard Pell witnesses, the supported-modulus interpolation with `E = τ²` folded
  into the strong register, the intersective root of `(t² + 3)(t³ − 19)`, assembly);
* `literal_zero_iff` identifies the literal's zeros with those of `P113Value.value portsR`.

`IntegerDomain` turns this into iPRA statements about `signedSplit expression`, the 24-unknown
natural-number form in which each integer unknown is written as `aᵢ − bᵢ`:

* `native_equivalence`: the native iPRA theory proves `nativeNoZero (signedSplit expression)`
  equivalent to `∼mappedNativeRefutation embedding`, the native rendering of "machine 215 does
  not halt" and so of Con(ZFC);
* `standard_equivalence`: the same in the standard iPRA theory;
* `reference_equivalence`: the order-erased form in the equality-only reference theory.

These endpoints are about the Lean syntax tree. Its correspondence with the JSON (pinned SHA-256,
numeric model, byte-identical regeneration) is `research/p113-integer12/tools/gen_literal113.py
--check`; the binding of the six coefficients to package 138's pinned payloads is
`research/p113-integer12/tools/check_ports113.py`, and of those payloads to `ports6`,
`research/p138-integer11/tools/check_ports138.py`. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAInteger113
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open IntegerDomain (IntegerModelBridge signedSplit native_of_integer standard_of_integer
  reference_of_integer)
open ModelDifferenceRing P138Ports

/-- Package 113's 1084/123 polynomial: the literal at the six source34 ports. -/
def expression : Expr (Fin 12) := P113Syntax.literal (fun i => (ports6 i : ℤ))

section Model
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- At the six fixed ports, zeros of the literal in `DiffRing V` are zeros of
`P113Value.value portsR`. -/
theorem literal_zero_iff (x : Fin 12 → DiffRing V) :
    expression.evalRing x = 0 ↔ P113Value.value portsR x = 0 := by
  unfold expression
  rw [P113Syntax.evalRing_literal]
  rfl

end Model

/-- In every model of `𝗜𝚺₁`, an integer zero exists iff machine 215 halts. -/
theorem bridge : IntegerModelBridge expression := fun _ _ _ =>
  ⟨fun ⟨x, hx⟩ => P113Leaf.sound x ((literal_zero_iff x).1 hx),
   fun ⟨T, hT⟩ =>
    let ⟨x, hx⟩ := P113Complete.complete T hT
    ⟨x, (literal_zero_iff x).2 hx⟩⟩

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

#print axioms literal_zero_iff
#print axioms bridge
#print axioms native_equivalence
#print axioms standard_equivalence
#print axioms reference_equivalence

end DiophantineConsistency.IPRAInteger113
