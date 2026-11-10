import DiophantineConsistency.ZRows.IntegerDomain
import DiophantineConsistency.P135.P135Syntax352
import DiophantineConsistency.P135.P135Syntax340
import DiophantineConsistency.P135.P135Syntax328
import DiophantineConsistency.LinCof.LCFamily

/-! # iPRA endpoints for package 135's eleven-integer equations 352/125, 340/129, 328/130

The equations are the JSON DAGs below `con-zfc-diophantine-forms/135-cofinal-anchors-round17/scalar/`:

* `free_cofactor11_none.json`: eleven unknowns over ℤ, degree 352, 125 operations (`P135Syntax352.literal`);
* `free_cofactor11_simple.json`: eleven unknowns over ℤ, degree 340, 129 operations (`P135Syntax340.literal`);
* `free_cofactor11_sharp.json`: eleven unknowns over ℤ, degree 328, 130 operations (`P135Syntax328.literal`);

each read at the six source34 ports `P138Ports.ports6`. They are the linear-cofactor circuit
of package 172's 300/144 equation with another centre and the radical weight
`4 = 2²` (`P135Value`), so each bridge is an instance of
`LCFamily.zero_iff_halts`: the centre does not read the unknown `n = x 9` (by `rfl`), and
`4` is a nonzero even square (`LCNorm.weight4`).

For each equation, in its own namespace `Form<degree>`:

* `bridge`: in every model of `𝗜𝚺₁`, the polynomial has a zero in `DiffRing V` iff machine
  215 halts internally;
* `native_equivalence`, `standard_equivalence`, `reference_equivalence`: native iPRA,
  standard iPRA and equality-only iPRA prove that the unsolvability sentence
  `nativeNoZero (signedSplit expression)` (each integer unknown as a difference of two
  naturals) is equivalent to the selected Foundation ZFC consistency predicate. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAInteger135
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open IntegerDomain (IntegerModelBridge signedSplit native_of_integer standard_of_integer
  reference_of_integer)
open P138Ports (ports6 portsR)
open P135Value

namespace Form352

/-- Package 135's 352/125 polynomial: the literal at the six source34 ports. -/
def expression : Expr (Fin 11) := P135Syntax352.literal (fun i => (ports6 i : ℤ))

/-- In every model of `𝗜𝚺₁`, an integer zero exists iff machine 215 halts (no centre,
weight `4`). -/
theorem bridge : IntegerModelBridge expression := fun V _ _ =>
  have h := LCFamily.zero_iff_halts (V := V) (wt := 4) 2 (by norm_num)
    LCNorm.weight4 (fun _ => 0) fun _ _ => rfl
  ⟨fun ⟨x, hx⟩ => h.1 ⟨x, (P135Syntax352.literal_zero_iff x).1 hx⟩,
   fun hT =>
    let ⟨x, hx⟩ := h.2 hT
    ⟨x, (P135Syntax352.literal_zero_iff x).2 hx⟩⟩

/-- **Native iPRA proves: package 135's 352/125 equation has no integer zero iff ZFC is
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

end Form352

namespace Form340

/-- Package 135's 340/129 polynomial: the literal at the six source34 ports. -/
def expression : Expr (Fin 11) := P135Syntax340.literal (fun i => (ports6 i : ℤ))

/-- In every model of `𝗜𝚺₁`, an integer zero exists iff machine 215 halts (centre `P135Value.psi340`,
weight `4`). -/
theorem bridge : IntegerModelBridge expression := fun V _ _ =>
  have h := LCFamily.zero_iff_halts (V := V) (wt := 4) 2 (by norm_num)
    LCNorm.weight4 (psi340 portsR) fun _ _ => rfl
  ⟨fun ⟨x, hx⟩ => h.1 ⟨x, (P135Syntax340.literal_zero_iff x).1 hx⟩,
   fun hT =>
    let ⟨x, hx⟩ := h.2 hT
    ⟨x, (P135Syntax340.literal_zero_iff x).2 hx⟩⟩

/-- **Native iPRA proves: package 135's 340/129 equation has no integer zero iff ZFC is
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

end Form340

namespace Form328

/-- Package 135's 328/130 polynomial: the literal at the six source34 ports. -/
def expression : Expr (Fin 11) := P135Syntax328.literal (fun i => (ports6 i : ℤ))

/-- In every model of `𝗜𝚺₁`, an integer zero exists iff machine 215 halts (centre `P135Value.psi328`,
weight `4`). -/
theorem bridge : IntegerModelBridge expression := fun V _ _ =>
  have h := LCFamily.zero_iff_halts (V := V) (wt := 4) 2 (by norm_num)
    LCNorm.weight4 (psi328 portsR) fun _ _ => rfl
  ⟨fun ⟨x, hx⟩ => h.1 ⟨x, (P135Syntax328.literal_zero_iff x).1 hx⟩,
   fun hT =>
    let ⟨x, hx⟩ := h.2 hT
    ⟨x, (P135Syntax328.literal_zero_iff x).2 hx⟩⟩

/-- **Native iPRA proves: package 135's 328/130 equation has no integer zero iff ZFC is
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

end Form328

end DiophantineConsistency.IPRAInteger135
