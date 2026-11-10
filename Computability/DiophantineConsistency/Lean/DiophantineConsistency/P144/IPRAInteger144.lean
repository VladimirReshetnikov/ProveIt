import DiophantineConsistency.ZRows.IntegerDomain
import DiophantineConsistency.P144.P144Syntax316
import DiophantineConsistency.P144.P144Syntax308
import DiophantineConsistency.LinCof.LCFamily

/-! # iPRA endpoints for package 144's eleven-integer equations 316/133, 308/140

The equations are the JSON DAGs below `con-zfc-diophantine-forms/144-shared-certificates-round18/scalar/`:

* `free_whole_center11_c316.json`: eleven unknowns over ℤ, degree 316, 133 operations (`P144Syntax316.literal`);
* `free_whole_center11_c308.json`: eleven unknowns over ℤ, degree 308, 140 operations (`P144Syntax308.literal`);

each read at the six source34 ports `P138Ports.ports6`. They are the linear-cofactor circuit
of package 172's 300/144 equation with another centre and the radical weight
`64 = 8²` (`P135Value`), so each bridge is an instance of
`LCFamily.zero_iff_halts`: the centre does not read the unknown `n = x 9` (by `rfl`), and
`64` is a nonzero even square (`LCNorm.weight64`).

For each equation, in its own namespace `Form<degree>`:

* `bridge`: in every model of `𝗜𝚺₁`, the polynomial has a zero in `DiffRing V` iff machine
  215 halts internally;
* `native_equivalence`, `standard_equivalence`, `reference_equivalence`: native iPRA,
  standard iPRA and equality-only iPRA prove that the unsolvability sentence
  `nativeNoZero (signedSplit expression)` (each integer unknown as a difference of two
  naturals) is equivalent to the selected Foundation ZFC consistency predicate. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAInteger144
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open IntegerDomain (IntegerModelBridge signedSplit native_of_integer standard_of_integer
  reference_of_integer)
open P138Ports (ports6 portsR)
open P135Value

namespace Form316

/-- Package 144's 316/133 polynomial: the literal at the six source34 ports. -/
def expression : Expr (Fin 11) := P144Syntax316.literal (fun i => (ports6 i : ℤ))

/-- In every model of `𝗜𝚺₁`, an integer zero exists iff machine 215 halts (centre `P135Value.psi316`,
weight `64`). -/
theorem bridge : IntegerModelBridge expression := fun V _ _ =>
  have h := LCFamily.zero_iff_halts (V := V) (wt := 64) 8 (by norm_num)
    LCNorm.weight64 (psi316 portsR) fun _ _ => rfl
  ⟨fun ⟨x, hx⟩ => h.1 ⟨x, (P144Syntax316.literal_zero_iff x).1 hx⟩,
   fun hT =>
    let ⟨x, hx⟩ := h.2 hT
    ⟨x, (P144Syntax316.literal_zero_iff x).2 hx⟩⟩

/-- **Native iPRA proves: package 144's 316/133 equation has no integer zero iff ZFC is
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

end Form316

namespace Form308

/-- Package 144's 308/140 polynomial: the literal at the six source34 ports. -/
def expression : Expr (Fin 11) := P144Syntax308.literal (fun i => (ports6 i : ℤ))

/-- In every model of `𝗜𝚺₁`, an integer zero exists iff machine 215 halts (centre `P135Value.psi308`,
weight `64`). -/
theorem bridge : IntegerModelBridge expression := fun V _ _ =>
  have h := LCFamily.zero_iff_halts (V := V) (wt := 64) 8 (by norm_num)
    LCNorm.weight64 (psi308 portsR) fun _ _ => rfl
  ⟨fun ⟨x, hx⟩ => h.1 ⟨x, (P144Syntax308.literal_zero_iff x).1 hx⟩,
   fun hT =>
    let ⟨x, hx⟩ := h.2 hT
    ⟨x, (P144Syntax308.literal_zero_iff x).2 hx⟩⟩

/-- **Native iPRA proves: package 144's 308/140 equation has no integer zero iff ZFC is
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

end Form308

end DiophantineConsistency.IPRAInteger144
