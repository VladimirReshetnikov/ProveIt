import DiophantineConsistency.ZRows.IntegerDomain
import DiophantineConsistency.Z10.Z10SyntaxPolar
import DiophantineConsistency.Z10.Z10SyntaxLinear
import DiophantineConsistency.Z10.Z10SyntaxCubic
import DiophantineConsistency.Z10.Z10SyntaxSixterm
import DiophantineConsistency.Z10.Z10Sound
import DiophantineConsistency.Z10.Z10Complete

/-! # iPRA endpoints for package 106's four ten-integer equations

The equations are `106-compact-certificates-round13/norm/integer10_{polar,linear,cubic,sixterm}.json`:
ten unrestricted integer unknowns `t g0 c0 k0 l w x y z m`, 467, 470, 473 and 507 operations, at
the four ports of the 121x8801 machine (`Mixed121Ports.ports`). Their Lean syntax trees are the
generated literals `Z10SyntaxPolar.literal` … `Z10SyntaxSixterm.literal`.

`bridge`: in every model `V` of `𝗜𝚺₁`, each equation has a zero in the ring of differences
`DiffRing V` iff machine 215 halts internally:

* `Z10Sound.halts` (soundness: a zero of the polar value gives a halt);
* `Z10Complete.zero_of_halt` (completeness: a halt gives a zero of the polar value);
* `Z10Regs.exists_shift`: a variant has a zero exactly when polar has one (its value is polar's
  at `m + shear`, and the shear does not read `m`);
* `Z10Syntax*.literal_zero_iff` identifies each literal's zeros with those of its value.

`IntegerDomain` turns this into iPRA statements about `signedSplit expression`, the 20-unknown
natural-number form in which each integer unknown is written as `aᵢ − bᵢ`. For each form:

* `native_equivalence`: the native iPRA theory proves `nativeNoZero (signedSplit expression)`
  (no integer zero) equivalent to `∼mappedNativeRefutation embedding`, the native rendering of
  "machine 215 does not halt" and so of Con(ZFC);
* `standard_equivalence`: the same in the standard iPRA theory;
* `reference_equivalence`: the order-erased form in the equality-only reference theory.

The correspondence of the literals with the JSON files is the finite check
`research/p106-integer10/tools/gen_literal106.py FORM --check`. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAInteger106
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open IntegerDomain (IntegerModelBridge signedSplit native_of_integer standard_of_integer
  reference_of_integer)

/-- The ports of the 121x8801 machine as integers. -/
def ports : Fin 4 → ℤ := fun j => (Mixed121Ports.ports j : ℤ)

namespace Polar

/-- Package 106's 467-operation polar polynomial. -/
def expression : Expr (Fin 10) := Z10SyntaxPolar.literal ports

theorem bridge : IntegerModelBridge expression := fun _ _ _ =>
  ⟨fun ⟨x, hx⟩ => Z10Sound.halts x ((Z10SyntaxPolar.literal_zero_iff x).1 hx),
   fun ⟨T, hT⟩ =>
    let ⟨x, hx⟩ := Z10Complete.zero_of_halt T hT
    ⟨x, (Z10SyntaxPolar.literal_zero_iff x).2 hx⟩⟩

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

end Polar

namespace Linear

/-- Package 106's 470-operation linear polynomial. -/
def expression : Expr (Fin 10) := Z10SyntaxLinear.literal ports

theorem bridge : IntegerModelBridge expression := fun _ _ _ =>
  ⟨fun ⟨x, hx⟩ =>
    let ⟨x', hx'⟩ := (Z10Regs.exists_shift Z10Regs.shearLin _).mp
      ⟨x, (Z10SyntaxLinear.literal_zero_iff x).1 hx⟩
    Z10Sound.halts x' hx',
   fun ⟨T, hT⟩ =>
    let ⟨x, hx⟩ := Z10Complete.zero_of_halt_variant Z10Regs.shearLin T hT
    ⟨x, (Z10SyntaxLinear.literal_zero_iff x).2 hx⟩⟩

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

end Linear

namespace Cubic

/-- Package 106's 473-operation cubic polynomial. -/
def expression : Expr (Fin 10) := Z10SyntaxCubic.literal ports

theorem bridge : IntegerModelBridge expression := fun _ _ _ =>
  ⟨fun ⟨x, hx⟩ =>
    let ⟨x', hx'⟩ := (Z10Regs.exists_shift Z10Regs.shearCub _).mp
      ⟨x, (Z10SyntaxCubic.literal_zero_iff x).1 hx⟩
    Z10Sound.halts x' hx',
   fun ⟨T, hT⟩ =>
    let ⟨x, hx⟩ := Z10Complete.zero_of_halt_variant Z10Regs.shearCub T hT
    ⟨x, (Z10SyntaxCubic.literal_zero_iff x).2 hx⟩⟩

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

end Cubic

namespace Sixterm

/-- Package 106's 507-operation six-term polynomial. -/
def expression : Expr (Fin 10) := Z10SyntaxSixterm.literal ports

theorem bridge : IntegerModelBridge expression := fun _ _ _ =>
  ⟨fun ⟨x, hx⟩ =>
    let ⟨x', hx'⟩ := (Z10Regs.exists_shift Z10Regs.shearSix _).mp
      ⟨x, (Z10SyntaxSixterm.literal_zero_iff x).1 hx⟩
    Z10Sound.halts x' hx',
   fun ⟨T, hT⟩ =>
    let ⟨x, hx⟩ := Z10Complete.zero_of_halt_variant Z10Regs.shearSix T hT
    ⟨x, (Z10SyntaxSixterm.literal_zero_iff x).2 hx⟩⟩

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

end Sixterm

#print axioms Polar.native_equivalence
#print axioms Polar.standard_equivalence
#print axioms Polar.reference_equivalence
#print axioms Linear.native_equivalence
#print axioms Cubic.native_equivalence
#print axioms Sixterm.native_equivalence

end DiophantineConsistency.IPRAInteger106
