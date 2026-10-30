import ZFCinPA.UniformStatement

/-!
# Existential proof packages for the uniform internal-provability selector

`ZFCinPA.UniformStatement` reduced the literal sentence
`PA ⊢ ∀ n, Prov_ZFC(⌜Conₙ(ZFC)⌝)` to the selector `ZFCProofSelectorIn`: an
internal `𝗭𝗙𝗖`-proof of the built consistency code at *every* element of
every PA model.  In a nonstandard model, a metatheoretic recursion over `Nat`
cannot produce those proof codes.

This module records the `𝚺₁` package induction that discharges the selector
from three local obligations.  A `Package x z` witness may store the code of
a level-specific certificate together with codes of `𝗭𝗙𝗖` derivations for
its clauses; the relation is allowed to have many witnesses, so it need not
be the graph of a canonical primitive-recursive compiler.  `𝚺₁` induction
inside the model only needs one base package, a way to extend any package by
one level, and an extraction of the required consistency proof from any
package.

The results below are an infrastructure reduction, not a construction of
those packages: the substantive base, successor, and extraction obligations
remain explicit hypotheses.  The direct specialization at the end takes the
package relation to be the represented proof predicate itself, applied to a
`𝚺₁`-definable master-code function — the exact interface the staged
certificate compiler is expected to fill.
-/

set_option autoImplicit false

namespace LeanProofs
namespace ZFCinPA

open LO LO.FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V]

/-- There is some coded proof package at index `x`.

Keeping the package contents abstract makes the induction lemma reusable
while still exposing its exact logical-complexity requirement. -/
def HasZFCConsistencyProofPackage
    (Package : V → V → Prop) (x : V) : Prop :=
  ∃ z : V, Package x z

/-- Existentially forgetting a package code preserves `𝚺₁` definability.

`Definable.exs` places its freshly bound witness in coordinate zero.  The
explicit coordinate swap below is therefore necessary because `Package`
takes the index before the package code. -/
lemma hasZFCConsistencyProofPackage_definable
    {Package : V → V → Prop}
    (hPackage : HierarchySymbol.sigmaOne.DefinableRel Package) :
    HierarchySymbol.sigmaOne.DefinablePred
      (HasZFCConsistencyProofPackage Package) := by
  unfold HasZFCConsistencyProofPackage
  apply HierarchySymbol.Definable.exs
  exact HierarchySymbol.DefinableRel.comp hPackage
    (HierarchySymbol.DefinableFunction.var 1)
    (HierarchySymbol.DefinableFunction.var 0)

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Existential proof packages are sufficient for the model-internal
selector.

The induction is model-internal: `x` ranges over the ambient arithmetic
model `V`, so the conclusion includes nonstandard indices.  No uniqueness,
canonical choice, or definable function graph for package witnesses is
used. -/
theorem zfcProofSelectorIn_of_package
    {Package : V → V → Prop}
    (hPackage : HierarchySymbol.sigmaOne.DefinableRel Package)
    (hzero : ∃ z : V, Package 0 z)
    (hsucc : ∀ x z : V, Package x z → ∃ z' : V, Package (x + 1) z')
    (hfinal : ∀ x z : V, Package x z →
      ∃ c : V, ConZFCSetCode c x ∧ Provable 𝗭𝗙𝗖 c) :
    ZFCProofSelectorIn V := by
  have hall : ∀ x : V, HasZFCConsistencyProofPackage Package x := by
    intro x
    induction x using ISigma1.sigma1_succ_induction
    · exact hasZFCConsistencyProofPackage_definable hPackage
    case zero => exact hzero
    case succ x ih =>
      rcases ih with ⟨z, hz⟩
      exact hsucc x z hz
  intro x
  rcases hall x with ⟨z, hz⟩
  exact hfinal x z hz

/-! ## The direct master-certificate specialization

The staged compiler is expected to produce, at every index, a `𝗭𝗙𝗖`-proof of
one master certificate whose code is a `𝚺₁`-definable function of the index.
For that shape the package relation can be the represented proof predicate
itself: `Proof 𝗭𝗙𝗖` is `𝚫₁`, so composing it with the master-code function
keeps the relation `𝚺₁`, and no auxiliary compiler state has to be coded
into the witness. -/

/-- The package witness is the proof code of the master certificate at index
`x` — no auxiliary state and no canonical-choice requirement. -/
def DirectZFCMasterProofPackage (masterCode : V → V) (x d : V) : Prop :=
  Proof 𝗭𝗙𝗖 d (masterCode x)

/-- Direct proof packages form a `𝚺₁` relation as soon as the master-code
function is `𝚺₁` definable. -/
lemma directZFCMasterProofPackage_definable
    {masterCode : V → V}
    (hmaster : HierarchySymbol.sigmaOne.DefinableFunction₁ masterCode) :
    HierarchySymbol.sigmaOne.DefinableRel
      (DirectZFCMasterProofPackage (V := V) masterCode) := by
  letI : HierarchySymbol.sigmaOne.DefinableFunction₁ masterCode := hmaster
  unfold DirectZFCMasterProofPackage
  apply HierarchySymbol.DefinableRel.comp (P := Proof 𝗭𝗙𝗖)
  · exact HierarchySymbol.Definable.of_deltaOne (by definability)
  · exact HierarchySymbol.DefinableFunction.var 1
  · exact HierarchySymbol.DefinableFunction₁.comp
      (HierarchySymbol.DefinableFunction.var 0)

/-- A base master proof, a successor template, and a consistency-proof
extraction give the model-internal selector, for any `𝚺₁`-definable master
code.  This theorem performs genuine `𝚺₁` induction inside the model
through `zfcProofSelectorIn_of_package`; it is not an external recursion
over standard naturals. -/
theorem zfcProofSelectorIn_of_directMasterProofs
    {masterCode : V → V}
    (hmaster : HierarchySymbol.sigmaOne.DefinableFunction₁ masterCode)
    (hbase : ∃ d : V, Proof 𝗭𝗙𝗖 d (masterCode 0))
    (hsucc : ∀ x d : V, Proof 𝗭𝗙𝗖 d (masterCode x) →
      ∃ d' : V, Proof 𝗭𝗙𝗖 d' (masterCode (x + 1)))
    (hfinal : ∀ x d : V, Proof 𝗭𝗙𝗖 d (masterCode x) →
      ∃ c : V, ConZFCSetCode c x ∧ Provable 𝗭𝗙𝗖 c) :
    ZFCProofSelectorIn V := by
  apply zfcProofSelectorIn_of_package
    (Package := DirectZFCMasterProofPackage masterCode)
  · exact directZFCMasterProofPackage_definable hmaster
  · exact hbase
  · exact hsucc
  · exact hfinal

end ZFCinPA
end LeanProofs
