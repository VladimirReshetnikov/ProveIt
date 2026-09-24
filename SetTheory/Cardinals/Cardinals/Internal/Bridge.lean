/-
  BRIDGE TO ProveIt's INTERNAL SATISFACTION MACHINERY.

  `ProveIt`'s `BoundedZFCConsistency` development builds, for an abstract model `(V, mem)`
  of the ZF axioms, a Gödel coding `formCode : Form → V` of formulas as sets and an
  internal satisfaction relation `SatIn H A R c e` for set-sized structures, with all
  Tarski clauses and totality proved, and -- decisively -- a *formula* `fSatInF` whose
  satisfaction in `(V, mem)` is exactly `SatIn` (`fSatInF_spec`).

  That is the ingredient this development has been working around: it makes
  "`x` is definable over `V_θ` by the formula coded by `c` from the parameters `e`"
  expressible by a `Form`, which is what the least-counterexample device of the research
  note needs in order to reach the full `OD` class in Theorem 5.1(3), and what the
  definability of the cumulative hierarchy needs in `Virtual/Restriction.lean`.

  This file supplies the first half of the bridge: Lean's concrete `ZFSet` universe is a
  model of ProveIt's `ZFAxioms`.  Nothing is admitted.
-/
import Cardinals.Foundations.Basic
import BoundedZFCConsistency.InternalSatTotality

universe u

namespace Cardinals

open ZFSet
open SetTheory (Form Sat scons ZFAxioms Functional relOf)

/-! ### Replacement for `ZFSet` along an arbitrary functional relation -/

open Classical in
/-- The image of `a` under a functional relation `R`, as a set.  Mathlib's `ZFSet.image`
asks for a `Definable` function; here the relation is an arbitrary `Prop`-valued one, so
the image is built as the range of a choice function on the small index type of those
members of `a` that the relation relates to something. -/
noncomputable def relImage (R : ZFSet.{u} → ZFSet.{u} → Prop) (a : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun y => ∃ x, x ∈ a ∧ R y x)
    (ZFSet.range (fun p : (a : Type (u + 1)) =>
      if h : ∃ y, R y p.1 then Classical.choose h else ∅))

theorem mem_relImage {R : ZFSet.{u} → ZFSet.{u} → Prop} (hfun : Functional R)
    {a y : ZFSet.{u}} : y ∈ relImage R a ↔ ∃ x, x ∈ a ∧ R y x := by
  unfold relImage
  rw [ZFSet.mem_sep]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  obtain ⟨x, hxa, hy⟩ := h
  rw [ZFSet.mem_range]
  refine ⟨⟨x, hxa⟩, ?_⟩
  have hex : ∃ y, R y x := ⟨y, hy⟩
  simp only [dif_pos hex]
  exact hfun x _ _ (Classical.choose_spec hex) hy

/-! ### `ZFSet` is a model of ProveIt's ZF axioms -/

/-- **Lean's `ZFSet` universe satisfies ProveIt's `ZFAxioms`.**  This is what lets the
internal-satisfaction machinery of `BoundedZFCConsistency` be used with the concrete
structures of this development. -/
theorem zfAxioms_zfset : ZFAxioms (fun x y : ZFSet.{u} => x ∈ y) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- extensionality
    intro a b h
    exact ZFSet.ext h
  · -- separation
    intro phi e a
    refine ⟨ZFSet.sep (fun x => Sat (fun x y : ZFSet.{u} => x ∈ y) (scons x e) phi) a,
      fun x => ?_⟩
    exact ZFSet.mem_sep
  · -- pairing
    intro a b
    exact ⟨{a, b}, fun x => ZFSet.mem_pair⟩
  · -- union
    intro u
    refine ⟨⋃₀ u, fun x => ?_⟩
    rw [ZFSet.mem_sUnion]
    exact ⟨fun ⟨v, hv, hx⟩ => ⟨v, hx, hv⟩, fun ⟨v, hx, hv⟩ => ⟨v, hv, hx⟩⟩
  · -- infinity
    refine ⟨ZFSet.omega, ⟨∅, ZFSet.omega_zero, fun z hz => ZFSet.notMem_empty z hz⟩, ?_⟩
    intro x hx
    exact ⟨insert x x, ZFSet.omega_succ hx, fun t => ZFSet.mem_insert_iff.trans Or.comm⟩
  · -- replacement
    intro psi e hfun a
    exact ⟨relImage (relOf (fun x y : ZFSet.{u} => x ∈ y) psi e) a,
      fun y => mem_relImage hfun⟩

end Cardinals
