import BusyBeaver.ZFC.KQ1Collect

/-!
Native formula-indexed Replacement in the bisimulation quotient of a `QHyp`
structure, derived from its existing quotient Collection theorem.

The actual matrix guards membership in the requested domain and swaps the
output/input slots. Collection supplies a supported covering set; functionality
identifies each chosen output with the requested one. No totality or Collection
for arbitrary semantic relations is assumed.

The native guarded-image argument adapts the consolidation-plan proposal placed
at 56b37bde8b064d852154ad8478d58ec9ab5375d6. Its raw predecessor followed
`S_ax.v:rep_core`, upstream 297ab8df7e5de329605c3875b4934643b371a5e3;
the source-change record preserves that predecessor and its retired helper names.
-/

namespace SetTheory.BusyBeaver.ZFC.KQ1Replacement

open Form ProfileCollection ProfileModel KQHyp

universe u
variable {V : Type u}

/-- Swap the matrix's two arguments, and skip the inserted domain slot. -/
def replacementRename : Nat → Nat
  | 0 => 1
  | 1 => 0
  | k + 2 => k + 3

/-- Native quotient Collection gives the actual semantic `ZFAxioms.repl` image. -/
theorem quotient_replacement (mem : V → V → Prop) (witness : V) (h : QHyp mem)
    (phi : Form) (env : Nat → KQ1Model.Domain mem witness h)
    (hFunctional : Functional (relOf (KQ1Model.quotientMember mem witness h) phi env))
    (a : KQ1Model.Domain mem witness h) :
    ∃ b, ∀ y, KQ1Model.quotientMember mem witness h y b ↔
      ∃ x, KQ1Model.quotientMember mem witness h x a ∧
        relOf (KQ1Model.quotientMember mem witness h) phi env y x := by
  let qm := KQ1Model.quotientMember mem witness h
  have hc : CollectionInstance qm (fun x y => qm x a ∧ relOf qm phi env y x) :=
    collectionInstance_congr qm _ _ (fun x y => and_congr Iff.rfl
      (Sat_rename_relOf (mem := qm) phi replacementRename
        (scons x (scons y (scons a env))) env y x
        (fun n => match n with | 0 => rfl | 1 => rfl | _ + 2 => rfl)))
      (KQ1Collect.quotient_collection mem witness h
        (fAnd (fMem 0 2) (rename replacementRename phi)) (scons a env))
  obtain ⟨b, hSupport, hCover⟩ := hc a
  refine ⟨b, fun y => ⟨hSupport y, ?_⟩⟩
  rintro ⟨x, hxa, hxy⟩
  obtain ⟨z, hzb, _, hxz⟩ := hCover x hxa ⟨y, hxa, hxy⟩
  exact (hFunctional x z y hxz hxy) ▸ hzb

/-- Every repository Replacement formula holds under every quotient valuation. -/
theorem quotient_repl_form (mem : V → V → Prop) (witness : V) (h : QHyp mem) :
    ∀ phi env, SetTheory.Sat (KQ1Model.quotientMember mem witness h) env (Repl_form phi) := by
  intro phi env
  exact (bridge_Repl phi env).mpr (quotient_replacement mem witness h phi env)

end SetTheory.BusyBeaver.ZFC.KQ1Replacement
