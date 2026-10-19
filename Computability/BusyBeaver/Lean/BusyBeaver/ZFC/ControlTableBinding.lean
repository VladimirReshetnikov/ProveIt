import BusyBeaver.ZFC.ArithmeticControlTable
import BusyBeaver.ZFC.PackedTables

set_option autoImplicit false

/-!
Finite packed-table binding to a decoder catalogue. The executable test uses a
counted tree supplied by the caller; its equality to `annotate t` is a separate
proof obligation. `allSites` retains full source paths and rejects `.none`.
There is no linear catalogue lookup in the executable test. The list appears
only in the generic soundness proof and its resulting exact table equality.

This module neither establishes a concrete closed check nor transports runs
of the binary machine in an internal arithmetic model.
-/

namespace SetTheory.BusyBeaver.ZFC.ControlTableBinding

open RegisterPath RMBisim SiteCoverage ControlCatalogue ArithmeticControlTable
open ArithmeticControlBisim (Row)

def successorCounted (ct : ControlCatalogue.CTree) (P : List Bool) (e : Edge) (positive : Bool) : Nat :=
  match e with
  | .node _ | .halt => 0
  | _ => crank ct (outgoingPathOf P e positive) + 1

def rowCounted (ct : ControlCatalogue.CTree) (entry : List Bool × Edge) : Row :=
  ⟨edgeOpcode entry.2, ⟨registerOf entry.2, registerOf_lt _⟩,
    successorCounted ct entry.1 entry.2 false,
    successorCounted ct entry.1 entry.2 true⟩

theorem rowCounted_annotate (t : Tree) (entry : List Bool × Edge) :
    rowCounted (annotate t) entry = rowOf t entry := by
  rcases entry with ⟨P, e⟩
  cases e <;> rfl

/-- Both stored successor fields are checked, including the second field on
non-test rows, even though the interpreter ignores it there. -/
def checkRow (ct : ControlCatalogue.CTree) (rows : Nat → Option Row) (P : List Bool) (e : Edge) : Bool :=
  decide (rows (crank ct P + 1) = some (rowCounted ct (P, e)))

theorem checkRow_sound (ct : ControlCatalogue.CTree) (rows : Nat → Option Row) (P : List Bool) (e : Edge)
    (h : checkRow ct rows P e = true) :
    rows (crank ct P + 1) = some (rowCounted ct (P, e)) := by
  exact of_decide_eq_true h

/-- Generic copy of the structural leaf-path lemma; it imports no old fixed
catalogue and assumes no Prog254 control numbering. -/
theorem leafAt_twalk {t : Tree} {P : List Bool} {e : Edge}
    (hl : LeafAt t P e) : ∀ i, twalk t P i = some (e, i + P.length) := by
  induction hl with
  | here e => intro i; simp [twalk]
  | left hl ih =>
    intro i
    simpa only [twalk, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using ih (i + 1)
  | right hl ih =>
    intro i
    simpa only [twalk, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using ih (i + 1)

/-- The rank of a catalogue entry's complete path is its original index.
Nodup is used only in this generic proof, never as a per-row computation. -/
theorem crank_at_get (t : Tree) (i : Nat) (hi : i < (leafEntries t).length) :
    crank (annotate t) ((getElem (leafEntries t) i hi)).1 = i := by
  let entry := (getElem (leafEntries t) i hi)
  have hl : LeafAt t entry.1 entry.2 :=
    leafEntries_sound t entry.1 entry.2 (List.getElem_mem hi)
  obtain ⟨hr, he⟩ := entry_at_crank t entry.1 0 entry.2 entry.1.length
    (by simpa only [Nat.zero_add] using leafAt_twalk hl 0)
  have he' : (getElem (leafEntries t) (crank (annotate t) entry.1) hr) = (getElem (leafEntries t) i hi) := by
    simpa only [Nat.sub_zero, consume, List.take_append_length] using he
  exact (List.getElem_inj (leafEntries_nodup t)).mp he'

theorem checked_row_at_leaf (t : Tree) (ct : ControlCatalogue.CTree) (rows : Nat → Option Row)
    (hct : ct = annotate t) (hall : allSites (checkRow ct rows) [] t = true)
    (P : List Bool) (e : Edge) (hl : LeafAt t P e) :
    rows (crank (annotate t) P + 1) = some (rowOf t (P, e)) := by
  have hs := allSites_sound (checkRow ct rows) hl [] hall
  have hr := checkRow_sound ct rows P e
    (by simpa only [List.reverse_nil, List.nil_append] using hs)
  simpa only [hct, rowCounted_annotate] using hr

theorem checked_row_at_index (t : Tree) (ct : ControlCatalogue.CTree) (rows : Nat → Option Row)
    (hct : ct = annotate t) (hall : allSites (checkRow ct rows) [] t = true)
    (i : Nat) (hi : i < (leafEntries t).length) :
    rows (i + 1) = some (rowOf t ((getElem (leafEntries t) i hi))) := by
  have hl := leafEntries_sound t ((getElem (leafEntries t) i hi)).1 ((getElem (leafEntries t) i hi)).2
    (List.getElem_mem hi)
  have hr := checked_row_at_leaf t ct rows hct hall _ _ hl
  simpa only [crank_at_get t i hi] using hr

/-- Exact list equality, not just equality of the interpreter's active fields.
The length premise prevents unexamined extra packed rows. -/
theorem packed_table_eq (t : Tree) (ct : ControlCatalogue.CTree) (n count : Nat)
    (hct : ct = annotate t) (hcount : count = (leafEntries t).length)
    (hall : allSites (checkRow ct (PackedTables.rowsOf n count)) [] t = true) :
    PackedTables.table n count = (leafEntries t).map (rowOf t) := by
  apply List.ext_getElem
  · simp only [PackedTables.table_length, List.length_map, hcount]
  · intro i hi hj
    have hi' : i < (leafEntries t).length := by simpa only [List.length_map] using hj
    have hr := checked_row_at_index t ct (PackedTables.rowsOf n count) hct hall i hi'
    obtain ⟨_, hg⟩ := PackedTables.rowsOf_some n count (i + 1) _ hr
    have hg' : getElem? (PackedTables.table n count) i = some (rowOf t (getElem (leafEntries t) i hi')) := by
      simpa only [Nat.add_sub_cancel] using hg
    rw [List.getElem_map]
    exact (List.getElem_eq_iff hi).mpr hg'

/-- Every raw pointer resolves to a real catalogue entry, including implicit
zero extension and truncation. Apply this to `outgoingPathOf P e branch` for
the successor of an instruction. Neither an arbitrary rank nor a default
source entry is admitted as a substitute for the resolved path. -/
theorem checked_rank_resolves (t : Tree) (ct : ControlCatalogue.CTree) (rows : Nat → Option Row)
    (hct : ct = annotate t) (hall : allSites (checkRow ct rows) [] t = true)
    (P : List Bool) :
    ∃ e d, ∃ hr : crank ct P < (leafEntries t).length,
      twalk t P 0 = some (e, d) ∧
      getElem (leafEntries t) (crank ct P) hr = (consume P d, e) := by
  obtain ⟨e, d, hw⟩ := allSites_total (checkRow ct rows) t [] hall P 0
  obtain ⟨hr, he⟩ := entry_at_crank t P 0 e d hw
  subst ct
  exact ⟨e, d, hr, hw, by simpa only [Nat.sub_zero] using he⟩

/-- The checked row for a leaf reached by an arbitrary incoming pointer. -/
theorem checked_row_at_walk (t : Tree) (ct : ControlCatalogue.CTree) (rows : Nat → Option Row)
    (hct : ct = annotate t) (hall : allSites (checkRow ct rows) [] t = true)
    (P : List Bool) (e : Edge) (d : Nat) (hw : twalk t P 0 = some (e, d)) :
    rows (crank (annotate t) (consume P d) + 1) = some (rowOf t (consume P d, e)) := by
  have hs := allSites_twalk (checkRow ct rows) t hall P e d hw
  have hr := checkRow_sound ct rows (consume P d) e hs
  simpa only [hct, rowCounted_annotate] using hr

end SetTheory.BusyBeaver.ZFC.ControlTableBinding
