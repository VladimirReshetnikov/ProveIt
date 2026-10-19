import BusyBeaver.ZFC.TableRowsRotation240
import BusyBeaver.ZFC.SitesRotation240

set_option autoImplicit false

/-!
The exact direct240 source catalogue and packed control rows. All finite
identities and site acceptance come from the separately checked complete
tables/coverage; no row or binary-site computation is repeated here.
Control numbers are one-based DFS positions in TreeRotation240, not Prog254.
Pointer resolution retains the consumed path, including implicit zero bits.
This is a source-only adapter; it asserts no internal binary simulation.
The source/program/simulation attribution of the imported modules is retained.
-/
namespace SetTheory.BusyBeaver.ZFC.ControlCatalogueRotation240

open RegisterPath RMBisim SiteCoverage ControlCatalogue

def actualEntries : List (List Bool × Edge) := leafEntries TreeRotation240.tree

theorem actualEntries_length : actualEntries.length = 6455 :=
  CountedTreeRotation240.catalogue_length

abbrev Control := Fin 6455

def source (i : Control) : List Bool × Edge :=
  getElem actualEntries i.val (by rw [actualEntries_length]; exact i.isLt)

def number (i : Control) : Nat := i.val + 1

/-- Least-significant-first numeric instruction pointer; its length is separate. -/
def sourcePC (i : Control) : Nat := ArithmeticControlTable.bitsNat (source i).1

abbrev table : List ArithmeticControlBisim.Row :=
  PackedTables.table BisimCertRotation240.tableR BisimCertRotation240.countR

abbrev rows (c : Nat) : Option ArithmeticControlBisim.Row :=
  PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR c

theorem table_eq : table = actualEntries.map (ArithmeticControlTable.rowOf TreeRotation240.tree) :=
  TableRowsRotation240.table_eq

theorem table_length : table.length = 6455 := by
  simpa only [table, BisimCertRotation240.countR] using
    PackedTables.table_length BisimCertRotation240.tableR BisimCertRotation240.countR

theorem source_leaf (i : Control) : LeafAt TreeRotation240.tree (source i).1 (source i).2 :=
  leafEntries_sound _ _ _ (List.getElem_mem _)

theorem source_accepted (i : Control) :
    SiteRotation240.checkSite (source i).1 (source i).2 = true := by
  simpa only [List.reverse_nil, List.nil_append] using
    allSites_sound SiteRotation240.checkSite (source_leaf i) [] SitesRotation240.all_sites

theorem source_length (i : Control) : (source i).1.length ≤ 64 :=
  SiteRotation240.checkSite_length _ _ (source_accepted i)

theorem source_not_node (i : Control) (n : Nat) : (source i).2 ≠ .node n := by
  intro hn
  have h := source_accepted i
  rw [hn, SiteRotation240.check_node_false] at h
  cases h

theorem source_walk (i : Control) :
    walk SourceRotation240.program (SourceRotation240.program.nnodes + 1)
      SourceRotation240.program.root (source i).1 0 =
      some ((source i).2, (source i).1.length) := by
  rw [TreeRotation240.walk_eq_tree]
  simpa only [List.drop_zero, Nat.zero_add] using
    ControlTableBinding.leafAt_twalk (source_leaf i) 0

theorem source_rank (i : Control) :
    crank CountedTreeRotation240.counted (source i).1 = i.val := by
  rw [CountedTreeRotation240.counted_eq]
  exact ControlTableBinding.crank_at_get TreeRotation240.tree i.val
    (by rw [CountedTreeRotation240.catalogue_length]; exact i.isLt)

theorem rows_at (i : Control) :
    rows (number i) = some (ArithmeticControlTable.rowOf TreeRotation240.tree (source i)) := by
  exact ControlTableBinding.checked_row_at_index TreeRotation240.tree
    CountedTreeRotation240.counted rows CountedTreeRotation240.counted_eq
    TableRowsRotation240.all_rows i.val
    (by rw [CountedTreeRotation240.catalogue_length]; exact i.isLt)

theorem table_row_at (i : Control) :
    getElem? table i.val = some (ArithmeticControlTable.rowOf TreeRotation240.tree (source i)) := by
  have h := (PackedTables.rowsOf_some BisimCertRotation240.tableR
    BisimCertRotation240.countR (number i) _ (rows_at i)).2
  simpa only [number, Nat.add_sub_cancel] using h

private theorem rank_lt (P : List Bool) : crank CountedTreeRotation240.counted P < 6455 := by
  obtain ⟨e, d, hr, _, _⟩ := ControlTableBinding.checked_rank_resolves
    TreeRotation240.tree CountedTreeRotation240.counted rows
    CountedTreeRotation240.counted_eq TableRowsRotation240.all_rows P
  simpa only [CountedTreeRotation240.catalogue_length] using hr

/-- Every pointer resolves to a real source entry, never a default entry. -/
def resolveControl (P : List Bool) : Control :=
  ⟨crank CountedTreeRotation240.counted P, rank_lt P⟩

theorem resolve_source (P : List Bool) (e : Edge) (d : Nat)
    (hw : walk SourceRotation240.program (SourceRotation240.program.nnodes + 1)
      SourceRotation240.program.root P 0 = some (e, d)) :
    source (resolveControl P) = (consume P d, e) := by
  have ht : twalk TreeRotation240.tree P 0 = some (e, d) := by
    simpa only [TreeRotation240.walk_eq_tree, List.drop_zero] using hw
  obtain ⟨hr, he⟩ := entry_at_crank TreeRotation240.tree P 0 e d ht
  simpa only [source, actualEntries, resolveControl, CountedTreeRotation240.counted_eq,
    Nat.sub_zero] using he

theorem resolve_source_self (i : Control) : resolveControl (source i).1 = i := by
  apply Fin.ext
  exact source_rank i

theorem resolve_number_valid (P : List Bool) :
    0 < number (resolveControl P) ∧ number (resolveControl P) ≤ 6455 :=
  ⟨Nat.succ_pos _, Nat.succ_le_of_lt (resolveControl P).isLt⟩

theorem resolved_path (P : List Bool) :
    ∃ e d, walk SourceRotation240.program (SourceRotation240.program.nnodes + 1)
        SourceRotation240.program.root P 0 = some (e, d) ∧
      source (resolveControl P) = (consume P d, e) ∧
      SiteRotation240.checkSite (consume P d) e = true := by
  obtain ⟨e, d, hw⟩ := SitesRotation240.actual_walk_exists P
  exact ⟨e, d, hw, resolve_source P e d hw, SitesRotation240.actual_walk_checked P e d hw⟩

def nextControl (i : Control) (positive : Bool) : Nat :=
  ArithmeticControlTable.successorOf TreeRotation240.tree (source i).1 (source i).2 positive

theorem nextControl_number (i : Control) (positive : Bool) (h : (source i).2 ≠ .halt) :
    nextControl i positive = number (resolveControl
      (ArithmeticControlTable.outgoingPathOf (source i).1 (source i).2 positive)) := by
  cases he : (source i).2 with
  | node n => exact False.elim (source_not_node i n he)
  | halt => exact False.elim (h he)
  | inc r =>
    simp only [nextControl, ArithmeticControlTable.successorOf, he, number,
      resolveControl, CountedTreeRotation240.counted_eq]
  | decnz r =>
    simp only [nextControl, ArithmeticControlTable.successorOf, he, number,
      resolveControl, CountedTreeRotation240.counted_eq]
  | brk k =>
    simp only [nextControl, ArithmeticControlTable.successorOf, he, number,
      resolveControl, CountedTreeRotation240.counted_eq]
  | cont k =>
    simp only [nextControl, ArithmeticControlTable.successorOf, he, number,
      resolveControl, CountedTreeRotation240.counted_eq]

/-- Successor resolution preserves the actual decoded and accepted source. -/
theorem nextControl_resolves (i : Control) (positive : Bool) (h : (source i).2 ≠ .halt) :
    ∃ j : Control, nextControl i positive = number j ∧
      ∃ e d, walk SourceRotation240.program (SourceRotation240.program.nnodes + 1)
          SourceRotation240.program.root
          (ArithmeticControlTable.outgoingPathOf (source i).1 (source i).2 positive) 0 =
          some (e, d) ∧
        source j = (consume
          (ArithmeticControlTable.outgoingPathOf (source i).1 (source i).2 positive) d, e) := by
  let P := ArithmeticControlTable.outgoingPathOf (source i).1 (source i).2 positive
  obtain ⟨e, d, hw, hs, _⟩ := resolved_path P
  exact ⟨resolveControl P, nextControl_number i positive h, e, d, hw, hs⟩

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic

theorem sourcePC_cast {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
    (i : Control) : (sourcePC i : V) = ArithmeticControlTable.binaryValue (source i).1 :=
  (ArithmeticControlTable.binaryValue_cast (source i).1).symm

end SetTheory.BusyBeaver.ZFC.ControlCatalogueRotation240
