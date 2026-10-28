from pathlib import Path
p=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticDagControlPerm222.lean')
s=p.read_text()
old='''/-- Complete current catalogue identity, checked in the kernel. -/
theorem table_eq_catalogue :
    table = (ControlCatalogue.leafEntries (RMBisim.ptree path)).map
      (ArithmeticControlTable.rowOf (RMBisim.ptree path)) := by
  decide +kernel

theorem table_length : table.length = 4751 := PackedTables.table_length _ _
'''
new='''theorem table_length : table.length = 4751 := PackedTables.table_length _ _

private def catalogue : List Row :=
  (ControlCatalogue.leafEntries (RMBisim.ptree path)).map
    (ArithmeticControlTable.rowOf (RMBisim.ptree path))

/-- Complete block composition, for arbitrary lists; no concrete row is assumed. -/
private theorem eq_of_blocks {α : Type*} (a b : List α) (width blocks : Nat)
    (hw : 0 < width) (ha : a.length ≤ blocks * width) (hb : b.length ≤ blocks * width)
    (h : ∀ i : Fin blocks, (a.drop (width * i.val)).take width =
      (b.drop (width * i.val)).take width) : a = b := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < blocks * width
  · have hi : k / width < blocks := (Nat.div_lt_iff_lt_mul hw).2 hk
    have hr : k % width < width := Nat.mod_lt k hw
    have he := congrArg (fun l : List α => l[k % width]?) (h ⟨k / width, hi⟩)
    simpa only [List.getElem?_take_of_lt hr, List.getElem?_drop, Nat.div_add_mod] using he
  · rw [List.getElem?_eq_none (by omega : a.length ≤ k),
        List.getElem?_eq_none (by omega : b.length ≤ k)]

private theorem catalogue_length : catalogue.length = 4751 := by decide +kernel

private def block (i : Nat) : Prop :=
  (table.drop (64 * i)).take 64 = (catalogue.drop (64 * i)).take 64

'''
for i in range(75):new+=f'private theorem block_{i} : block {i} := by decide +kernel\n'
term='Fin.elim0'
for i in reversed(range(75)):term=f'(Fin.cases block_{i} {term})'
new+='\nprivate theorem blocks_checked : ∀ i : Fin 75, block i.val :=\n  '+term+'\n\n'
new+='''/-- Complete current catalogue identity from all 75 checked blocks. -/
theorem table_eq_catalogue :
    table = (ControlCatalogue.leafEntries (RMBisim.ptree path)).map
      (ArithmeticControlTable.rowOf (RMBisim.ptree path)) := by
  exact eq_of_blocks table catalogue 64 75 (by decide)
    (by rw [table_length]; decide) (by rw [catalogue_length]; decide) blocks_checked
'''
assert s.count(old)==1
p.write_text(s.replace(old,new))
