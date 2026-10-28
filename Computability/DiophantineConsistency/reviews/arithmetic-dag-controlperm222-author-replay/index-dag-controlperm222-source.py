from pathlib import Path
p=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticDagControlPerm222.lean')
s=p.read_text();start=s.index('private def catalogue :');end=s.index('/-- Every ordinary root exit',start)
new='''private def catalogue : List Row :=
  (ControlCatalogue.leafEntries (RMBisim.ptree path)).map
    (ArithmeticControlTable.rowOf (RMBisim.ptree path))

/-- Index a tree without traversing a long list prefix. -/
private def entryAt : RMBisim.Tree → Nat → Option (List Bool × RegisterPath.Edge)
  | .none, _ => none
  | .leaf e, 0 => some ([], e)
  | .leaf _, _ + 1 => none
  | .node a b, n =>
      if n < SiteCoverage.leafCount a then
        (entryAt a n).map (fun e => (false :: e.1, e.2))
      else (entryAt b (n - SiteCoverage.leafCount a)).map (fun e => (true :: e.1, e.2))

/-- Generic exact indexing identity; neither table nor program is assumed. -/
private theorem entryAt_eq (t : RMBisim.Tree) (n : Nat) :
    entryAt t n = (ControlCatalogue.leafEntries t)[n]? := by
  induction t generalizing n with
  | none => simp [entryAt, ControlCatalogue.leafEntries]
  | leaf e => cases n <;> simp [entryAt, ControlCatalogue.leafEntries]
  | node a b iha ihb =>
    simp only [entryAt, ControlCatalogue.leafEntries, List.getElem?_append,
      List.length_map, ControlCatalogue.leafEntries_length, List.getElem?_map,
      iha, ihb]

private def rowAt (n : Nat) : Option Row :=
  (entryAt (RMBisim.ptree path) n).map (ArithmeticControlTable.rowOf (RMBisim.ptree path))

private theorem rowAt_eq (n : Nat) : rowAt n = catalogue[n]? := by
  simp only [rowAt, catalogue, List.getElem?_map, entryAt_eq]

private def packedAt (n : Nat) : Option Row :=
  if n < count then some (PackedTables.decodeRow (PackedTables.slot packedRows n 36)) else none

private theorem packedAt_eq (n : Nat) : packedAt n = table[n]? := by
  simp only [packedAt, table, PackedTables.table, List.getElem?_ofFn]

private theorem catalogue_length : catalogue.length = 4751 := by
  rw [catalogue, List.length_map, ControlCatalogue.leafEntries_length]
  decide +kernel

private abbrev block (i : Nat) : Prop :=
  ∀ j : Fin 64, 64 * i + j.val < count →
    packedAt (64 * i + j.val) = rowAt (64 * i + j.val)

'''
for i in range(75):new+=f'private theorem block_{i} : block {i} := by decide +kernel\n'
term='(fun i => Fin.elim0 i)'
for i in reversed(range(75)):term=f'(Fin.cases block_{i} {term})'
new+='\nprivate theorem blocks_checked : ∀ i : Fin 75, block i.val :=\n  '+term+'\n\n'
new+='''/-- The quotient/remainder split covers every actual row, including the last 15. -/
private theorem all_rows (n : Nat) (hn : n < count) : packedAt n = rowAt n := by
  have hi : n / 64 < 75 := (Nat.div_lt_iff_lt_mul (by decide)).2 (by
    change n < 4751 at hn
    omega)
  have h := blocks_checked ⟨n / 64, hi⟩ ⟨n % 64, Nat.mod_lt _ (by decide)⟩
  simp only [Nat.div_add_mod] at h
  exact h hn

/-- Complete catalogue equality: all indices, not a sample or supplied premise. -/
theorem table_eq_catalogue :
    table = (ControlCatalogue.leafEntries (RMBisim.ptree path)).map
      (ArithmeticControlTable.rowOf (RMBisim.ptree path)) := by
  change table = catalogue
  apply List.ext_getElem?
  intro n
  by_cases hn : n < count
  · rw [← packedAt_eq, ← rowAt_eq]
    exact all_rows n hn
  · have ht : table.length ≤ n := by rw [table_length]; change ¬n < 4751 at hn; omega
    have hc : catalogue.length ≤ n := by rw [catalogue_length]; change ¬n < 4751 at hn; omega
    rw [List.getElem?_eq_none ht, List.getElem?_eq_none hc]

'''
p.write_text(s[:start]+new+s[end:])
