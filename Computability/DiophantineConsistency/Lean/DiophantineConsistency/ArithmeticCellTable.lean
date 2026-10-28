import DiophantineConsistency.CurrentKernelData2011

/-! Matrix-free row facts of the 942-tile table, checked in one kernel traversal
(see `ArithmeticCellPhysical`). -/

namespace DiophantineConsistency.ArithmeticCellPhysical

open WangTiles942

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-! ### Row facts, by evaluation of the table -/

noncomputable def Tight (t : Tile) : Prop := t.west < 256 ∧ t.east < 256 ∧ t.north ≤ 438 ∧ t.south ≤ 438

noncomputable instance (t : Tile) : Decidable (Tight t) := inferInstanceAs
  (Decidable (t.west < 256 ∧ t.east < 256 ∧ t.north ≤ 438 ∧ t.south ≤ 438))


/-- A structural left inverse for the complete printed tile table
(`WangTiles942Permutation.recoveredIndex`). -/
noncomputable def recoveredIndex (t : Tile) : ℕ :=
  if 2 ≤ t.north ∧ t.north ≤ 431 then t.north - 1
  else if t.south = 438 then 923 + 2 * (t.north / 432) + t.north % 432
  else if t.north ≤ 1 then
    if t.south = t.north then 433 + t.north
    else 423 + 2 * (t.west + t.east) + t.north
  else if t.north ≤ 433 then t.north - 1
  else if t.north = 434 then 927
  else if t.north = 435 then 0
  else if t.north = 436 then if t.south = 4 then 928 else 929
  else if t.north = 437 then 933 + 3 * (if t.west = 4 then 2 else t.west) + t.east
  else 496 + t.south

noncomputable def cutoffTile : Tile := ⟨0,1,221,45⟩

noncomputable def RowFacts (row : ℕ × Tile) : Prop :=
  Tight row.2 ∧ row.2.west < 250 ∧ recoveredIndex row.2 = row.1 ∧
    (row.2.south = 45 → row.2 = cutoffTile)

noncomputable instance (row : ℕ × Tile) : Decidable (RowFacts row) := by unfold RowFacts; infer_instance

/-- All row facts in one traversal of the table. -/
theorem rows_facts : ∀ row ∈ orderedRows, RowFacts row := by decide +kernel

theorem rows_tight : ∀ row ∈ orderedRows, Tight row.2 := fun r h => (rows_facts r h).1
theorem rows_west_lt : ∀ row ∈ orderedRows, row.2.west < 250 := fun r h => (rows_facts r h).2.1
theorem rows_recovered : ∀ row ∈ orderedRows, recoveredIndex row.2 = row.1 :=
  fun r h => (rows_facts r h).2.2.1
theorem rows_south45 : ∀ row ∈ orderedRows, row.2.south = 45 → row.2 = cutoffTile :=
  fun r h => (rows_facts r h).2.2.2


end DiophantineConsistency.ArithmeticCellPhysical
