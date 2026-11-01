import DiophantineConsistency.CurrentKernelData2011

/-! Matrix-free row facts of the 942-tile table that the Matrix-free clones
`MFWangTiles942Core`/`MFWangTiles942Permutation` do not provide, checked in one kernel
traversal (see `ArithmeticCellPhysical`). Kept in its own module so that the table
evaluation does not share a Lean process with the rest of `ArithmeticCellPhysical`. -/

namespace DiophantineConsistency.ArithmeticCellPhysical

open WangTiles942

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

noncomputable def cutoffTile : Tile := ⟨0,1,221,45⟩

noncomputable def RowFacts (row : ℕ × Tile) : Prop :=
  row.2.west < 250 ∧ (row.2.south = 45 → row.2 = cutoffTile)

noncomputable instance (row : ℕ × Tile) : Decidable (RowFacts row) := by
  unfold RowFacts; infer_instance

/-- Both row facts in one traversal of the table. -/
theorem rows_facts : ∀ row ∈ orderedRows, RowFacts row := by decide +kernel

end DiophantineConsistency.ArithmeticCellPhysical
