import PA194ADDispatch
import PA194ADBounded
set_option autoImplicit false
namespace PA194ADNumericTape
open TableDispatch PA194ADTable

theorem row_write_eq (i : Nat) :
    (adRows.getD i (0,0,194)).1 = (PA194Rows.rows.getD i (0,0,194)).1 := by
  have ha := getDMap (fun r : Nat × Nat × Nat => r.1) adRows i (0,0,194)
  have hp := getDMap (fun r : Nat × Nat × Nat => r.1) PA194Rows.rows i (0,0,194)
  change PA194ADDispatch.writes.getD i 0 = _ at ha
  change TableDispatch.writes.getD i 0 = _ at hp
  rw [PA194ADDispatch.writes_eq] at ha
  exact ha.symm.trans hp

theorem row_direction_eq (i : Nat) :
    (adRows.getD i (0,0,194)).2.1 = (PA194Rows.rows.getD i (0,0,194)).2.1 := by
  have ha := getDMap (fun r : Nat × Nat × Nat => r.2.1) adRows i (0,0,194)
  have hp := getDMap (fun r : Nat × Nat × Nat => r.2.1) PA194Rows.rows i (0,0,194)
  change PA194ADDispatch.directions.getD i 0 = _ at ha
  change TableDispatch.directions.getD i 0 = _ at hp
  rw [PA194ADDispatch.directions_eq] at ha
  exact ha.symm.trans hp

theorem next_tape_eq (q l r : Nat) :
    (PA194ADTable.next adRows (q,l,r)).2 = (PA194Bounded.next (q,l,r)).2 := by
  simp only [PA194ADTable.next, PA194Bounded.next, PA194Bounded.row, PA194Bounded.rows, rowIndex,
    row_write_eq, row_direction_eq]
  split_ifs <;> rfl

#print axioms row_write_eq
#print axioms row_direction_eq
#print axioms next_tape_eq
end PA194ADNumericTape
