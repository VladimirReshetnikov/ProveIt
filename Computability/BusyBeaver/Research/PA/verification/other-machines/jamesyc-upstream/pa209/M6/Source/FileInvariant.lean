module
public import M6.Source.RootFrame
@[expose] public section

namespace M6.Source
open M6.Runtime

theorem incr_file_length (vs : List Nat) (i : Nat) : (Runtime.incr i vs).length = vs.length := by
  induction vs generalizing i with
  | nil => cases i <;> rfl
  | cons v vs ih => cases i <;> simp [Runtime.incr,ih]

theorem decr_file_length (vs : List Nat) (i : Nat) : (Runtime.decr i vs).length = vs.length := by
  induction vs generalizing i with
  | nil => cases i <;> rfl
  | cons v vs ih => cases i <;> simp [Runtime.decr,ih]

/-- Spare cells are retained: increment appends a fresh zero and decrement
never shortens the physical register file. -/
theorem effectFile_length (e : Eff) (vs : List Nat) : vs.length ≤ (effectFile e vs).length := by
  cases e <;> simp [effectFile,incr_file_length,decr_file_length]

theorem effectFile_valid_length (e : Eff) (vs : List Nat) (h : 10 ≤ vs.length) :
    10 ≤ (effectFile e vs).length := Nat.le_trans h (effectFile_length e vs)
#print axioms effectFile_valid_length
end M6.Source

