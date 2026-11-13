module
public import M6.Runtime
public import M6.Source.Semantics

/-! Exact logical-to-physical register permutation. The physical file has at
least ten cells, including a spare; increment appends another one spare. -/
@[expose] public section

namespace M6.Source

def physicalRegister (r : Fin 9) : Nat :=
  match r.val with
  | 0 => 6 | 1 => 2 | 2 => 0 | 3 => 4 | 4 => 3
  | 5 => 7 | 6 => 8 | 7 => 5 | _ => 1

def readFile (vs : List Nat) : Registers := fun r => vs.getD (physicalRegister r) 0

theorem physicalRegister_lt (r : Fin 9) : physicalRegister r < 9 := by
  exact (by decide : ∀ r : Fin 9, physicalRegister r < 9) r

theorem physicalRegister_injective (r s : Fin 9) :
    physicalRegister r = physicalRegister s ↔ r = s := by
  exact (by decide : ∀ r s : Fin 9, physicalRegister r = physicalRegister s ↔ r = s) r s

private theorem getD_incr (vs : List Nat) (i j : Nat) (hi : i < vs.length) :
    (Runtime.incr i vs).getD j 0 =
      if j = i then vs.getD j 0 + 1 else vs.getD j 0 := by
  induction vs generalizing i j with
  | nil => simp at hi
  | cons v vs ih =>
    cases i <;> cases j <;> simp_all [Runtime.incr, List.getD]

private theorem getD_decr (vs : List Nat) (i j : Nat) (hi : i < vs.length) :
    (Runtime.decr i vs).getD j 0 =
      if j = i then vs.getD j 0 - 1 else vs.getD j 0 := by
  induction vs generalizing i j with
  | nil => simp at hi
  | cons v vs ih =>
    cases i <;> cases j <;> simp_all [Runtime.decr, List.getD]

theorem readFile_incr (vs : List Nat) (hv : 9 ≤ vs.length) (r : Fin 9) :
    readFile (Runtime.incr (physicalRegister r) vs) =
      write (readFile vs) r (readFile vs r + 1) := by
  funext s
  have hi : physicalRegister r < vs.length := Nat.lt_of_lt_of_le (physicalRegister_lt r) hv
  simp only [readFile, getD_incr vs _ _ hi, write, physicalRegister_injective]
  split <;> simp_all

theorem readFile_decr (vs : List Nat) (hv : 9 ≤ vs.length) (r : Fin 9) :
    readFile (Runtime.decr (physicalRegister r) vs) =
      write (readFile vs) r (readFile vs r - 1) := by
  funext s
  have hi : physicalRegister r < vs.length := Nat.lt_of_lt_of_le (physicalRegister_lt r) hv
  simp only [readFile, getD_decr vs _ _ hi, write, physicalRegister_injective]
  split <;> simp_all

private theorem incr_length (vs : List Nat) (i : Nat) :
    (Runtime.incr i vs).length = vs.length := by
  induction vs generalizing i with
  | nil => cases i <;> rfl
  | cons v vs ih => cases i <;> simp [Runtime.incr, ih]

private theorem getD_append_left (vs ws : List Nat) (i : Nat) (hi : i < vs.length) :
    (vs ++ ws).getD i 0 = vs.getD i 0 := by
  induction vs generalizing i with
  | nil => simp at hi
  | cons v vs ih => cases i <;> simp_all [List.getD]

theorem readFile_append (vs ws : List Nat) (hv : 9 ≤ vs.length) :
    readFile (vs ++ ws) = readFile vs := by
  funext r
  exact getD_append_left vs ws _ (Nat.lt_of_lt_of_le (physicalRegister_lt r) hv)

/-- The actual runtime increment preserves the register projection despite
appending a one-valued spare. No assumption discards the physical spare tail. -/
theorem readFile_increment_with_spare (vs : List Nat) (hv : 9 ≤ vs.length) (r : Fin 9) :
    readFile (Runtime.incr (physicalRegister r) vs ++ [1]) =
      write (readFile vs) r (readFile vs r + 1) := by
  rw [readFile_append _ _ (by simpa only [incr_length] using hv)]
  exact readFile_incr vs hv r

/-- Physical zero/positive branch conditions are exactly the source register
conditions, rather than an independent interpretation of the branch flag. -/
theorem valid_branch_iff (vs : List Nat) (r : Fin 9) (zero : Bool) :
    Runtime.Valid (some (physicalRegister r, zero)) vs ↔
      10 ≤ vs.length ∧ (if zero then readFile vs r = 0 else readFile vs r ≠ 0) := by
  rfl

#print axioms readFile_increment_with_spare
#print axioms readFile_decr
#print axioms valid_branch_iff
end M6.Source

