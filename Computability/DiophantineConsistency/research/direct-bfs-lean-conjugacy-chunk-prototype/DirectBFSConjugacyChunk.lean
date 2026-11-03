import DirectBFSConjugacyBase

/-! Bounded checks for an array-backed direct-BFS conjugacy certificate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
noncomputable section
namespace DirectBFSConjugacyChunk
open DirectBFSConjugacyBase

def checkRows (start count : Nat) : Bool :=
  (List.range' start count).all fun i =>
    decide (rename (original.getD i (0,0,0,0)) = direct.getD (rowMap.getD i 0) (0,0,0,0))

def checkHorizontal (start count : Nat) : Bool :=
  (List.range' start count).all fun i => decide (horizontal.getD (horizontalInverse.getD i 0) 0=i)

def checkVertical (start count : Nat) : Bool :=
  (List.range' start count).all fun i => decide (vertical.getD (verticalInverse.getD i 0) 0=i)

def checkRowInverse (start count : Nat) : Bool :=
  (List.range' start count).all fun i => decide (rowMap.getD (rowInverse.getD i 0) 0=i)

theorem rows_first : checkRows 0 8=true := by decide
theorem rows_last : checkRows 935 8=true := by decide
theorem horizontal_first : checkHorizontal 0 8=true := by decide
theorem vertical_last : checkVertical 431 8=true := by decide
theorem inverse_last : checkRowInverse 935 8=true := by decide

#print axioms DirectBFSConjugacyChunk.rows_first
#print axioms DirectBFSConjugacyChunk.rows_last
#print axioms DirectBFSConjugacyChunk.horizontal_first
#print axioms DirectBFSConjugacyChunk.vertical_last
#print axioms DirectBFSConjugacyChunk.inverse_last
end DirectBFSConjugacyChunk
