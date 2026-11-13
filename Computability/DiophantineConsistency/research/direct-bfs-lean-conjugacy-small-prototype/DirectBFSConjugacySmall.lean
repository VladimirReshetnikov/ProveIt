import DirectBFSConjugacyBase

/-! Bounded checks for an array-backed direct-BFS conjugacy certificate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
noncomputable section
namespace DirectBFSConjugacySmall
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

theorem rows_000 : checkRows 0 16=true := by decide
theorem rows_927 : checkRows 927 16=true := by decide
theorem inverse_000 : checkRowInverse 0 16=true := by decide
theorem inverse_927 : checkRowInverse 927 16=true := by decide
#print axioms DirectBFSConjugacySmall.rows_000
#print axioms DirectBFSConjugacySmall.rows_927
#print axioms DirectBFSConjugacySmall.inverse_000
#print axioms DirectBFSConjugacySmall.inverse_927
end DirectBFSConjugacySmall
