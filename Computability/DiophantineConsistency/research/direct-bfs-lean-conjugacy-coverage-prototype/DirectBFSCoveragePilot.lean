import DirectBFSConjugacyBase

/-! Bounded checks for an array-backed direct-BFS conjugacy certificate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
noncomputable section
namespace DirectBFSCoveragePilot
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

theorem rows_000 : checkRows 0 32=true := by decide
theorem rows_928 : checkRows 928 15=true := by decide
theorem horizontal_all : checkHorizontal 0 250=true := by decide
theorem vertical_all : checkVertical 0 439=true := by decide
theorem row_inverse_all : checkRowInverse 0 943=true := by decide
#print axioms DirectBFSCoveragePilot.rows_000
#print axioms DirectBFSCoveragePilot.rows_928
#print axioms DirectBFSCoveragePilot.horizontal_all
#print axioms DirectBFSCoveragePilot.vertical_all
#print axioms DirectBFSCoveragePilot.row_inverse_all
end DirectBFSCoveragePilot
