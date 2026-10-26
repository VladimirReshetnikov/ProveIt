import DiophantineConsistency.WangTiles942CycleBoundary

/-! Independent margin choices, squared seam code, and the moved-head exclusion check. -/

namespace DiophantineConsistency.WangTiles942CycleBoundaryChecks

open SetTheory.BusyBeaver WangTiles942 WangTiles942Language WangMachineEncoding
open WangTiles942TraceCycle WangTiles942CycleBoundary

set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

example : edgeCode (0 : Fin 5) = 2 ∧ edgeCode (3 : Fin 5) = 0 ∧
    edgeCode (4 : Fin 5) = 1 := by decide

-- The right seam code really is squared: the initializer edge is 4, not 2.
example : (edgeCode (0 : Fin 5))^2 = 4 ∧
    (edgeCode (0 : Fin 5))^2 ≠ edgeCode (0 : Fin 5) := by decide

-- Any pair of the exposed codes forms one of the actual nine seam tuples.
example {H : ℕ} (k l : Fin H) :
    Allowed (⟨(edgeCode k)^2,437,edgeCode l,437⟩ : Tile) :=
  Allowed.seam ⟨edgeCode k,by have h := edgeCode_le_two k; omega⟩
    ⟨edgeCode l,by have h := edgeCode_le_two l; omega⟩

-- Each side may have arbitrary, unequal extra width; there is no height premise.
example (T leftExtra rightExtra : ℕ)
    (hh : (DecimalMachine215.machine.run T).state = none) {H : ℕ} (k : Fin H) :
    (cycleTile k (-((T+2+leftExtra : ℕ) : ℤ)+1)).west = edgeCode k ∧
    (cycleTile k (((T+2+rightExtra : ℕ) : ℤ)-1)).east = (edgeCode k)^2 :=
  cycleTile_outer_edges T (T+2+leftExtra) (T+2+rightExtra) hh (by omega) (by omega) k

-- Arbitrarily late run rows still use the literal blank pass tile at these margins.
example (T t : ℕ) (hh : (DecimalMachine215.machine.run T).state = none) :
    runTile t (-((T : ℤ)+1)) = ⟨0,0,0,0⟩ ∧
    runTile t ((T : ℤ)+1) = ⟨0,0,0,0⟩ :=
  ⟨runTile_outer_blank T hh t _ (Or.inl (by omega)),
    runTile_outer_blank T hh t _ (Or.inr (by omega))⟩

-- Excluding only the old head is insufficient: the actual first receiver is at 1.
example : (1 : ℤ) ≠ (DecimalMachine215.machine.run 0).head ∧
    runTile 0 1 ≠ (⟨0,0,0,0⟩ : Tile) := by
  constructor
  · decide
  · intro he
    have hs := congrArg Tile.south he
    have hv : (runTile 0 1).south = 4 := by
      rw [runTile_south,DecimalMachineInitialization.run_one]
      exact initialized_color_one
    rw [hv] at hs
    change (4 : ℕ) = 0 at hs
    omega

#print axioms runTile_outer_blank
#print axioms runTile_left_blank
#print axioms runTile_right_blank
#print axioms edgeCode_le_two
#print axioms cycleTile_left_west
#print axioms cycleTile_right_east
#print axioms cycleTile_outer_edges

end DiophantineConsistency.WangTiles942CycleBoundaryChecks
