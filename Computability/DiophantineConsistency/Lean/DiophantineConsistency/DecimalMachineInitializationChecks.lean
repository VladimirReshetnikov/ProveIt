import DiophantineConsistency.DecimalMachineInitialization

/-! Exact first-step, integer tape, clock-shift and boundary-component checks.
No tiling premise and no second evaluation of the decimal numeral occur. -/

namespace DiophantineConsistency.DecimalMachineInitializationChecks

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open DecimalMachineInitialization

set_option Elab.async false
set_option maxRecDepth 10000

example : DecimalMachine215.action 0 = (true, true, 1) := first_action

example : DecimalMachine215.machine.transition (0 : Fin 215) false =
    ({ write := true, move := Move.right, next := some (1 : Fin 215) } : Action 215) :=
  first_transition

example : DecimalMachine215.machine.run 1 =
    ({ state := some 1, head := 1, tape := [0] } : Config 215) := run_one

example : (DecimalMachine215.machine.run 1).state ≠ none := by
  rw [run_one]
  exact initialized_not_halted

example (p : ℤ) : Tape.read (DecimalMachine215.machine.run 1).tape p = true ↔ p = 0 := by
  rw [run_one]
  exact initialized_read_true_iff p

/-- Negative positions are included: this is not a one-sided tape claim. -/
example : Tape.read initialized.tape (-1) = false :=
  (initialized_read_false_iff (-1)).mpr (by decide)

example : Tape.read initialized.tape initialized.head = false := initialized_read_head

example (t : ℕ) :
    DecimalMachine215.machine.runFrom initialized t = DecimalMachine215.machine.run (t+1) :=
  runFrom_initialized t

example : KDenseBridge.BlankHalts DecimalMachine215.machine ↔
    ∃ t, (DecimalMachine215.machine.runFrom initialized t).state = none :=
  blank_halts_iff_initialized

/-- The post-step configuration is genuinely different from the blank start. -/
example : initialized ≠ initial 215 := by
  intro h
  have hh := congrArg Config.head h
  change (1 : ℤ) = 0 at hh
  exact (by decide : (1 : ℤ) ≠ 0) hh

example : (WangTiles942.tile 0).south = 1 := start_south

example : (WangTiles942.tile 928).south = 4 := by
  rw [initializer_south, initialized_head_color]

example :
    (927, (⟨2,434,2,0⟩ : WangTiles942.Tile)) ∈ WangTiles942.tailRows ∧
    (929, (⟨4,436,4,0⟩ : WangTiles942.Tile)) ∈ WangTiles942.tailRows :=
  ⟨initialization_rows.1, initialization_rows.2.2⟩

example (row : ℕ × WangTiles942.Tile) (h : row ∈ WangTiles942.tailRows)
    (hi : row.1 = 927 ∨ row.1 = 929) : row.2.south = 0 :=
  initialization_side_south row h hi

#print axioms first_action
#print axioms first_transition
#print axioms step_initial
#print axioms run_one
#print axioms initialized_not_halted
#print axioms initialized_read_true_iff
#print axioms initialized_read_false_iff
#print axioms initialized_read_origin
#print axioms initialized_read_head
#print axioms runFrom_initialized
#print axioms blank_initial_not_halted
#print axioms blank_halts_iff_initialized
#print axioms start_south
#print axioms initialized_head_color
#print axioms initializer_south
#print axioms initialization_rows
#print axioms initialization_side_south
#print axioms initialization_components

end DiophantineConsistency.DecimalMachineInitializationChecks
