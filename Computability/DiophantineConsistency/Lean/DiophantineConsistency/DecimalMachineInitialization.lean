import DiophantineConsistency.WangTiles942Core

/-!
# The actual decimal machine's first blank-tape step

The authenticated action-cache theorem supplies the first decoded action;
the large decimal numeral is not reevaluated here. The resulting concrete
configuration writes a one at zero and moves right into state one. This is
the configuration represented by the initialization boundary components,
not the all-blank configuration before the first machine transition.
No tiling, machine-run extraction or consistency equivalence is assumed.
-/

namespace DiophantineConsistency.DecimalMachineInitialization

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC

set_option Elab.async false
set_option maxRecDepth 10000

/-- Transport the cached first action through the proved complete decoder
binding; do not unfold or evaluate the715-digit decoder again. -/
theorem first_action : DecimalMachine215.action 0 = (true, true, 1) := by
  exact (WangTiles942.action_eq_decoder (0 : Fin 430)).symm.trans
    WangTiles942.actual_first_action

/-- The actual machine convention is write, then move right, then state1. -/
theorem first_transition : DecimalMachine215.machine.transition (0 : Fin 215) false =
    ({ write := true, move := Move.right, next := some (1 : Fin 215) } : Action 215) := by
  change KDense215.act (DecimalMachine215.action 0) = _
  rw [first_action]
  rfl

/-- Exact finite-support configuration after one step from the blank tape. -/
def initialized : Config 215 where
  state := some 1
  head := 1
  tape := [0]

theorem step_initial : DecimalMachine215.machine.step (initial 215) = initialized := by
  simp only [Machine.step, initial, startState, Tape.read, List.not_mem_nil, ite_false]
  have hz : (⟨0, Nat.succ_pos 214⟩ : Fin 215) = 0 := by
    apply Fin.ext
    rfl
  rw [hz, first_transition]
  rfl

theorem run_one : DecimalMachine215.machine.run 1 = initialized := by
  exact step_initial

@[simp] theorem initialized_state : initialized.state = some (1 : Fin 215) := rfl

@[simp] theorem initialized_head : initialized.head = (1 : ℤ) := rfl

@[simp] theorem initialized_tape : initialized.tape = [0] := rfl

theorem initialized_not_halted : initialized.state ≠ none := by decide

/-- The only written symbol is exactly the origin; all integer positions
other than zero, including the new head position, still read blank. -/
theorem initialized_read_true_iff (p : ℤ) : Tape.read initialized.tape p = true ↔ p = 0 := by
  simp [initialized, Tape.read]

theorem initialized_read_false_iff (p : ℤ) : Tape.read initialized.tape p = false ↔ p ≠ 0 := by
  simp [initialized, Tape.read]

theorem initialized_read_origin : Tape.read initialized.tape 0 = true := rfl

theorem initialized_read_head : Tape.read initialized.tape initialized.head = false := rfl

/-- Starting from the initialization configuration removes exactly the
first blank-tape transition, without changing the machine or its clock. -/
theorem runFrom_initialized (t : ℕ) :
    DecimalMachine215.machine.runFrom initialized t = DecimalMachine215.machine.run (t+1) := by
  have hh := DecimalMachine215.machine.run_add_eq_runFrom 1 t
  rw [run_one] at hh
  simpa only [Nat.add_comm 1 t] using hh.symm

theorem blank_initial_not_halted : (DecimalMachine215.machine.run 0).state ≠ none := by
  change (some (0 : Fin 215) : Option (Fin 215)) ≠ none
  exact Option.some_ne_none _

/-- Blank-tape halting and halting from the exact initialized state agree.
The zero-time blank configuration is ruled out explicitly. -/
theorem blank_halts_iff_initialized : KDenseBridge.BlankHalts DecimalMachine215.machine ↔
    ∃ t, (DecimalMachine215.machine.runFrom initialized t).state = none := by
  constructor
  · rintro ⟨t, ht⟩
    cases t with
    | zero => exact False.elim (blank_initial_not_halted ht)
    | succ t =>
        refine ⟨t, ?_⟩
        rw [runFrom_initialized]
        exact ht
  · rintro ⟨t, ht⟩
    refine ⟨t+1, ?_⟩
    rw [← runFrom_initialized]
    exact ht

/-- The actual Start boundary leaves plain symbol1 at its origin. -/
theorem start_south : (WangTiles942.tile 0).south = 1 := by
  rw [WangTiles942.start_zero]

/-- The literal initializer head color is the operating state1 reading0. -/
theorem initialized_head_color : WangTiles942.headColor 1 0 = 4 := rfl

theorem initializer_south : (WangTiles942.tile 928).south = WangTiles942.headColor 1 0 := by
  rw [WangTiles942.initializer_928]
  rfl

/-- The left/head/right boundary rows are present in the actual finite
tail table. This small check does not unfold any machine action decoder. -/
theorem initialization_rows :
    (927, (⟨2,434,2,0⟩ : WangTiles942.Tile)) ∈ WangTiles942.tailRows ∧
    (928, (⟨3,436,4,4⟩ : WangTiles942.Tile)) ∈ WangTiles942.tailRows ∧
    (929, (⟨4,436,4,0⟩ : WangTiles942.Tile)) ∈ WangTiles942.tailRows := by
  decide +kernel

/-- Both actual side initializer rows leave plain blank0 below them. -/
theorem initialization_side_south : ∀ row ∈ WangTiles942.tailRows,
    row.1 = 927 ∨ row.1 = 929 → row.2.south = 0 := by
  decide +kernel

/-- Component calibration only: origin symbol1 and the adjacent head1/0
agree with the post-step tape and state. No global row semantics is asserted. -/
theorem initialization_components :
    (WangTiles942.tile 0).south = (Tape.read initialized.tape 0).toNat ∧
    (WangTiles942.tile 928).south =
      WangTiles942.headColor 1 (Tape.read initialized.tape initialized.head).toNat ∧
    ∀ p : ℤ, p ≠ 0 → Tape.read initialized.tape p = false := by
  refine ⟨?_, ?_, ?_⟩
  · rw [start_south, initialized_read_origin]
    rfl
  · rw [initializer_south, initialized_read_head]
    rfl
  · intro p hp
    exact (initialized_read_false_iff p).mpr hp

end DiophantineConsistency.DecimalMachineInitialization
