import DiophantineConsistency.WangTiles942TraceCycle
import DiophantineConsistency.WangTiles942InputLanguage

/-! Exact time indexing, wrapped edge, free height padding, and missing-premise controls. -/

namespace DiophantineConsistency.WangTiles942TraceCycleChecks

open SetTheory.BusyBeaver WangTiles942 WangTiles942Language WangMachineEncoding
open WangTiles942FinishConstruction WangTiles942TraceCycle

set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

-- The actual first run row outputs the same seeded configuration as initialization.
example : (runTile 0 0).south = 1 ∧ (runTile 0 1).south = 4 := by
  rw [runTile_south,runTile_south,DecimalMachineInitialization.run_one]
  exact ⟨initialized_color_zero,initialized_color_one⟩

example (t : ℕ) (x : ℤ) :
    Allowed (runTile t x) ∧ (runTile t x).north = color (DecimalMachine215.machine.run t) x ∧
      (runTile t x).south = color (DecimalMachine215.machine.run (t+1)) x ∧
      (runTile t (x+1)).west = (runTile t x).east :=
  ⟨runTile_allowed t x,runTile_north t x,runTile_south t x,runTile_horizontal t x⟩

example (T extra : ℕ) (hh : (DecimalMachine215.machine.run T).state = none) (x : ℤ) :
    runTile (T+extra) x = passTile (DecimalMachine215.machine.run T) x :=
  runTile_after_halt T hh (T+extra) (by omega) x

-- The modulo successor is explicit at both interior and wraparound indices.
example : nextIndex (by decide : 0 < 5) (3 : Fin 5) = 4 ∧
    nextIndex (by decide : 0 < 5) (4 : Fin 5) = 0 := by decide

-- At height 3 there are exactly initializer, finish(run1), reset branches.
-- Their Allowed membership is not asserted here without a halt premise.
example (x : ℤ) : cycleTile (0 : Fin 3) x = initialTile x ∧
    cycleTile (1 : Fin 3) x = finishTile (DecimalMachine215.machine.run 1) x ∧
    cycleTile (2 : Fin 3) x = resetTile x := by
  exact ⟨cycleTile_zero (by decide) x,
    cycleTile_finish (by decide) (1 : Fin 3) (by decide) x,
    cycleTile_last (by decide) (2 : Fin 3) (by decide) x⟩

example (x : ℤ) : cycleTile (2 : Fin 5) x = runTile 2 x :=
  cycleTile_run (2 : Fin 5) (by decide) (by decide) (by decide) x

-- Every natural amount of extra height is permitted, without any width parameter.
example (T extra : ℕ) (hh : (DecimalMachine215.machine.run T).state = none) :
    let H := T+3+extra
    (∀ k : Fin H, ∀ x : ℤ, Allowed (cycleTile k x)) ∧
    (∀ k : Fin H, ∀ x : ℤ,
      (cycleTile (nextIndex (by omega) k) x).north = (cycleTile k x).south) ∧
    cycleTile (⟨0,by omega⟩ : Fin H) 0 = start := by
  dsimp only
  obtain ⟨hA,_,hV,hS⟩ := trace_cycle T (T+3+extra) hh (by omega) (by omega)
  exact ⟨hA,hV,hS⟩

-- Wraparound is proved at every signed spatial coordinate, not only at Start.
example {H : ℕ} (hH : 3 ≤ H) (k : Fin H) (hk : k.val+1 = H) (x : ℤ) :
    (cycleTile (⟨0,by omega⟩ : Fin H) x).north = (cycleTile k x).south := by
  have hn : nextIndex (by omega) k = (⟨0,by omega⟩ : Fin H) :=
    Fin.ext (nextIndex_val_of_last (by omega) k hk)
  simpa only [hn] using cycleTile_temporal hH k x

-- Dropping the height>=3 condition makes the initializer/reset edge mismatch.
example : (cycleTile (nextIndex (by decide : 0 < 2) (0 : Fin 2)) 0).north ≠
    (cycleTile (0 : Fin 2) 0).south := by decide

-- Temporal colors alone do not imply Allowed finish membership before actual halt.
example : ¬ Allowed (cycleTile (1 : Fin 3) 1) := by
  rw [cycleTile_finish (by decide) (1 : Fin 3) (by decide)]
  change ¬ Allowed (finishTile (DecimalMachine215.machine.run 1) 1)
  rw [DecimalMachineInitialization.run_one]
  intro ht
  have he := (WangTiles942InputLanguage.north_operating_iff_transition
    ht (1 : Fin 215) (0 : Fin 2)).mp rfl
  have hs := congrArg Tile.south he
  have hb := Bool.toNat_le (WangTiles942.action
    (WangTiles942InputLanguage.inputIndex (1 : Fin 215) (0 : Fin 2))).1
  change (438 : ℕ) = (WangTiles942.action
    (WangTiles942InputLanguage.inputIndex (1 : Fin 215) (0 : Fin 2))).1.toNat at hs
  omega

#print axioms runTile_allowed
#print axioms runTile_north
#print axioms runTile_south
#print axioms runTile_horizontal
#print axioms runTile_after_halt
#print axioms nextIndex_val_of_lt
#print axioms nextIndex_val_of_last
#print axioms cycleTile_zero
#print axioms cycleTile_last
#print axioms cycleTile_finish
#print axioms cycleTile_run
#print axioms cycleTile_allowed
#print axioms cycleTile_horizontal
#print axioms cycleTile_north
#print axioms cycleTile_south
#print axioms cycleTile_temporal
#print axioms trace_cycle

end DiophantineConsistency.WangTiles942TraceCycleChecks
