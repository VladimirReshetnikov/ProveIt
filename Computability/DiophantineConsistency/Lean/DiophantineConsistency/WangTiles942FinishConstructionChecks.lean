import DiophantineConsistency.WangTiles942FinishConstruction
import DiophantineConsistency.WangTiles942InputLanguage

/-! Halted-head alternatives, signed initializer coordinates, and exact reset interfaces. -/

namespace DiophantineConsistency.WangTiles942FinishConstructionChecks

open SetTheory.BusyBeaver WangTiles942 WangTiles942Language WangMachineEncoding
open WangTiles942FinishConstruction

set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

-- Both halted read bits are retained: blank head 432 and written head 433.
example : passTile ⟨none,0,[]⟩ 0 = ⟨0,432,0,432⟩ ∧
    finishTile ⟨none,0,[]⟩ 0 = ⟨0,432,0,438⟩ := ⟨rfl,rfl⟩

private def haltedCfg : Config 215 := ⟨none,-3,[-3,-3,8]⟩

example : passTile haltedCfg (-3) = ⟨0,433,0,433⟩ ∧
    finishTile haltedCfg (-3) = ⟨0,433,0,438⟩ := by decide +kernel

-- The arbitrary duplicate-containing tape still has plain cells away from its head.
example : passTile haltedCfg 8 = ⟨0,1,0,1⟩ ∧
    finishTile haltedCfg 8 = ⟨0,1,0,438⟩ ∧
    passTile haltedCfg 0 = ⟨0,0,0,0⟩ := by decide +kernel

example (x : ℤ) : Allowed (passTile haltedCfg x) ∧ Allowed (finishTile haltedCfg x) :=
  ⟨passTile_allowed haltedCfg rfl x,finishTile_allowed haltedCfg rfl x⟩

-- A pass row agrees with the actual stationary step of a halted configuration.
example (cfg : Config 215) (hh : cfg.state = none) (x : ℤ) :
    (passTile cfg x).south = color (DecimalMachine215.machine.step cfg) x := by
  have he : DecimalMachine215.machine.step cfg = cfg := by simp only [Machine.step,hh]
  rw [he]
  rfl

-- The halt premise cannot be dropped: the initial operating head needs a transition.
example : ¬ Allowed (passTile (initial 215) 0) := by
  intro ht
  have he := (WangTiles942InputLanguage.north_operating_iff_transition
    ht (0 : Fin 215) (0 : Fin 2)).mp rfl
  have heast := congrArg Tile.east he
  have hrail : (transitionRow (WangTiles942InputLanguage.inputIndex
      (0 : Fin 215) (0 : Fin 2))).2.east = 7 := by decide +kernel
  rw [hrail] at heast
  change (0 : ℕ) = 7 at heast
  omega

example : initialTile (-100) = ⟨2,434,2,0⟩ ∧ initialTile 0 = start ∧
    initialTile 1 = ⟨3,436,4,4⟩ ∧ initialTile 100 = ⟨4,436,4,0⟩ := by decide +kernel

-- Actual initializer south 4 is preserved; the old 188 convention is excluded.
example : (initialTile 1).south = 4 ∧ (initialTile 1).south ≠ 188 := by decide

-- All three integer boundary crossings match with the stated orientation.
example : (initialTile 0).west = (initialTile (-1)).east ∧
    (initialTile 1).west = (initialTile 0).east ∧
    (initialTile 2).west = (initialTile 1).east := by decide

example (x : ℤ) (hx : x < 0) : resetTile x = ⟨1,438,1,434⟩ := by
  unfold resetTile
  rw [initialTile_negative x hx]

example : resetTile 0 = ⟨1,438,1,435⟩ ∧ resetTile 1 = ⟨1,438,1,436⟩ := by decide

example (cfg : Config 215) (hh : cfg.state = none) (x : ℤ) :
    (∃ p : Fin 942, tile p = passTile cfg x) ∧
    (∃ f : Fin 942, tile f = finishTile cfg x) ∧
    (∃ i : Fin 942, tile i = initialTile x) ∧
    (∃ r : Fin 942, tile r = resetTile x) :=
  ⟨(allowed_iff_tile _).mp (passTile_allowed cfg hh x),
    (allowed_iff_tile _).mp (finishTile_allowed cfg hh x),
    (allowed_iff_tile _).mp (initialTile_allowed x),
    (allowed_iff_tile _).mp (resetTile_allowed x)⟩

example (cfg : Config 215) (x : ℤ) :
    (finishTile cfg x).north = (passTile cfg x).south ∧
    (resetTile x).north = (finishTile cfg x).south ∧
    (initialTile x).north = (resetTile x).south ∧
    (initialTile x).south = color DecimalMachineInitialization.initialized x :=
  ⟨(pass_finish_matching cfg x).2,(finish_reset_initial_matching cfg x).1,
    (finish_reset_initial_matching cfg x).2,initialTile_south x⟩

#print axioms passTile_allowed
#print axioms finishTile_allowed
#print axioms passTile_colors
#print axioms finishTile_colors
#print axioms passTile_horizontal
#print axioms finishTile_horizontal
#print axioms initialTile_negative
#print axioms initialTile_zero
#print axioms initialTile_one
#print axioms initialTile_right
#print axioms initialTile_allowed
#print axioms initialTile_north_mem
#print axioms initialTile_south
#print axioms initialTile_horizontal
#print axioms resetTile_allowed
#print axioms resetTile_colors
#print axioms resetTile_horizontal
#print axioms pass_finish_matching
#print axioms finish_reset_initial_matching
#print axioms closing_rows

end DiophantineConsistency.WangTiles942FinishConstructionChecks
