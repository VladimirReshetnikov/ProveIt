import DiophantineConsistency.WangTiles942StepConstruction

/-! Whole-row, actual first action, left move, and halt-entry reception checks. -/

namespace DiophantineConsistency.WangTiles942StepConstructionChecks

open SetTheory.BusyBeaver WangTiles942 WangTiles942Language
open WangMachineEncoding WangMachineAction WangMachineStep WangTiles942StepConstruction

set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

-- No row, tape-normalization, or target-not-halt premise is supplied.
example (cfg : Config 215) (q : Fin 215) (hq : cfg.state = some q) :
    ∃ R : ℤ → Tile, (∀ x, Allowed (R x)) ∧
      (∀ x, (R x).north = color cfg x) ∧
      (∀ x, (R x).south = color (DecimalMachine215.machine.step cfg) x) ∧
      (∀ x, (R (x+1)).west = (R x).east) :=
  ⟨stepTile cfg q, step_row cfg q hq⟩

example (cfg : Config 215) (q : Fin 215) (x : ℤ) :
    ∃ i : Fin 942, tile i = stepTile cfg q x :=
  (allowed_iff_tile _).mp (stepTile_allowed cfg q x)

-- The receiving bit is the old destination bit, including entry into halt.
example (cfg : Config 215) (q : Fin 215) (hq : cfg.state = some q)
    (hh : (DecimalMachine215.machine.transition q (Tape.read cfg.tape cfg.head)).next = none) :
    (stepTile cfg q (nextHead cfg q)).south =
      432 + (Tape.read cfg.tape (nextHead cfg q)).toNat := by
  rw [stepTile_south cfg q hq]
  exact color_step_enter_halt DecimalMachine215.machine cfg q hq hh

private theorem blank_index : sourceIndex (initial 215) (0 : Fin 215) = 0 := rfl
private theorem blank_next : nextHead (initial 215) (0 : Fin 215) = 1 := by
  rw [nextHead_eq,blank_index]
  have hd : (WangTiles942.action (0 : Fin 430)).2.1 = true := by decide +kernel
  rw [hd]
  rfl

example : stepTile (initial 215) (0 : Fin 215) 0 = ⟨0,2,7,1⟩ := by
  change stepTile (initial 215) (0 : Fin 215) (initial 215).head = _
  rw [stepTile_old_head,blank_index]
  decide +kernel

example : stepTile (initial 215) (0 : Fin 215) 1 = ⟨7,0,0,4⟩ := by
  rw [← blank_next,stepTile_new_head]
  unfold receiveTile
  rw [blank_index,blank_next]
  decide +kernel

-- A duplicate-containing tape is allowed; the destination is already one.
private def haltCfg : Config 215 := ⟨some (62 : Fin 215),-5,[-5,-4,-4]⟩
private theorem halt_index : sourceIndex haltCfg (62 : Fin 215) = 125 := by decide +kernel
private theorem halt_next : nextHead haltCfg (62 : Fin 215) = -4 := by
  rw [nextHead_eq,halt_index]
  have hd : (WangTiles942.action (125 : Fin 430)).2.1 = true := by decide +kernel
  rw [hd]
  rfl

example : stepTile haltCfg (62 : Fin 215) (-5) = ⟨0,127,204,1⟩ := by
  change stepTile haltCfg (62 : Fin 215) haltCfg.head = _
  rw [stepTile_old_head,halt_index]
  decide +kernel

example : stepTile haltCfg (62 : Fin 215) (-4) = ⟨204,1,0,433⟩ := by
  rw [← halt_next,stepTile_new_head]
  unfold receiveTile
  rw [halt_index,halt_next]
  decide +kernel

example : (DecimalMachine215.machine.step haltCfg).state = none := by
  have hh : (DecimalMachine215.machine.transition (62 : Fin 215)
      (Tape.read haltCfg.tape haltCfg.head)).next = none := by
    apply (transition_next_none_iff _ _).mpr
    change (WangTiles942.action (sourceIndex haltCfg (62 : Fin 215))).2.2 = 215
    rw [halt_index]
    decide +kernel
  exact congrArg Config.state
    (step_enter_halt DecimalMachine215.machine haltCfg (62 : Fin 215) rfl hh)

private def leftCfg : Config 215 := ⟨some (2 : Fin 215),3,[3,2]⟩
private theorem left_index : sourceIndex leftCfg (2 : Fin 215) = 5 := by decide +kernel
private theorem left_next : nextHead leftCfg (2 : Fin 215) = 2 := by
  rw [nextHead_eq,left_index]
  have hd : (WangTiles942.action (5 : Fin 430)).2.1 = false := by decide +kernel
  rw [hd]
  rfl

example : stepTile leftCfg (2 : Fin 215) 2 = ⟨0,1,205,11⟩ := by
  rw [← left_next,stepTile_new_head]
  unfold receiveTile
  rw [left_index,left_next]
  decide +kernel

-- This includes either order of old/new head; there is no right-move restriction.
example (cfg : Config 215) (q : Fin 215) (x : ℤ) :
    (stepTile cfg q (x+1)).west = (stepTile cfg q x).east := stepTile_horizontal cfg q x

#print axioms nextHead_ne
#print axioms nextHead_eq
#print axioms stepTile_old_head
#print axioms stepTile_new_head
#print axioms stepTile_elsewhere
#print axioms receiveTile_allowed
#print axioms stepTile_allowed
#print axioms stepTile_north
#print axioms stepTile_south
#print axioms stepTile_west
#print axioms stepTile_east
#print axioms stepTile_horizontal
#print axioms step_row

end DiophantineConsistency.WangTiles942StepConstructionChecks
