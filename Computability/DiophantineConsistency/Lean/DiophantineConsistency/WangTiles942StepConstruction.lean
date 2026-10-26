import DiophantineConsistency.WangMachineAction
import DiophantineConsistency.WangMachineStep

/-!
# Construct the exact Wang row of an actual operating machine step

The old head uses its literal transition tile, the moved head uses the receive
tile for its actual target and old tape bit, and every other cell passes its bit.
Entry into halt is included. This constructs a whole-integer matching row; it
assumes no row/step equivalence or finite-rectangle calibration.
-/

namespace DiophantineConsistency.WangTiles942StepConstruction

open SetTheory.BusyBeaver WangTiles942 WangTiles942Language
open WangMachineEncoding WangMachineAction WangMachineStep

set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The action index at the actual old head. -/
def sourceIndex (cfg : Config 215) (q : Fin 215) : Fin 430 :=
  WangMachineAction.inputIndex q (Tape.read cfg.tape cfg.head)

/-- The moved head from the actual decimal machine transition. -/
def nextHead (cfg : Config 215) (q : Fin 215) : ℤ :=
  (DecimalMachine215.machine.transition q (Tape.read cfg.tape cfg.head)).move.apply cfg.head

def receiveTile (cfg : Config 215) (q : Fin 215) (x : ℤ) : Tile :=
  let a := WangTiles942.action (sourceIndex cfg q)
  let b := (Tape.read cfg.tape x).toNat
  ⟨a.2.1.toNat * rail a.2.1 a.2.2,b,(1-a.2.1.toNat)*rail a.2.1 a.2.2,
    WangTiles942.headColor a.2.2 b⟩

/-- An explicit whole-integer row; the live-state premise is used only by
its north/south interpretation, not by the construction itself. -/
def stepTile (cfg : Config 215) (q : Fin 215) (x : ℤ) : Tile :=
  if x = cfg.head then (transitionRow (sourceIndex cfg q)).2
  else if x = nextHead cfg q then receiveTile cfg q x
  else ⟨0,(Tape.read cfg.tape x).toNat,0,(Tape.read cfg.tape x).toNat⟩

theorem nextHead_ne (cfg : Config 215) (q : Fin 215) : nextHead cfg q ≠ cfg.head :=
  moved_head_ne _ _

theorem nextHead_eq (cfg : Config 215) (q : Fin 215) :
    nextHead cfg q = if (WangTiles942.action (sourceIndex cfg q)).2.1
      then cfg.head+1 else cfg.head-1 :=
  transition_moved_head q (Tape.read cfg.tape cfg.head) cfg.head

theorem stepTile_old_head (cfg : Config 215) (q : Fin 215) :
    stepTile cfg q cfg.head = (transitionRow (sourceIndex cfg q)).2 := by
  simp [stepTile]

theorem stepTile_new_head (cfg : Config 215) (q : Fin 215) :
    stepTile cfg q (nextHead cfg q) = receiveTile cfg q (nextHead cfg q) := by
  simp [stepTile, nextHead_ne]

theorem stepTile_elsewhere (cfg : Config 215) (q : Fin 215) (x : ℤ)
    (ho : x ≠ cfg.head) (hn : x ≠ nextHead cfg q) :
    stepTile cfg q x = ⟨0,(Tape.read cfg.tape x).toNat,0,(Tape.read cfg.tape x).toNat⟩ := by
  simp only [stepTile, if_neg ho, if_neg hn]

theorem receiveTile_allowed (cfg : Config 215) (q : Fin 215) (x : ℤ) :
    Allowed (receiveTile cfg q x) := by
  exact Allowed.receive _ _ (action_target_mem (sourceIndex cfg q))
    ⟨(Tape.read cfg.tape x).toNat, by have h := bit_le_one (Tape.read cfg.tape x); omega⟩

/-- Every constructed tile belongs to the actual finite table language. -/
theorem stepTile_allowed (cfg : Config 215) (q : Fin 215) (x : ℤ) :
    Allowed (stepTile cfg q x) := by
  by_cases ho : x = cfg.head
  · subst x
    rw [stepTile_old_head]
    exact Allowed.transition _
  · by_cases hn : x = nextHead cfg q
    · rw [stepTile, if_neg ho, if_pos hn]
      exact receiveTile_allowed cfg q x
    · rw [stepTile_elsewhere cfg q x ho hn]
      simpa only [Fin.val_zero, Nat.mul_zero, zero_add] using
        Allowed.pass (0 : Fin 2)
          ⟨(Tape.read cfg.tape x).toNat, by have h := bit_le_one (Tape.read cfg.tape x); omega⟩

/-- Exact north input, under only the live-state identification. -/
theorem stepTile_north (cfg : Config 215) (q : Fin 215)
    (hq : cfg.state = some q) (x : ℤ) : (stepTile cfg q x).north = color cfg x := by
  by_cases ho : x = cfg.head
  · subst x
    rw [stepTile_old_head, color_at_head, hq, operating_head_color]
    change WangTiles942.headColor ((WangMachineAction.inputIndex q _).val / 2)
      ((WangMachineAction.inputIndex q _).val % 2) = _
    rw [inputIndex_div_two, inputIndex_mod_two]
  · rw [color_of_ne_head cfg x ho]
    by_cases hn : x = nextHead cfg q
    · simp only [stepTile, if_neg ho, if_pos hn, receiveTile]
    · rw [stepTile_elsewhere cfg q x ho hn]

/-- Exact south output of the actual machine step, including entering halt. -/
theorem stepTile_south (cfg : Config 215) (q : Fin 215)
    (hq : cfg.state = some q) (x : ℤ) :
    (stepTile cfg q x).south = color (DecimalMachine215.machine.step cfg) x := by
  by_cases ho : x = cfg.head
  · subst x
    rw [stepTile_old_head, color_step_old_head _ cfg q hq, transition_write]
    rfl
  · by_cases hn : x = nextHead cfg q
    · subst x
      rw [stepTile_new_head]
      change WangTiles942.headColor _ _ = color (DecimalMachine215.machine.step cfg)
        ((DecimalMachine215.machine.transition q (Tape.read cfg.tape cfg.head)).move.apply cfg.head)
      rw [color_step_new_head _ cfg q hq, transition_headColor]
      rfl
    · rw [stepTile_elsewhere cfg q x ho hn,
        color_step_elsewhere _ cfg q hq x ho hn, color_of_ne_head cfg x ho]

/-- The only west signal is at the old head for left moves, or the new head for right moves. -/
theorem stepTile_west (cfg : Config 215) (q : Fin 215) (x : ℤ) :
    (stepTile cfg q x).west =
      if (WangTiles942.action (sourceIndex cfg q)).2.1 then
        if x = nextHead cfg q then rail true (WangTiles942.action (sourceIndex cfg q)).2.2 else 0
      else if x = cfg.head then rail false (WangTiles942.action (sourceIndex cfg q)).2.2 else 0 := by
  have hne := nextHead_ne cfg q
  by_cases ho : x = cfg.head <;> by_cases hn : x = nextHead cfg q <;>
    cases hd : (WangTiles942.action (sourceIndex cfg q)).2.1 <;>
    simp_all [stepTile, transitionRow, receiveTile]

/-- The only east signal is at the new head for left moves, or the old head for right moves. -/
theorem stepTile_east (cfg : Config 215) (q : Fin 215) (x : ℤ) :
    (stepTile cfg q x).east =
      if (WangTiles942.action (sourceIndex cfg q)).2.1 then
        if x = cfg.head then rail true (WangTiles942.action (sourceIndex cfg q)).2.2 else 0
      else if x = nextHead cfg q then rail false (WangTiles942.action (sourceIndex cfg q)).2.2 else 0 := by
  have hne := nextHead_ne cfg q
  by_cases ho : x = cfg.head <;> by_cases hn : x = nextHead cfg q <;>
    cases hd : (WangTiles942.action (sourceIndex cfg q)).2.1 <;>
    simp_all [stepTile, transitionRow, receiveTile]

/-- All horizontal edges match with the actual plane orientation. -/
theorem stepTile_horizontal (cfg : Config 215) (q : Fin 215) (x : ℤ) :
    (stepTile cfg q (x+1)).west = (stepTile cfg q x).east := by
  rw [stepTile_west, stepTile_east]
  have hn := nextHead_eq cfg q
  cases hd : (WangTiles942.action (sourceIndex cfg q)).2.1 <;>
    simp only [hd, Bool.false_eq_true, ↓reduceIte] at hn ⊢
  · have he : x+1 = cfg.head ↔ x = nextHead cfg q := by omega
    simp only [he]
  · have he : x+1 = nextHead cfg q ↔ x = cfg.head := by omega
    simp only [he]

/-- The constructed row realizes an actual operating step over every integer position. -/
theorem step_row (cfg : Config 215) (q : Fin 215) (hq : cfg.state = some q) :
    (∀ x : ℤ, Allowed (stepTile cfg q x)) ∧
    (∀ x : ℤ, (stepTile cfg q x).north = color cfg x) ∧
    (∀ x : ℤ, (stepTile cfg q x).south = color (DecimalMachine215.machine.step cfg) x) ∧
    (∀ x : ℤ, (stepTile cfg q (x+1)).west = (stepTile cfg q x).east) :=
  ⟨stepTile_allowed cfg q, stepTile_north cfg q hq, stepTile_south cfg q hq,
    stepTile_horizontal cfg q⟩

end DiophantineConsistency.WangTiles942StepConstruction
