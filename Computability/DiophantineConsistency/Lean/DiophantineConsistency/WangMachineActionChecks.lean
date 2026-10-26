import DiophantineConsistency.WangMachineAction
import DiophantineConsistency.WangMachineStep

/-! Actual input indexing, target-state and action-color binding checks.
The only concrete target computation is over the proved small action cache. -/

namespace DiophantineConsistency.WangMachineActionChecks

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open WangMachineEncoding WangMachineAction

set_option Elab.async false
set_option maxRecDepth 10000

example : (inputIndex (0 : Fin 215) false).val = 0 := rfl
example : (inputIndex (214 : Fin 215) true).val = 429 := rfl

example (q : Fin 215) (b : Bool) : (inputIndex q b).val / 2 = q.val :=
  inputIndex_div_two q b

example (q : Fin 215) (b : Bool) : (inputIndex q b).val % 2 = b.toNat :=
  inputIndex_mod_two q b

example (q : Fin 215) (b : Bool) :
    (inputIndex q b).val + 2 = WangTiles942.headColor q.val b.toNat := inputIndex_north q b

example (q : Fin 215) (b : Bool) :
    DecimalMachine215.machine.transition q b =
      KDense215.act (WangTiles942.action (inputIndex q b)) := transition_eq_cached q b

example (q : Fin 215) (b : Bool) :
    (DecimalMachine215.machine.transition q b).write =
      (WangTiles942.action (inputIndex q b)).1 := transition_write q b

example (q : Fin 215) (b : Bool) :
    (DecimalMachine215.machine.transition q b).move =
      if (WangTiles942.action (inputIndex q b)).2.1 then Move.right else Move.left :=
  transition_move q b

example (q : Fin 215) (b : Bool) :
    stateNumber (DecimalMachine215.machine.transition q b).next =
      (WangTiles942.action (inputIndex q b)).2.2 := transition_stateNumber q b

example (q : Fin 215) (b c : Bool) :
    headColor (DecimalMachine215.machine.transition q b).next c =
      WangTiles942.headColor (WangTiles942.action (inputIndex q b)).2.2 c.toNat :=
  transition_headColor q b c

/-- The exact target bound is essential: the raw action convention would
also collapse an invalid216 to halt, and would not preserve its number. -/
example : stateNumber (KDense215.act (false, false, 216)).next ≠ 216 := by decide

example : stateNumber (KDense215.act (false, false, 215)).next = 215 :=
  act_stateNumber _ (by decide)

example : stateNumber (KDense215.act (true, true, 214)).next = 214 :=
  act_stateNumber _ (by decide)

private theorem cached_halt_125 :
    (WangTiles942.action (inputIndex (62 : Fin 215) true)).2.2 = 215 := by
  decide +kernel

/-- The actual early halting action is bound without evaluating its decimal decode. -/
example : (DecimalMachine215.machine.transition (62 : Fin 215) true).next = none :=
  (transition_next_none_iff _ _).mpr cached_halt_125

example (c : Bool) :
    headColor (DecimalMachine215.machine.transition (62 : Fin 215) true).next c =
      432 + c.toNat := by
  rw [(transition_next_none_iff _ _).mpr cached_halt_125, halted_head_color]

/-- Composition with the generic operational step uses the original
destination bit and the exact literal action target. -/
example (cfg : Config 215) (q : Fin 215) (hq : cfg.state = some q) :
    let b := Tape.read cfg.tape cfg.head
    let a := DecimalMachine215.machine.transition q b
    color (DecimalMachine215.machine.step cfg) (a.move.apply cfg.head) =
      WangTiles942.headColor (WangTiles942.action (inputIndex q b)).2.2
        (Tape.read cfg.tape (a.move.apply cfg.head)).toNat := by
  dsimp only
  rw [WangMachineStep.color_step_new_head _ cfg q hq]
  exact transition_headColor _ _ _

#print axioms inputIndex_div_two
#print axioms inputIndex_mod_two
#print axioms inputIndex_north
#print axioms action_target_lt
#print axioms act_stateNumber
#print axioms act_next_none_iff
#print axioms transition_eq_cached
#print axioms transition_write
#print axioms transition_move
#print axioms transition_moved_head
#print axioms transition_stateNumber
#print axioms transition_next_none_iff
#print axioms transition_headColor

end DiophantineConsistency.WangMachineActionChecks
