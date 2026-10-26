import DiophantineConsistency.WangMachineStep

/-! Direction, write/erase, entering-halt, and unchanged-cell checks for
the actual operational three-way color formula. -/

namespace DiophantineConsistency.WangMachineStepChecks

open SetTheory.BusyBeaver WangMachineEncoding WangMachineStep

set_option Elab.async false
set_option maxRecDepth 10000

example (p : ℤ) : Move.left.apply p = p - 1 := rfl
example (p : ℤ) : Move.right.apply p = p + 1 := rfl

example (m : Move) (p : ℤ) : m.apply p ≠ p := moved_head_ne m p

example (tape : Tape) (p : ℤ) (a : Action 215) :
    Tape.read (Tape.write tape p a.write) (a.move.apply p) =
      Tape.read tape (a.move.apply p) := read_written_at_moved tape p a

example (M : Machine 215) (cfg : Config 215) (q : Fin 215) (hq : cfg.state = some q)
    (x : ℤ) :
    let a := M.transition q (Tape.read cfg.tape cfg.head)
    color (M.step cfg) x =
      if x = a.move.apply cfg.head then headColor a.next (Tape.read cfg.tape x)
      else if x = cfg.head then a.write.toNat else color cfg x :=
  color_step M cfg q hq x

example (M : Machine 215) (cfg : Config 215) (q : Fin 215) (hq : cfg.state = some q) :
    Tape.read (M.step cfg).tape (M.step cfg).head =
      Tape.read cfg.tape (M.step cfg).head := step_read_at_new_head M cfg q hq

private def sample : Config 215 where
  state := some 0
  head := 0
  tape := [-1, 0, 1, 7]

private def leftErase : Machine 215 where
  transition _ _ := { write := false, move := Move.left, next := some 7 }

private def rightWriteHalt : Machine 215 where
  transition _ _ := { write := true, move := Move.right, next := none }

/-- Leftward erasure changes only the written cell and the new head color. -/
example : color (leftErase.step sample) (-1) = 17 := rfl
example : color (leftErase.step sample) 0 = 0 := rfl
example : color (leftErase.step sample) 1 = 1 := rfl
example : color (leftErase.step sample) 7 = 1 := rfl

/-- The old head had color3 and must lose it after movement. -/
example : color (leftErase.step sample) 0 ≠ color sample 0 := by decide

/-- Rightward entry into halt retains the written bit and moved head. -/
example : color (rightWriteHalt.step sample) 1 = 433 := rfl
example : color (rightWriteHalt.step sample) 0 = 1 := rfl
example : color (rightWriteHalt.step sample) (-1) = 1 := rfl
example : color (rightWriteHalt.step sample) 7 = 1 := rfl

example : color (rightWriteHalt.step sample) 0 ≠ 433 := by decide

/-- With a blank destination, the same entering-halt action yields432. -/
example : color (rightWriteHalt.step (initial 215)) 1 = 432 := rfl
example : color (rightWriteHalt.step (initial 215)) 0 = 1 := rfl

example (M : Machine 215) (cfg : Config 215) (q : Fin 215) (hq : cfg.state = some q)
    (hh : (M.transition q (Tape.read cfg.tape cfg.head)).next = none) :
    let a := M.transition q (Tape.read cfg.tape cfg.head)
    color (M.step cfg) (a.move.apply cfg.head) =
      432 + (Tape.read cfg.tape (a.move.apply cfg.head)).toNat :=
  color_step_enter_halt M cfg q hq hh

#print axioms moved_head_left_or_right
#print axioms moved_head_ne
#print axioms read_written_at_moved
#print axioms step_eq
#print axioms step_head_left_or_right
#print axioms step_head_ne
#print axioms step_read_at_new_head
#print axioms color_action
#print axioms color_step
#print axioms color_step_new_head
#print axioms color_step_old_head
#print axioms color_step_elsewhere
#print axioms color_step_enter_halt

end DiophantineConsistency.WangMachineStepChecks
