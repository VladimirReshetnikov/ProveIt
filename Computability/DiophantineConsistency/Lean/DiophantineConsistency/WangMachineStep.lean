import DiophantineConsistency.WangMachineEncoding

/-!
# Actual operational step in vertical colors

A live-state action writes at the old head and moves exactly one cell.
The destination therefore reads its old tape bit. Its new head color uses
the action's actual optional next state, including entry into halt.
No tile-row, run-calibration, or consistency premise is used.
-/

namespace DiophantineConsistency.WangMachineStep

open SetTheory.BusyBeaver WangMachineEncoding

set_option Elab.async false
set_option maxRecDepth 10000

theorem moved_head_left_or_right (m : Move) (p : ℤ) :
    m.apply p = p - 1 ∨ m.apply p = p + 1 := by
  cases m with
  | left => exact Or.inl rfl
  | right => exact Or.inr rfl

theorem moved_head_ne (m : Move) (p : ℤ) : m.apply p ≠ p := by
  rcases moved_head_left_or_right m p with h | h <;> omega

/-- Writing at the old head cannot change the bit at the moved head. -/
theorem read_written_at_moved (tape : Tape) (p : ℤ) (a : Action 215) :
    Tape.read (Tape.write tape p a.write) (a.move.apply p) =
      Tape.read tape (a.move.apply p) :=
  Tape.read_write_of_ne tape (moved_head_ne a.move p) a.write

/-- This is the actual record returned by `Machine.step` at a live state.
No assumption on `next` is made. -/
theorem step_eq (M : Machine 215) (cfg : Config 215) (q : Fin 215)
    (hq : cfg.state = some q) :
    M.step cfg =
      let a := M.transition q (Tape.read cfg.tape cfg.head)
      { state := a.next, head := a.move.apply cfg.head,
        tape := Tape.write cfg.tape cfg.head a.write } := by
  simp only [Machine.step, hq]

theorem step_head_left_or_right (M : Machine 215) (cfg : Config 215) (q : Fin 215)
    (hq : cfg.state = some q) :
    (M.step cfg).head = cfg.head - 1 ∨ (M.step cfg).head = cfg.head + 1 := by
  rw [step_eq M cfg q hq]
  exact moved_head_left_or_right _ _

theorem step_head_ne (M : Machine 215) (cfg : Config 215) (q : Fin 215)
    (hq : cfg.state = some q) : (M.step cfg).head ≠ cfg.head := by
  rcases step_head_left_or_right M cfg q hq with h | h <;> omega

theorem step_read_at_new_head (M : Machine 215) (cfg : Config 215) (q : Fin 215)
    (hq : cfg.state = some q) :
    Tape.read (M.step cfg).tape (M.step cfg).head =
      Tape.read cfg.tape (M.step cfg).head := by
  rw [step_eq M cfg q hq]
  exact read_written_at_moved _ _ _

/-- The exact three-way color update for an arbitrary action record. -/
theorem color_action (cfg : Config 215) (a : Action 215) (x : ℤ) :
    color
      ({ state := a.next
         head := a.move.apply cfg.head
         tape := Tape.write cfg.tape cfg.head a.write } : Config 215) x =
      if x = a.move.apply cfg.head then headColor a.next (Tape.read cfg.tape x)
      else if x = cfg.head then a.write.toNat else color cfg x := by
  by_cases ho : x = cfg.head
  · subst x
    simp [color, (moved_head_ne a.move cfg.head).symm]
  · simp [color, ho, Tape.read_write_of_ne cfg.tape ho a.write]

/-- The complete actual machine-step formula. The head branch uses
`a.next` even when it is `none`; writing and movement have already occurred. -/
theorem color_step (M : Machine 215) (cfg : Config 215) (q : Fin 215)
    (hq : cfg.state = some q) (x : ℤ) :
    let a := M.transition q (Tape.read cfg.tape cfg.head)
    color (M.step cfg) x =
      if x = a.move.apply cfg.head then headColor a.next (Tape.read cfg.tape x)
      else if x = cfg.head then a.write.toNat else color cfg x := by
  dsimp only
  rw [step_eq M cfg q hq]
  exact color_action cfg _ x

theorem color_step_new_head (M : Machine 215) (cfg : Config 215) (q : Fin 215)
    (hq : cfg.state = some q) :
    let a := M.transition q (Tape.read cfg.tape cfg.head)
    color (M.step cfg) (a.move.apply cfg.head) =
      headColor a.next (Tape.read cfg.tape (a.move.apply cfg.head)) := by
  dsimp only
  rw [color_step M cfg q hq]
  simp

theorem color_step_old_head (M : Machine 215) (cfg : Config 215) (q : Fin 215)
    (hq : cfg.state = some q) :
    color (M.step cfg) cfg.head =
      (M.transition q (Tape.read cfg.tape cfg.head)).write.toNat := by
  rw [color_step M cfg q hq]
  have hn := (moved_head_ne
    (M.transition q (Tape.read cfg.tape cfg.head)).move cfg.head).symm
  simp [hn]

theorem color_step_elsewhere (M : Machine 215) (cfg : Config 215) (q : Fin 215)
    (hq : cfg.state = some q) (x : ℤ) (ho : x ≠ cfg.head)
    (hn : x ≠ (M.transition q (Tape.read cfg.tape cfg.head)).move.apply cfg.head) :
    color (M.step cfg) x = color cfg x := by
  rw [color_step M cfg q hq]
  simp only [if_neg hn, if_neg ho]

/-- Explicit entering-halt specialization, using the destination's old bit. -/
theorem color_step_enter_halt (M : Machine 215) (cfg : Config 215) (q : Fin 215)
    (hq : cfg.state = some q)
    (hh : (M.transition q (Tape.read cfg.tape cfg.head)).next = none) :
    let a := M.transition q (Tape.read cfg.tape cfg.head)
    color (M.step cfg) (a.move.apply cfg.head) =
      432 + (Tape.read cfg.tape (a.move.apply cfg.head)).toNat := by
  dsimp only
  rw [color_step_new_head M cfg q hq, hh, halted_head_color]

end DiophantineConsistency.WangMachineStep
