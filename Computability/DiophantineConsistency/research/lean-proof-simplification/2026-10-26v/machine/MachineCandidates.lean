import DiophantineConsistency.WangMachineAction
import DiophantineConsistency.WangMachineStep
import DiophantineConsistency.WangMachineTraceBounds

/-!
Uncompiled source-exact candidates for ProveIt commit
22e020937caa81d0cb72a4f63071d6c0bcc1eba9.
The three imported original target theorems are NEVER used in their replacements.
Only earlier independently proved helpers are used. No new assumptions or axioms.
-/
namespace DiophantineConsistency.Round3MachineCandidates

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open WangMachineEncoding WangMachineAction WangMachineStep WangMachineTraceBounds

theorem act_next_none_iff_candidate (a : Bool × Bool × ℕ) (ha : a.2.2 < 216) :
    (KDense215.act a).next = none ↔ a.2.2 = 215 := by
  rw [← stateNumber_injective.eq_iff, act_stateNumber a ha, stateNumber_none]

theorem color_action_candidate (cfg : Config 215) (a : Action 215) (x : ℤ) :
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

theorem run_read_of_abs_ge_candidate {n : ℕ} (M : Machine n) (t : ℕ) (x : ℤ)
    (hx : (t : ℤ) ≤ |x|) : Tape.read (M.run t).tape x = false := by
  exact run_read_outside M t x (le_abs'.mp hx)

-- The target<216 guard is material, not decorative.
example : (KDense215.act (false, false, 215)).next = none :=
  (act_next_none_iff_candidate _ (by decide)).mpr rfl

example : stateNumber (KDense215.act (false, false, 216)).next ≠ 216 := by decide

-- Old/new-head projections remain consequences of the same three-way formula.
example (cfg : Config 215) (a : Action 215) :
    color ({state := a.next, head := a.move.apply cfg.head,
      tape := Tape.write cfg.tape cfg.head a.write} : Config 215) cfg.head =
      a.write.toNat := by
  simpa only [if_neg (moved_head_ne a.move cfg.head).symm, if_pos rfl] using
    color_action_candidate cfg a cfg.head

example (cfg : Config 215) (a : Action 215) :
    color ({state := a.next, head := a.move.apply cfg.head,
      tape := Tape.write cfg.tape cfg.head a.write} : Config 215)
        (a.move.apply cfg.head) =
      headColor a.next (Tape.read cfg.tape (a.move.apply cfg.head)) := by
  simpa only [if_pos rfl] using
    color_action_candidate cfg a (a.move.apply cfg.head)

-- In particular, time zero retains every integer position, not only nonzero x.
example {n : ℕ} (M : Machine n) (x : ℤ) : Tape.read (M.run 0).tape x = false :=
  run_read_of_abs_ge_candidate M 0 x (abs_nonneg x)

end DiophantineConsistency.Round3MachineCandidates

#print axioms DiophantineConsistency.Round3MachineCandidates.act_next_none_iff_candidate
#print axioms DiophantineConsistency.Round3MachineCandidates.color_action_candidate
#print axioms DiophantineConsistency.Round3MachineCandidates.run_read_of_abs_ge_candidate
