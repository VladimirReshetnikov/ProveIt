import DiophantineConsistency.WangTiles942OperatingRow
import DiophantineConsistency.WangMachineAction
import DiophantineConsistency.WangMachineStep

/-!
# The actual stepped head remains strictly inside the strip

A transition's active rail has color at least6. The right wall's west
color is at most4 and the left wall's east color is at most2. Actual
horizontal matching therefore prevents either move from entering a wall.
The proof uses no absence-of-finish or time-matching premise.
-/

namespace DiophantineConsistency.WangTiles942HeadBounds

open SetTheory.BusyBeaver
open WangTiles942 WangTiles942Language WangTiles942RowEncoding
  WangTiles942StripGeometry WangTiles942OperatingRow

set_option Elab.async false
set_option maxRecDepth 10000

/-- The finite-bit tile index and Boolean machine index are the same. -/
theorem inputIndex_eq (q : Fin 215) (cfg : Config 215) (x : ℤ) :
    WangTiles942InputLanguage.inputIndex q (symbol cfg x) =
      WangMachineAction.inputIndex q (Tape.read cfg.tape x) := by
  apply Fin.ext
  rfl

theorem head_transition {T : ℤ → ℤ → Tile} {l r t : ℤ} {cfg : Config 215}
    (hA : ∀ x τ, Allowed (T x τ)) (h : RowEncodes T l r t cfg)
    (q : Fin 215) (hq : cfg.state = some q) :
    T cfg.head t =
      (transitionRow (WangMachineAction.inputIndex q (Tape.read cfg.tape cfg.head))).2 := by
  rw [operating_head_tile hA h q hq, inputIndex_eq]

theorem right_active_edge {T : ℤ → ℤ → Tile} {l r t : ℤ} {cfg : Config 215}
    (hA : ∀ x τ, Allowed (T x τ)) (h : RowEncodes T l r t cfg)
    (q : Fin 215) (hq : cfg.state = some q)
    (hd : (action (WangMachineAction.inputIndex q (Tape.read cfg.tape cfg.head))).2.1 = true) :
    6 ≤ (T cfg.head t).east := by
  rw [head_transition hA h q hq]
  have hr := (valid_rail_range (action_target_mem
    (WangMachineAction.inputIndex q (Tape.read cfg.tape cfg.head)))).1
  simp only [transitionRow, hd, Bool.toNat_true, Nat.one_mul] at *
  exact hr

theorem left_active_edge {T : ℤ → ℤ → Tile} {l r t : ℤ} {cfg : Config 215}
    (hA : ∀ x τ, Allowed (T x τ)) (h : RowEncodes T l r t cfg)
    (q : Fin 215) (hq : cfg.state = some q)
    (hd : (action (WangMachineAction.inputIndex q (Tape.read cfg.tape cfg.head))).2.1 = false) :
    6 ≤ (T cfg.head t).west := by
  rw [head_transition hA h q hq]
  have hr := (valid_rail_range (action_target_mem
    (WangMachineAction.inputIndex q (Tape.read cfg.tape cfg.head)))).1
  simp only [transitionRow, hd, Bool.toNat_false, Nat.sub_zero, Nat.one_mul] at *
  exact hr

theorem left_wall_east_le_two {T : ℤ → ℤ → Tile} {N L R : ℕ}
    (hs : PersistentStrip T N L R) (t : ℤ) : (T (-(L : ℤ)) t).east ≤ 2 := by
  obtain ⟨a,b,h⟩ := hs.left_wall t
  rw [h]
  exact Nat.le_of_lt_succ b.isLt

theorem right_wall_west_le_four {T : ℤ → ℤ → Tile} {N L R : ℕ}
    (hs : PersistentStrip T N L R) (t : ℤ) : (T (R : ℤ) t).west ≤ 4 := by
  obtain ⟨a,b,h⟩ := hs.right_wall t
  rw [h]
  exact Nat.pow_le_pow_left (Nat.le_of_lt_succ a.isLt) 2

theorem right_move_not_wall {T : ℤ → ℤ → Tile} {N L R : ℕ} {t : ℤ} {cfg : Config 215}
    (hA : ∀ x τ, Allowed (T x τ))
    (hH : ∀ x τ, (T (x+1) τ).west = (T x τ).east)
    (hs : PersistentStrip T N L R)
    (h : RowEncodes T (-(L : ℤ)) (R : ℤ) t cfg)
    (q : Fin 215) (hq : cfg.state = some q)
    (hd : (action (WangMachineAction.inputIndex q (Tape.read cfg.tape cfg.head))).2.1 = true) :
    cfg.head + 1 ≠ (R : ℤ) := by
  intro he
  have ha := right_active_edge hA h q hq hd
  have hw := right_wall_west_le_four hs t
  have hm := hH cfg.head t
  rw [he] at hm
  rw [hm] at hw
  omega

theorem left_move_not_wall {T : ℤ → ℤ → Tile} {N L R : ℕ} {t : ℤ} {cfg : Config 215}
    (hA : ∀ x τ, Allowed (T x τ))
    (hH : ∀ x τ, (T (x+1) τ).west = (T x τ).east)
    (hs : PersistentStrip T N L R)
    (h : RowEncodes T (-(L : ℤ)) (R : ℤ) t cfg)
    (q : Fin 215) (hq : cfg.state = some q)
    (hd : (action (WangMachineAction.inputIndex q (Tape.read cfg.tape cfg.head))).2.1 = false) :
    cfg.head - 1 ≠ -(L : ℤ) := by
  intro he
  have ha := left_active_edge hA h q hq hd
  have hw := left_wall_east_le_two hs t
  have hm := hH (cfg.head-1) t
  rw [sub_add_cancel, he] at hm
  rw [← hm] at hw
  omega

/-- The actual successor head, including a successor entering halt,
stays strictly between the existing persistent walls. -/
theorem next_head_inside {T : ℤ → ℤ → Tile} {N L R : ℕ} {t : ℤ} {cfg : Config 215}
    (hA : ∀ x τ, Allowed (T x τ))
    (hH : ∀ x τ, (T (x+1) τ).west = (T x τ).east)
    (hs : PersistentStrip T N L R)
    (h : RowEncodes T (-(L : ℤ)) (R : ℤ) t cfg)
    (q : Fin 215) (hq : cfg.state = some q) :
    -(L : ℤ) < (DecimalMachine215.machine.step cfg).head ∧
      (DecimalMachine215.machine.step cfg).head < (R : ℤ) := by
  have hm : (DecimalMachine215.machine.step cfg).head =
      if (action (WangMachineAction.inputIndex q (Tape.read cfg.tape cfg.head))).2.1
      then cfg.head + 1 else cfg.head - 1 := by
    rw [WangMachineStep.step_eq _ cfg q hq]
    exact WangMachineAction.transition_moved_head _ _ _
  have hl := h.head_left
  have hr := h.head_right
  cases hd : (action (WangMachineAction.inputIndex q (Tape.read cfg.tape cfg.head))).2.1 with
  | false =>
      have hn := left_move_not_wall hA hH hs h q hq hd
      simp only [hd, Bool.false_eq_true, if_false] at hm
      omega
  | true =>
      have hn := right_move_not_wall hA hH hs h q hq hd
      simp only [hd, if_true] at hm
      omega

end DiophantineConsistency.WangTiles942HeadBounds
