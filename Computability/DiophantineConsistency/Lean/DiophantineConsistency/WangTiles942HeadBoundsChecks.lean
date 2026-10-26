import DiophantineConsistency.WangTiles942HeadBounds

/-! The next-head result uses only allowedness, horizontal matching,
the existing strip and live row encoding; no time or no-finish premise. -/

namespace DiophantineConsistency.WangTiles942HeadBoundsChecks

open SetTheory.BusyBeaver
open WangTiles942 WangTiles942Language WangTiles942RowEncoding
  WangTiles942StripGeometry WangTiles942HeadBounds

set_option Elab.async false
set_option maxRecDepth 10000

variable {T : ℤ → ℤ → Tile} {N L R : ℕ} {t : ℤ} {cfg : Config 215}

example (q : Fin 215) (x : ℤ) :
    WangTiles942InputLanguage.inputIndex q (WangTiles942OperatingRow.symbol cfg x) =
      WangMachineAction.inputIndex q (Tape.read cfg.tape x) := inputIndex_eq q cfg x

example (hs : PersistentStrip T N L R) :
    (T (-(L : ℤ)) t).east ≤ 2 ∧ (T (R : ℤ) t).west ≤ 4 :=
  ⟨left_wall_east_le_two hs t, right_wall_west_le_four hs t⟩

example (hA : ∀ x τ, Allowed (T x τ))
    (hH : ∀ x τ, (T (x+1) τ).west = (T x τ).east)
    (hs : PersistentStrip T N L R)
    (h : RowEncodes T (-(L : ℤ)) (R : ℤ) t cfg)
    (q : Fin 215) (hq : cfg.state = some q) :
    -(L : ℤ) < (DecimalMachine215.machine.step cfg).head ∧
      (DecimalMachine215.machine.step cfg).head < (R : ℤ) :=
  next_head_inside hA hH hs h q hq

example (hA : ∀ x τ, Allowed (T x τ))
    (hH : ∀ x τ, (T (x+1) τ).west = (T x τ).east)
    (hs : PersistentStrip T N L R)
    (h : RowEncodes T (-(L : ℤ)) (R : ℤ) t cfg)
    (q : Fin 215) (hq : cfg.state = some q)
    (hd : (action (WangMachineAction.inputIndex q (Tape.read cfg.tape cfg.head))).2.1 = true) :
    cfg.head + 1 ≠ (R : ℤ) := right_move_not_wall hA hH hs h q hq hd

example (hA : ∀ x τ, Allowed (T x τ))
    (hH : ∀ x τ, (T (x+1) τ).west = (T x τ).east)
    (hs : PersistentStrip T N L R)
    (h : RowEncodes T (-(L : ℤ)) (R : ℤ) t cfg)
    (q : Fin 215) (hq : cfg.state = some q)
    (hd : (action (WangMachineAction.inputIndex q (Tape.read cfg.tape cfg.head))).2.1 = false) :
    cfg.head - 1 ≠ -(L : ℤ) := left_move_not_wall hA hH hs h q hq hd

/-- Direction is essential: the first actual right-moving transition has
zero West edge, so no claim that both transition edges exceed the seams is valid. -/
example : (transitionRow 0).2.west = 0 := by
  simp [transitionRow, actual_first_action]

example (a : Fin 3) (r : ℕ) (hr : 6 ≤ r) : r ≠ a.val^2 := by
  have ha := a.isLt
  have hc : a.val = 0 ∨ a.val = 1 ∨ a.val = 2 := by omega
  rcases hc with he | he | he <;> rw [he] <;> norm_num <;> omega

example (b : Fin 3) (r : ℕ) (hr : 6 ≤ r) : r ≠ b.val := by
  have hb := b.isLt
  omega

#print axioms inputIndex_eq
#print axioms head_transition
#print axioms right_active_edge
#print axioms left_active_edge
#print axioms left_wall_east_le_two
#print axioms right_wall_west_le_four
#print axioms right_move_not_wall
#print axioms left_move_not_wall
#print axioms next_head_inside

end DiophantineConsistency.WangTiles942HeadBoundsChecks
