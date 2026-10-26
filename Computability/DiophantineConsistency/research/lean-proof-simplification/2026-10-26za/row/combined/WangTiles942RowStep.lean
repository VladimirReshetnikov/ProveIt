import DiophantineConsistency.WangTiles942HeadBounds
import DiophantineConsistency.WangTiles942Signals
import DiophantineConsistency.WangTiles942StepConstruction

/-!
# Actual machine steps in the derived Wang strip

The operating head writes, its adjacent receiver gets the exact next head
color, and every other interior tile passes its old bit. Signals cannot
appear between two plain inputs or enter from a seam wall. Absence of a
finish row is derived from the operating head, never supplied as a premise.
-/

namespace DiophantineConsistency.WangTiles942RowStep

open SetTheory.BusyBeaver
open WangTiles942 WangTiles942Language WangTiles942Signals WangTiles942RowEncoding
  WangTiles942StripGeometry WangTiles942OperatingRow WangTiles942HeadBounds
open WangTiles942StepConstruction

set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

variable {T : ℤ → ℤ → Tile} {N L R : ℕ} {t : ℤ} {cfg : Config 215}

/-- At the old head the forced transition writes the actual machine bit. -/
theorem head_south
    (hA : ∀ x τ, Allowed (T x τ))
    (hrow : RowEncodes T (-(L : ℤ)) (R : ℤ) t cfg)
    (q : Fin 215) (hq : cfg.state = some q) :
    (T cfg.head t).south =
      (DecimalMachine215.machine.transition q (Tape.read cfg.tape cfg.head)).write.toNat := by
  rw [head_transition hA hrow q hq, WangMachineAction.transition_write]
  rfl

/-- A receive tile in a live encoded row is caused by its actual head.
No temporal matching or exclusion of finishes is needed. -/
theorem receive_at_next_head
    (hA : ∀ x τ, Allowed (T x τ))
    (hH : ∀ x τ, (T (x+1) τ).west = (T x τ).east)
    (hs : PersistentStrip T N L R)
    (hrow : RowEncodes T (-(L : ℤ)) (R : ℤ) t cfg)
    (q : Fin 215) (hq : cfg.state = some q)
    (x : ℤ) (hl : -(L : ℤ) < x) (hr : x < (R : ℤ))
    (d : Bool) (p : ℕ) (hp : p ∈ targets d) (b : Fin 2)
    (ht : T x t = ⟨d.toNat * rail d p,b.val,
      (1-d.toNat) * rail d p,headColor p b.val⟩) :
    x = (DecimalMachine215.machine.transition q
      (Tape.read cfg.tape cfg.head)).move.apply cfg.head := by
  have hpos := (valid_rail_range hp).1
  have hnorth : (T x t).north = b.val := congrArg Tile.north ht
  have hhead := head_transition hA hrow q hq
  have hmove := WangMachineAction.transition_moved_head q
    (Tape.read cfg.tape cfg.head) cfg.head
  cases d with
  | false =>
      have he : (T x t).east = rail false p := by
        simpa only [Bool.toNat_false, Nat.sub_zero, Nat.one_mul] using congrArg Tile.east ht
      have hm := hH x t
      have hnbr : x+1 = cfg.head := by
        by_contra hh
        by_cases hb : x+1 = (R : ℤ)
        · have hw := right_wall_west_le_four hs t
          rw [hb] at hm
          omega
        · have hz := plain_pair_edge_zero (hA x t) (hA (x+1) t)
            b (symbol cfg (x+1)) hnorth
            (hrow.plain (x+1) (by omega) (by omega) hh) hm.symm
          omega
      rw [hnbr, hhead, he] at hm
      cases hd : (action (WangMachineAction.inputIndex q
          (Tape.read cfg.tape cfg.head))).2.1 with
      | false => simp only [hd, Bool.false_eq_true, if_false] at hmove; omega
      | true =>
          simp only [transitionRow, hd, Bool.toNat_true, Nat.sub_self, Nat.zero_mul] at hm
          omega
  | true =>
      have hw : (T x t).west = rail true p := by
        simpa only [Bool.toNat_true, Nat.one_mul] using congrArg Tile.west ht
      have hm := hH (x-1) t
      rw [sub_add_cancel] at hm
      have hnbr : x-1 = cfg.head := by
        by_contra hh
        by_cases hb : x-1 = -(L : ℤ)
        · have he := left_wall_east_le_two hs t
          rw [hb] at hm
          omega
        · have hz := plain_pair_edge_zero (hA (x-1) t) (hA x t)
            (symbol cfg (x-1)) b
            (hrow.plain (x-1) (by omega) (by omega) hh) hnorth hm.symm
          omega
      rw [hnbr, hhead, hw] at hm
      cases hd : (action (WangMachineAction.inputIndex q
          (Tape.read cfg.tape cfg.head))).2.1 with
      | false =>
          simp only [transitionRow, hd, Bool.toNat_false, Nat.zero_mul] at hm
          omega
      | true => simp only [hd, if_true] at hmove; omega

/-- Before using time matching, an unchanged plain cell may still finish.
The only excluded local alternative is a causally impossible receiver. -/
theorem far_pass_or_finish
    (hA : ∀ x τ, Allowed (T x τ))
    (hH : ∀ x τ, (T (x+1) τ).west = (T x τ).east)
    (hs : PersistentStrip T N L R)
    (hrow : RowEncodes T (-(L : ℤ)) (R : ℤ) t cfg)
    (q : Fin 215) (hq : cfg.state = some q)
    (x : ℤ) (hl : -(L : ℤ) < x) (hr : x < (R : ℤ))
    (ho : x ≠ cfg.head)
    (hn : x ≠ (DecimalMachine215.machine.transition q
      (Tape.read cfg.tape cfg.head)).move.apply cfg.head) :
    T x t = ⟨0,(Tape.read cfg.tape x).toNat,0,(Tape.read cfg.tape x).toNat⟩ ∨
      T x t = ⟨0,(Tape.read cfg.tape x).toNat,0,438⟩ := by
  have hp : (T x t).north = (symbol cfg x).val := hrow.plain x hl hr ho
  rcases (WangTiles942InputLanguage.north_plain_iff (hA x t) (symbol cfg x)).mp hp with
    hp | hf | ⟨d,p,hp,ht⟩
  · exact Or.inl hp
  · exact Or.inr hf
  · exact False.elim (hn (receive_at_next_head hA hH hs hrow q hq x hl hr
      d p hp (symbol cfg x) ht))

/-- A plain cell distinct from the receiving head has no incoming west
signal. Its left neighbor is a wall, another plain cell, or the inactive
side of the one actual transition. -/
theorem far_west_zero
    (hA : ∀ x τ, Allowed (T x τ))
    (hH : ∀ x τ, (T (x+1) τ).west = (T x τ).east)
    (hs : PersistentStrip T N L R)
    (hrow : RowEncodes T (-(L : ℤ)) (R : ℤ) t cfg)
    (q : Fin 215) (hq : cfg.state = some q)
    (x : ℤ) (hl : -(L : ℤ) < x) (hr : x < (R : ℤ))
    (ho : x ≠ cfg.head)
    (hn : x ≠ (DecimalMachine215.machine.transition q
      (Tape.read cfg.tape cfg.head)).move.apply cfg.head) : (T x t).west = 0 := by
  rcases far_pass_or_finish hA hH hs hrow q hq x hl hr ho hn with h | h <;>
    exact congrArg Tile.west h

/-- Symmetric exclusion of an outgoing east signal at an unchanged cell,
including the actual right wall and the transition's inactive side. -/
theorem far_east_zero
    (hA : ∀ x τ, Allowed (T x τ))
    (hH : ∀ x τ, (T (x+1) τ).west = (T x τ).east)
    (hs : PersistentStrip T N L R)
    (hrow : RowEncodes T (-(L : ℤ)) (R : ℤ) t cfg)
    (q : Fin 215) (hq : cfg.state = some q)
    (x : ℤ) (hl : -(L : ℤ) < x) (hr : x < (R : ℤ))
    (ho : x ≠ cfg.head)
    (hn : x ≠ (DecimalMachine215.machine.transition q
      (Tape.read cfg.tape cfg.head)).move.apply cfg.head) : (T x t).east = 0 := by
  rcases far_pass_or_finish hA hH hs hrow q hq x hl hr ho hn with h | h <;>
    exact congrArg Tile.east h

/-- Both zero edges and the independently derived no-finish theorem force
the complete pass tuple at every unchanged tape position. -/
theorem far_pass
    (hA : ∀ x τ, Allowed (T x τ))
    (hH : ∀ x τ, (T (x+1) τ).west = (T x τ).east)
    (hTime : ∀ x τ, (T x (τ+1)).north = (T x τ).south)
    (hs : PersistentStrip T N L R)
    (hrow : RowEncodes T (-(L : ℤ)) (R : ℤ) t cfg)
    (q : Fin 215) (hq : cfg.state = some q)
    (x : ℤ) (hl : -(L : ℤ) < x) (hr : x < (R : ℤ))
    (ho : x ≠ cfg.head)
    (hn : x ≠ (DecimalMachine215.machine.transition q
      (Tape.read cfg.tape cfg.head)).move.apply cfg.head) :
    T x t = ⟨0,(Tape.read cfg.tape x).toNat,0,(Tape.read cfg.tape x).toNat⟩ := by
  rcases far_pass_or_finish hA hH hs hrow q hq x hl hr ho hn with hp | hf
  · exact hp
  · exact False.elim (no_south438 hA hH hTime hs hrow q hq x hl hr
      (congrArg Tile.south hf))

/-- Retain the complete receiver equality instead of discarding three edges.
The action may enter halt; target215 and arbitrary destination bits remain. -/
theorem receiver_tile
    (hA : ∀ x τ, Allowed (T x τ))
    (hH : ∀ x τ, (T (x+1) τ).west = (T x τ).east)
    (hrow : RowEncodes T (-(L : ℤ)) (R : ℤ) t cfg)
    (q : Fin 215) (hq : cfg.state = some q)
    (x : ℤ) (hl : -(L : ℤ) < x) (hr : x < (R : ℤ))
    (hx : x = (DecimalMachine215.machine.transition q
      (Tape.read cfg.tape cfg.head)).move.apply cfg.head) :
    T x t = receiveTile cfg q x := by
  have ho : x ≠ cfg.head := hx ▸ WangMachineStep.moved_head_ne _ _
  have hp : (T x t).north = (symbol cfg x).val := hrow.plain x hl hr ho
  have hh := head_transition hA hrow q hq
  have hmove := WangMachineAction.transition_moved_head q
    (Tape.read cfg.tape cfg.head) cfg.head
  cases hd : (action (WangMachineAction.inputIndex q
      (Tape.read cfg.tape cfg.head))).2.1 with
  | false =>
      simp only [hd, Bool.false_eq_true, if_false] at hmove
      have he : x+1 = cfg.head := by omega
      have hm := hH x t
      rw [he, hh] at hm
      have hrx := left_transition_receiver
        (WangMachineAction.inputIndex q (Tape.read cfg.tape cfg.head)) hd
        (hA x t) (symbol cfg x) hp hm.symm
      simpa [receiveTile, sourceIndex, hd, symbol] using hrx
  | true =>
      simp only [hd, if_true] at hmove
      have he : cfg.head+1 = x := by omega
      have hm := hH cfg.head t
      rw [he, hh] at hm
      have hrx := right_transition_receiver
        (WangMachineAction.inputIndex q (Tape.read cfg.tape cfg.head)) hd
        (hA x t) (symbol cfg x) hp hm.symm
      simpa [receiveTile, sourceIndex, hd, symbol] using hrx

/-- The adjacent receiver uses the exact action target and the original
destination bit. The action may enter halt; target215 is not excluded. -/
theorem receiver_south
    (hA : ∀ x τ, Allowed (T x τ))
    (hH : ∀ x τ, (T (x+1) τ).west = (T x τ).east)
    (hrow : RowEncodes T (-(L : ℤ)) (R : ℤ) t cfg)
    (q : Fin 215) (hq : cfg.state = some q)
    (x : ℤ) (hl : -(L : ℤ) < x) (hr : x < (R : ℤ))
    (hx : x = (DecimalMachine215.machine.transition q
      (Tape.read cfg.tape cfg.head)).move.apply cfg.head) :
    (T x t).south = WangMachineEncoding.headColor
      (DecimalMachine215.machine.transition q (Tape.read cfg.tape cfg.head)).next
      (Tape.read cfg.tape x) := by
  rw [receiver_tile hA hH hrow q hq x hl hr hx]
  change WangTiles942.headColor (action (sourceIndex cfg q)).2.2
    (Tape.read cfg.tape x).toNat = _
  rw [WangMachineAction.transition_headColor]
  rfl

/-- Forward extraction agrees with the independently constructed reverse row,
on the actual open strip. This asserts complete tiles, not only south colors. -/
theorem row_tile_eq_stepTile
    (hA : ∀ x τ, Allowed (T x τ))
    (hH : ∀ x τ, (T (x+1) τ).west = (T x τ).east)
    (hTime : ∀ x τ, (T x (τ+1)).north = (T x τ).south)
    (hs : PersistentStrip T N L R)
    (hrow : RowEncodes T (-(L : ℤ)) (R : ℤ) t cfg)
    (q : Fin 215) (hq : cfg.state = some q)
    (x : ℤ) (hl : -(L : ℤ) < x) (hr : x < (R : ℤ)) :
    T x t = stepTile cfg q x := by
  by_cases ho : x = cfg.head
  · subst x
    rw [stepTile_old_head]
    exact head_transition hA hrow q hq
  · by_cases hn : x = nextHead cfg q
    · rw [stepTile, if_neg ho, if_pos hn]
      exact receiver_tile hA hH hrow q hq x hl hr hn
    · rw [stepTile_elsewhere cfg q x ho hn]
      exact far_pass hA hH hTime hs hrow q hq x hl hr ho hn

/-- The operational south profile is now a projection of canonical row equality. -/
theorem south_step
    (hA : ∀ x τ, Allowed (T x τ))
    (hH : ∀ x τ, (T (x+1) τ).west = (T x τ).east)
    (hTime : ∀ x τ, (T x (τ+1)).north = (T x τ).south)
    (hs : PersistentStrip T N L R)
    (hrow : RowEncodes T (-(L : ℤ)) (R : ℤ) t cfg)
    (q : Fin 215) (hq : cfg.state = some q)
    (x : ℤ) (hl : -(L : ℤ) < x) (hr : x < (R : ℤ)) :
    (T x t).south = WangMachineEncoding.color (DecimalMachine215.machine.step cfg) x := by
  exact (congrArg Tile.south (row_tile_eq_stepTile hA hH hTime hs hrow q hq x hl hr)).trans
    (stepTile_south cfg q hq x)

/-- Actual marked-strip row evolution. All native geometry and absence of
finishes are derived through the frozen component theorems; only actual
tile matching, persistent walls, an encoded row and a live state enter. -/
theorem row_step
    (hA : ∀ x τ, Allowed (T x τ))
    (hH : ∀ x τ, (T (x+1) τ).west = (T x τ).east)
    (hTime : ∀ x τ, (T x (τ+1)).north = (T x τ).south)
    (hs : PersistentStrip T N L R)
    (hrow : RowEncodes T (-(L : ℤ)) (R : ℤ) t cfg)
    (q : Fin 215) (hq : cfg.state = some q) :
    RowEncodes T (-(L : ℤ)) (R : ℤ) (t+1) (DecimalMachine215.machine.step cfg) := by
  obtain ⟨hl,hr⟩ := next_head_inside hA hH hs hrow q hq
  refine ⟨hl,hr,?_⟩
  intro x hxl hxr
  rw [hTime x t]
  exact south_step hA hH hTime hs hrow q hq x hxl hxr

end DiophantineConsistency.WangTiles942RowStep
