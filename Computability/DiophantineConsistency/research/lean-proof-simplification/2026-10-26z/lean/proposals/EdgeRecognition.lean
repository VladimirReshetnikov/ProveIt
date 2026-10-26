import DiophantineConsistency.WangTiles942RowStep

/-!
UNVALIDATED CANDIDATE. This file has not been compiled in the project environment.
It proves a recognition invariant for arbitrary allowed strip rows. It does not
construct a shared edge field; that construction is prior work and is assumed
available. No numeric table values or machine direction cases are reevaluated.
-/
namespace DiophantineConsistency.EdgeRecognition
open SetTheory.BusyBeaver
open WangTiles942 WangTiles942Language WangTiles942Signals WangTiles942RowEncoding
  WangTiles942StripGeometry WangTiles942OperatingRow WangTiles942HeadBounds

set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
variable {T : ℤ → ℤ → Tile} {N L R : ℕ} {t : ℤ} {cfg : Config 215}

/-- An edge with no head at either endpoint is zero. The encoded interior
head guarantees that the two walls cannot occupy adjacent integer cells. -/
theorem nonhead_edge_zero
    (hA : ∀ x τ, Allowed (T x τ))
    (hH : ∀ x τ, (T (x+1) τ).west = (T x τ).east)
    (hs : PersistentStrip T N L R)
    (hrow : RowEncodes T (-(L : ℤ)) (R : ℤ) t cfg)
    (x : ℤ) (hl : -(L : ℤ) ≤ x) (hr : x+1 ≤ (R : ℤ))
    (ho : x ≠ cfg.head) (hn : x+1 ≠ cfg.head) :
    (T x t).east = 0 := by
  have hm := hH x t
  have hhL := hrow.head_left
  have hhR := hrow.head_right
  by_cases hw : x = -(L : ℤ)
  · have hb := left_wall_east_le_two hs t
    rw [← hw] at hb
    have hp := hrow.plain (x+1) (by omega) (by omega) hn
    have hz := plain_west_small_eq_zero (hA (x+1) t) (symbol cfg (x+1)) hp (by omega)
    exact hm.symm.trans hz
  · by_cases hw' : x+1 = (R : ℤ)
    · have hb := right_wall_west_le_four hs t
      rw [← hw'] at hb
      have hp := hrow.plain x (by omega) (by omega) ho
      exact plain_east_small_eq_zero (hA x t) (symbol cfg x) hp (by omega)
    · exact plain_pair_edge_zero (hA x t) (hA (x+1) t)
        (symbol cfg x) (symbol cfg (x+1))
        (hrow.plain x (by omega) (by omega) ho)
        (hrow.plain (x+1) (by omega) (by omega) hn) hm.symm

/-- All actual horizontal edges are determined by the actual head tile.
This is independent of the head's state and has no direction split. -/
theorem edge_shape
    (hA : ∀ x τ, Allowed (T x τ))
    (hH : ∀ x τ, (T (x+1) τ).west = (T x τ).east)
    (hs : PersistentStrip T N L R)
    (hrow : RowEncodes T (-(L : ℤ)) (R : ℤ) t cfg)
    (x : ℤ) (hl : -(L : ℤ) ≤ x) (hr : x+1 ≤ (R : ℤ)) :
    (T x t).east =
      if x = cfg.head then (T cfg.head t).east
      else if x+1 = cfg.head then (T cfg.head t).west else 0 := by
  split_ifs with ho hn
  · exact congrArg (fun y => (T y t).east) ho
  · simpa only [hn] using (hH x t).symm
  · exact nonhead_edge_zero hA hH hs hrow x hl hr ho hn

#print axioms nonhead_edge_zero
#print axioms edge_shape
end DiophantineConsistency.EdgeRecognition
