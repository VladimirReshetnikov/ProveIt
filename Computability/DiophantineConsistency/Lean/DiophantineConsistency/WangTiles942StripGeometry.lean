import DiophantineConsistency.WangTiles942InitialStrip
import DiophantineConsistency.WangTiles942SeamColumns

/-!
# Fixed finite strip walls and a seam-free interior

The initial row determines the two walls and every interior tile. Actual
vertical matching preserves the wall columns and excludes seams at every
interior integer coordinate and time. No machine-run premise is used.
-/

namespace DiophantineConsistency.WangTiles942StripGeometry

open WangTiles942 WangTiles942Language WangTiles942Periodic
  WangTiles942InitialStrip WangTiles942SeamColumns

set_option Elab.async false
set_option maxHeartbeats 1000000

/-- The exact initial tile at every integer position strictly between the
walls. The distinguished South1 and head South4 are retained. -/
theorem initial_tile {T : ℤ → Tile} {N L R : ℕ} (h : InitialStrip T N L R)
    (x : ℤ) (hl : -(L : ℤ) < x) (hr : x < (R : ℤ)) :
    T x = if x < 0 then ⟨2,434,2,0⟩ else
      if x = 0 then start else if x = 1 then ⟨3,436,4,4⟩ else ⟨4,436,4,0⟩ := by
  by_cases hx : x < 0
  · rw [if_pos hx]
    have hc : ((-x).toNat : ℤ) = -x := Int.toNat_of_nonneg (by omega)
    have hi := h.left_inside (-x).toNat (by omega) (by omega)
    simpa only [hc, neg_neg] using hi
  · rw [if_neg hx]
    by_cases hz : x = 0
    · rw [if_pos hz, hz]
      exact h.start_at_zero
    · rw [if_neg hz]
      by_cases ho : x = 1
      · rw [if_pos ho, ho]
        exact h.head_at_one
      · rw [if_neg ho]
        have hc : (x.toNat : ℤ) = x := Int.toNat_of_nonneg (by omega)
        have hi := h.right_inside x.toNat (by omega) (by omega)
        simpa only [hc] using hi

theorem initial_vertical_nonseam {T : ℤ → Tile} {N L R : ℕ}
    (h : InitialStrip T N L R) (x : ℤ) (hl : -(L : ℤ) < x) (hr : x < (R : ℤ)) :
    (T x).north ≠ 437 ∧ (T x).south ≠ 437 := by
  rw [initial_tile h x hl hr]
  split_ifs <;> decide

/-- This is the seeded tape after the actual blank-machine first action:
one written1 at zero, state1 on blank0 at position1, and plain0 elsewhere. -/
theorem initial_south {T : ℤ → Tile} {N L R : ℕ}
    (h : InitialStrip T N L R) (x : ℤ) (hl : -(L : ℤ) < x) (hr : x < (R : ℤ)) :
    (T x).south = if x = 0 then 1 else if x = 1 then 4 else 0 := by
  rw [initial_tile h x hl hr]
  split_ifs <;> simp_all [start]

/-- Exact initial geometry, persistent seam walls, and no seam inside.
The finite seam parameters are permitted to change with time. -/
structure PersistentStrip (T : ℤ → ℤ → Tile) (N L R : ℕ) : Prop where
  initial : InitialStrip (fun x => T x 0) N L R
  left_wall : ∀ t : ℤ, ∃ a b : Fin 3, T (-(L : ℤ)) t = ⟨a.val^2,437,b.val,437⟩
  right_wall : ∀ t : ℤ, ∃ a b : Fin 3, T (R : ℤ) t = ⟨a.val^2,437,b.val,437⟩
  interior : ∀ x : ℤ, -(L : ℤ) < x → x < (R : ℤ) →
    ∀ t : ℤ, (T x t).north ≠ 437 ∧ (T x t).south ≠ 437

/-- All temporal geometry follows from allowedness, actual time matching
and the already derived initial strip; no horizontal premise is added. -/
theorem persistent_of_initial {T : ℤ → ℤ → Tile} {N L R : ℕ}
    (hA : ∀ x t, Allowed (T x t))
    (hTime : ∀ x t, (T x (t+1)).north = (T x t).south)
    (h : InitialStrip (fun x => T x 0) N L R) : PersistentStrip T N L R := by
  refine ⟨h, ?_, ?_, ?_⟩
  · exact column_seam_tuples hA hTime (-(L : ℤ)) 0 h.wall_north.1
  · exact column_seam_tuples hA hTime (R : ℤ) 0 h.wall_north.2
  · intro x hl hr t
    have hn := (initial_vertical_nonseam h x hl hr).1
    have ht : (T x t).north ≠ 437 := by
      intro hs
      exact hn ((seam_iff_zero hA hTime x t).mp hs)
    exact ⟨ht, fun hs => ht ((seam_at_iff_south hA x t).mpr hs)⟩

/-- A marked cyclic word supplies finite fixed strip walls and a seam-free
interior at every integer time, with only its three actual matching fields. -/
theorem marked_persistent_strip {N : ℕ} [NeZero N] {s : ℤ} {a : ZMod N → Fin 942}
    (h : MarkedWord N s a) : ∃ L R : ℕ, PersistentStrip (plane N s a) N L R := by
  obtain ⟨L,R,hi⟩ := marked_initial_strip h
  exact ⟨L,R,persistent_of_initial (plane_allowed N s a) (plane_time_matching h) hi⟩

end DiophantineConsistency.WangTiles942StripGeometry
