import DiophantineConsistency.WangTiles942Boundary
import DiophantineConsistency.WangTiles942Periodic

/-!
# Seam columns are invariant in integer time

The generic result needs only allowed tiles and the actual vertical
matching convention. Horizontal matching and periodicity are unnecessary.
The marked-word specialization preserves the exact plane address and
shows that the column containing the origin Start is never a seam.
-/

namespace DiophantineConsistency.WangTiles942SeamColumns

open WangTiles942 WangTiles942Language WangTiles942Boundary WangTiles942Periodic

set_option Elab.async false
set_option maxHeartbeats 1000000

/-- North color 437 detects the seam status of this position. -/
def SeamAt (T : ℤ → ℤ → Tile) (x t : ℤ) : Prop := (T x t).north = 437

section Generic

variable {T : ℤ → ℤ → Tile}
variable (hAllowed : ∀ x t, Allowed (T x t))
variable (hTime : ∀ x t, (T x (t+1)).north = (T x t).south)

include hAllowed in
theorem seam_at_iff_south (x t : ℤ) : SeamAt T x t ↔ (T x t).south = 437 :=
  north_437_iff_south_437 (hAllowed x t)

include hAllowed hTime

/-- A time step cannot introduce or remove a seam in an allowed column. -/
theorem seam_successor_iff (x t : ℤ) : SeamAt T x (t+1) ↔ SeamAt T x t := by
  unfold SeamAt
  rw [hTime x t]
  exact (north_437_iff_south_437 (hAllowed x t)).symm

/-- The step equivalence gives period one, hence constant status on integer time. -/
theorem seam_iff_zero (x t : ℤ) : SeamAt T x t ↔ SeamAt T x 0 := by
  have hp : Function.Periodic (SeamAt T x) 1 :=
    fun u => propext (seam_successor_iff hAllowed hTime x u)
  simpa only [Int.cast_id, mul_one, eq_iff_iff] using hp.int_mul_eq t

theorem seam_iff_time (x t u : ℤ) : SeamAt T x t ↔ SeamAt T x u :=
  (seam_iff_zero hAllowed hTime x t).trans (seam_iff_zero hAllowed hTime x u).symm

/-- A seam at one time forces one of the nine actual seam tuples at every
integer time. The two finite horizontal parameters may vary with time. -/
theorem column_seam_tuples (x t₀ : ℤ) (hs : SeamAt T x t₀) :
    ∀ t : ℤ, ∃ a b : Fin 3, T x t = ⟨a.val^2,437,b.val,437⟩ := by
  intro t
  apply (north_437_iff_seam (hAllowed x t)).mp
  exact (seam_iff_time hAllowed hTime x t t₀).mpr hs

theorem column_seam_tuples_of_exists (x : ℤ) (hs : ∃ t, SeamAt T x t) :
    ∀ t : ℤ, ∃ a b : Fin 3, T x t = ⟨a.val^2,437,b.val,437⟩ := by
  obtain ⟨t₀,hs⟩ := hs
  exact column_seam_tuples hAllowed hTime x t₀ hs

/-- A Start at any one position excludes a seam throughout that column;
the other tiles in the column are not asserted to be Start. -/
theorem start_column_not_seam (x t₀ : ℤ) (hStart : T x t₀ = start) (t : ℤ) :
    ¬ SeamAt T x t := by
  intro hs
  have h₀ := (seam_iff_time hAllowed hTime x t t₀).mp hs
  norm_num [SeamAt, hStart, start] at h₀

theorem start_column_vertical_ne (x t₀ : ℤ) (hStart : T x t₀ = start) (t : ℤ) :
    (T x t).north ≠ 437 ∧ (T x t).south ≠ 437 := by
  have hn := start_column_not_seam hAllowed hTime x t₀ hStart t
  refine ⟨hn, ?_⟩
  intro hs
  exact hn ((seam_at_iff_south hAllowed x t).mpr hs)

end Generic

section Marked

variable {N : ℕ} [NeZero N] {s : ℤ} {a : ZMod N → Fin 942}

/-- Specialization to the actual signed marked-word plane, with no added
periodicity, alignment, uniqueness, or computation hypothesis. -/
theorem marked_seam_iff_zero (h : MarkedWord N s a) (x t : ℤ) :
    SeamAt (plane N s a) x t ↔ SeamAt (plane N s a) x 0 :=
  seam_iff_zero (plane_allowed N s a) (plane_time_matching h) x t

theorem marked_column_seam_tuples (h : MarkedWord N s a) (x t₀ : ℤ)
    (hs : SeamAt (plane N s a) x t₀) :
    ∀ t : ℤ, ∃ u v : Fin 3, plane N s a x t = ⟨u.val^2,437,v.val,437⟩ :=
  column_seam_tuples (plane_allowed N s a) (plane_time_matching h) x t₀ hs

theorem marked_origin_never_seam (h : MarkedWord N s a) (t : ℤ) :
    (plane N s a 0 t).north ≠ 437 ∧ (plane N s a 0 t).south ≠ 437 :=
  start_column_vertical_ne (plane_allowed N s a) (plane_time_matching h)
    0 0 (plane_start h) t

end Marked

end DiophantineConsistency.WangTiles942SeamColumns
