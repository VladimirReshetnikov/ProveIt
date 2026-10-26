import DiophantineConsistency.WangTiles942Language
import Mathlib.Data.ZMod.Basic

/-!
# Pulling an actual marked cyclic Wang word back to the plane

The cyclic matching convention is East(i) = West(i-1) and
South(i) = North(i-s). The integer address -x-s*t therefore places the
east neighbor at (x+1,t) and the next time row at (x,t+1). The shift is
arbitrary; there is no coprimality, rectangular shape, unique Start,
occupation, machine-run, or halting premise.
-/

namespace DiophantineConsistency.WangTiles942Periodic

open WangTiles942 WangTiles942Language

set_option Elab.async false
set_option maxHeartbeats 1000000

/-- An actual indexed word on a nonempty cyclic group, with Start fixed at
zero and exactly the two literal color-matching conditions. -/
structure MarkedWord (N : ℕ) [NeZero N] (s : ℤ) (a : ZMod N → Fin 942) : Prop where
  start_at_zero : a 0 = 0
  horizontal : ∀ i, (tile (a i)).east = (tile (a (i - 1))).west
  temporal : ∀ i, (tile (a i)).south = (tile (a (i - (s : ZMod N)))).north

/-- The signed pullback address; subtraction takes place before the cast. -/
def address (N : ℕ) (s x t : ℤ) : ZMod N := ((-x - s*t : ℤ) : ZMod N)

/-- Every plane entry remains an index in the exact 942-tile table. -/
def plane (N : ℕ) (s : ℤ) (a : ZMod N → Fin 942) (x t : ℤ) : Tile :=
  tile (a (address N s x t))

@[simp] theorem address_origin (N : ℕ) (s : ℤ) : address N s 0 0 = 0 := by
  simp [address]

theorem address_east (N : ℕ) (s x t : ℤ) :
    address N s (x+1) t = address N s x t - 1 := by
  unfold address
  push_cast
  ring

theorem address_next_row (N : ℕ) (s x t : ℤ) :
    address N s x (t+1) = address N s x t - (s : ZMod N) := by
  unfold address
  push_cast
  ring

/-- The horizontal period is the complete cyclic modulus, with no claim
that it is a least period. -/
theorem address_horizontal_period (N : ℕ) (s x t : ℤ) :
    address N s (x + (N : ℤ)) t = address N s x t := by
  simp [address]

/-- A vertical shift by N also leaves the address unchanged for every s. -/
theorem address_vertical_period (N : ℕ) (s x t : ℤ) :
    address N s x (t + (N : ℤ)) = address N s x t := by
  simp [address]

/-- The additional helical period follows from the same signed address. -/
theorem address_helical_period (N : ℕ) (s x t : ℤ) :
    address N s (x-s) (t+1) = address N s x t := by
  unfold address
  push_cast
  ring

theorem plane_allowed (N : ℕ) (s : ℤ) (a : ZMod N → Fin 942) (x t : ℤ) :
    Allowed (plane N s a x t) := tile_allowed _

theorem plane_horizontal_period (N : ℕ) (s : ℤ) (a : ZMod N → Fin 942) (x t : ℤ) :
    plane N s a (x + (N : ℤ)) t = plane N s a x t := by
  unfold plane
  rw [address_horizontal_period]

theorem plane_vertical_period (N : ℕ) (s : ℤ) (a : ZMod N → Fin 942) (x t : ℤ) :
    plane N s a x (t + (N : ℤ)) = plane N s a x t := by
  unfold plane
  rw [address_vertical_period]

theorem plane_helical_period (N : ℕ) (s : ℤ) (a : ZMod N → Fin 942) (x t : ℤ) :
    plane N s a (x-s) (t+1) = plane N s a x t := by
  unfold plane
  rw [address_helical_period]

/-- The two rectangular period vectors are (N,0) and (0,N), without any
constraint on the temporal shift. -/
theorem plane_periodic (N : ℕ) (s : ℤ) (a : ZMod N → Fin 942) :
    (∀ t, Function.Periodic (fun x => plane N s a x t) (N : ℤ)) ∧
    (∀ x, Function.Periodic (fun t => plane N s a x t) (N : ℤ)) := by
  exact ⟨fun t x => plane_horizontal_period N s a x t,
    fun x t => plane_vertical_period N s a x t⟩

variable {N : ℕ} [NeZero N] {s : ℤ} {a : ZMod N → Fin 942}

/-- Actual color orientation: the west edge at x+1 is the east edge at x. -/
theorem plane_east_matching (h : MarkedWord N s a) (x t : ℤ) :
    (plane N s a (x+1) t).west = (plane N s a x t).east := by
  unfold plane
  rw [address_east]
  exact (h.horizontal (address N s x t)).symm

/-- Actual time orientation: the north edge in row t+1 is the south edge in t. -/
theorem plane_time_matching (h : MarkedWord N s a) (x t : ℤ) :
    (plane N s a x (t+1)).north = (plane N s a x t).south := by
  unfold plane
  rw [address_next_row]
  exact (h.temporal (address N s x t)).symm

theorem plane_start (h : MarkedWord N s a) : plane N s a 0 0 = start := by
  unfold plane
  rw [address_origin, h.start_at_zero]
  exact start_zero

/-- The whole geometric endpoint: actual tiles, a marked origin, correct
matching, and two positive-length periods. No machine semantics is included. -/
theorem marked_periodic_plane (h : MarkedWord N s a) :
    (∀ x t, Allowed (plane N s a x t)) ∧
    plane N s a 0 0 = start ∧
    (∀ x t, (plane N s a (x+1) t).west = (plane N s a x t).east) ∧
    (∀ x t, (plane N s a x (t+1)).north = (plane N s a x t).south) ∧
    0 < (N : ℤ) ∧
    (∀ t, Function.Periodic (fun x => plane N s a x t) (N : ℤ)) ∧
    (∀ x, Function.Periodic (fun t => plane N s a x t) (N : ℤ)) := by
  exact ⟨plane_allowed N s a, plane_start h, plane_east_matching h,
    plane_time_matching h, by exact_mod_cast NeZero.pos N, plane_periodic N s a⟩

end DiophantineConsistency.WangTiles942Periodic
