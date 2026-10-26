import DiophantineConsistency.WangTiles942Periodic

/-! Checks of the signed cyclic address and the exact matching orientation.
No marked word is postulated to exist, and no machine semantics is assumed. -/

namespace DiophantineConsistency.WangTiles942PeriodicChecks

open WangTiles942 WangTiles942Language WangTiles942Periodic

set_option Elab.async false
set_option maxHeartbeats 1000000

-- Moving east subtracts one, and advancing a row subtracts s.
example : address 7 3 2 4 = 0 ∧ address 7 3 3 4 = 6 ∧
    address 7 3 2 5 = 4 := by decide +kernel

-- The opposite sign is genuinely different, not an interchangeable convention.
example : address 7 3 3 4 ≠ address 7 3 2 4 + 1 ∧
    address 7 3 2 5 ≠ address 7 3 2 4 + 3 := by decide +kernel

example : address 7 (-3) 2 4 = 3 ∧ address 7 3 (-2) (-4) = 0 := by decide +kernel

-- Neither coprimality, shift divisibility, nor a reduced shift is needed.
example (a : ZMod 6 → Fin 942) (x t : ℤ) :
    plane 6 14 a (x+6) t = plane 6 14 a x t ∧
    plane 6 14 a x (t+6) = plane 6 14 a x t :=
  ⟨plane_horizontal_period 6 14 a x t, plane_vertical_period 6 14 a x t⟩

example (a : ZMod 6 → Fin 942) (x t : ℤ) :
    plane 6 (-14) a (x+14) (t+1) = plane 6 (-14) a x t := by
  simpa using plane_helical_period 6 (-14) a x t

variable {N : ℕ} [NeZero N] {s : ℤ} {a : ZMod N → Fin 942}

-- These are all fields of the input structure; no uniqueness or run field exists.
example (h0 : a 0 = 0)
    (hH : ∀ i, (tile (a i)).east = (tile (a (i-1))).west)
    (hT : ∀ i, (tile (a i)).south = (tile (a (i-(s : ZMod N)))).north) :
    MarkedWord N s a := ⟨h0,hH,hT⟩

example (h : MarkedWord N s a) : plane N s a 0 0 = ⟨2,435,3,1⟩ := plane_start h

example (h : MarkedWord N s a) (x t : ℤ) :
    (plane N s a (x+1) t).west = (plane N s a x t).east ∧
    (plane N s a x (t+1)).north = (plane N s a x t).south :=
  ⟨plane_east_matching h x t, plane_time_matching h x t⟩

example (h : MarkedWord N s a) :
    (∀ x t, Allowed (plane N s a x t)) ∧ plane N s a 0 0 = start :=
  ⟨plane_allowed N s a, plane_start h⟩

example (s₀ : ℕ) (h : MarkedWord N (s₀ : ℤ) a) (x t : ℤ) :
    (plane N (s₀ : ℤ) a x (t+1)).north = (plane N (s₀ : ℤ) a x t).south :=
  plane_time_matching h x t

#print axioms address_east
#print axioms address_next_row
#print axioms address_horizontal_period
#print axioms address_vertical_period
#print axioms plane_allowed
#print axioms plane_helical_period
#print axioms plane_periodic
#print axioms plane_east_matching
#print axioms plane_time_matching
#print axioms plane_start
#print axioms marked_periodic_plane

end DiophantineConsistency.WangTiles942PeriodicChecks
