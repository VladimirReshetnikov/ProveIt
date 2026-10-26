import DiophantineConsistency.WangTiles942InitialHorizontal

namespace DiophantineConsistency.WangTiles942InitialHorizontalChecks

open WangTiles942 WangTiles942Language WangTiles942InitialHorizontal

set_option Elab.async false
set_option maxRecDepth 10000

-- Both seam alternatives are genuine members of the actual indexed table.
example (a : Fin 3) : ∃ i : Fin 942, tile i = ⟨a.val^2,437,2,437⟩ :=
  (allowed_iff_tile _).mp (Allowed.seam a 2)

example (b : Fin 3) : ∃ i : Fin 942, tile i = ⟨4,437,b.val,437⟩ := by
  exact (allowed_iff_tile _).mp (Allowed.seam 2 b)

-- Omitting seams would give false classifications for both East2 and West4.
example : Allowed (⟨4,437,2,437⟩ : Tile) ∧
    (⟨4,437,2,437⟩ : Tile).east = 2 ∧
    (⟨4,437,2,437⟩ : Tile).west = 4 ∧
    (⟨4,437,2,437⟩ : Tile) ≠ ⟨2,434,2,0⟩ ∧
    (⟨4,437,2,437⟩ : Tile) ≠ ⟨4,436,4,0⟩ := by
  exact ⟨Allowed.seam 2 2, rfl, rfl, by decide, by decide⟩

-- The complete right-hand alternatives also imply Allowed, not merely color equality.
example (t : Tile) : (Allowed t ∧ t.east = 2) ↔
    t = ⟨2,434,2,0⟩ ∨ ∃ a : Fin 3, t = ⟨a.val^2,437,2,437⟩ := by
  constructor
  · rintro ⟨ht, he⟩
    exact (east_2_iff_initLeft_or_seam ht).mp he
  · rintro (rfl | ⟨a,rfl⟩)
    · exact ⟨Allowed.initLeft, rfl⟩
    · exact ⟨Allowed.seam a 2, rfl⟩

example (t : Tile) : (Allowed t ∧ t.west = 4) ↔
    t = ⟨4,436,4,0⟩ ∨ ∃ b : Fin 3, t = ⟨4,437,b.val,437⟩ := by
  constructor
  · rintro ⟨ht, hw⟩
    exact (west_4_iff_initRight_or_seam ht).mp hw
  · rintro (rfl | ⟨b,rfl⟩)
    · exact ⟨Allowed.initRight, rfl⟩
    · exact ⟨Allowed.seam 2 b, rfl⟩

-- Start's east edge3 forces a neighboring west3 tile to be the head initializer.
example (t : Tile) (ht : Allowed t) (he : t.west = start.east) :
    t = ⟨3,436,4,4⟩ := (west_3_iff_initHead ht).mp he

-- The head initializer's west edge3 forces an east3 neighbor to be Start.
example (t : Tile) (ht : Allowed t) (he : t.east = 3) : t = start :=
  (east_3_iff_start ht).mp he

example (i : Fin 942) : (tile i).west = 2 ↔
    tile i = start ∨ tile i = ⟨2,434,2,0⟩ :=
  west_2_iff_start_or_initLeft (tile_allowed i)

example (t : Tile) (ht : Allowed t) (hn : t.north ≠ 437) :
    (t.east = 2 → t = ⟨2,434,2,0⟩) ∧
    (t.west = 4 → t = ⟨4,436,4,0⟩) :=
  ⟨fun he => east_2_nonseam ht he hn, fun hw => west_4_nonseam ht hw hn⟩

#print axioms small_horizontal_cases
#print axioms east_2_iff_initLeft_or_seam
#print axioms west_3_iff_initHead
#print axioms west_4_iff_initRight_or_seam
#print axioms east_3_iff_start
#print axioms west_2_iff_start_or_initLeft
#print axioms east_2_nonseam
#print axioms west_4_nonseam

end DiophantineConsistency.WangTiles942InitialHorizontalChecks
