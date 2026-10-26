import DiophantineConsistency.WangTiles942Boundary

/-! Focused checks of actual boundary rows and of excluded lookalikes.
These are local finite-table statements, not strip or run assertions. -/

namespace DiophantineConsistency.WangTiles942BoundaryChecks

open WangTiles942 WangTiles942Language WangTiles942Boundary

set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

example (j : Fin 430) : (transitionRow j).2.north ≤ 431 := transition_north_bound j

example : (transitionRow (429 : Fin 430)).2.north = 431 := by
  change 2*(429/2)+429%2+2 = 431
  decide

-- Halt output heads 432 and 433 are included, but never reach a boundary color.
example : headColor 215 0 = 432 ∧ headColor 215 1 = 433 := by decide +kernel

example (b : Fin 2) : headColor 215 b.val ≤ 433 :=
  receive_south_bound (d := true) (by decide +kernel) b

example (i : Fin 942) : (tile i).north = 435 ↔ tile i = start :=
  north_435_iff_start (tile_allowed i)

example : (tile 928).north = 436 ∧ (tile 928).south = 4 := by
  rw [initializer_928]
  decide

example : ¬ Allowed (⟨3,436,4,188⟩ : Tile) := by
  intro h
  have hh := (north_436_iff_initializers h).mp rfl
  norm_num [Tile.mk.injEq] at hh

example : ∃ i : Fin 942, tile i = ⟨4,437,2,437⟩ := by
  exact seam_tile_exists (2 : Fin 3) (2 : Fin 3)

-- A seam west color is a square 0,1,4, not an arbitrary number below 3.
example : ¬ Allowed (⟨2,437,0,437⟩ : Tile) := by
  intro h
  obtain ⟨a,b,he⟩ := (north_437_iff_seam h).mp rfl
  have hw := congrArg Tile.west he
  simp only at hw
  fin_cases a <;> norm_num at hw

example {t : Tile} (ht : Allowed t) : t.north = 437 ↔ t.south = 437 :=
  north_437_iff_south_437 ht

example {t : Tile} (ht : Allowed t) : t.south = 435 ↔ t = ⟨1,438,1,435⟩ :=
  south_reset_iff ht 435 (by decide +kernel)

example {t : Tile} (ht : Allowed t) : t.south = 434 ↔ t = ⟨1,438,1,434⟩ :=
  south_reset_iff ht 434 (by decide +kernel)

example {t : Tile} (ht : Allowed t) : t.south = 436 ↔ t = ⟨1,438,1,436⟩ :=
  south_reset_iff ht 436 (by decide +kernel)

example : ¬ Allowed (⟨0,434,0,438⟩ : Tile) := by
  intro h
  obtain ⟨a,b,he⟩ := (south_438_iff_finish h).mp rfl
  have hn := congrArg Tile.north he
  have hb := plain_or_halt_bound a b
  simp only at hn
  omega

#print axioms transition_north_bound
#print axioms receive_south_bound
#print axioms high_north_cases
#print axioms high_south_cases
#print axioms north_435_iff_start
#print axioms north_434_iff_initLeft
#print axioms north_436_iff_initializers
#print axioms north_438_iff_reset
#print axioms north_437_iff_seam
#print axioms south_438_iff_finish
#print axioms south_437_iff_seam
#print axioms north_437_iff_south_437
#print axioms south_reset_iff
#print axioms seam_tile_exists

end DiophantineConsistency.WangTiles942BoundaryChecks
