import DiophantineConsistency.WangTiles942ResetHorizontal

/-! Checks of every reset alternative and indispensable seam exceptions.
No propagation to a whole row, computation, or halting is asserted. -/

namespace DiophantineConsistency.WangTiles942ResetHorizontalChecks

open WangTiles942 WangTiles942Language WangTiles942ResetHorizontal

set_option Elab.async false
set_option maxHeartbeats 1000000

example {d : Bool} {q : ℕ} (hq : q ∈ targets d) : rail d q ≠ 1 := by
  have h := (valid_rail_range hq).1
  omega

example (p : ℕ) (hp : p ∈ [434,435,436]) : Allowed (⟨1,438,1,p⟩ : Tile) :=
  Allowed.reset p hp

-- West 1 must preserve every possible seam east parameter.
example (b : Fin 3) : Allowed (⟨1,437,b.val,437⟩ : Tile) :=
  Allowed.seam (1 : Fin 3) b

-- East 1 must preserve all three west square parameters, including 0 and 4.
example (a : Fin 3) : Allowed (⟨a.val^2,437,1,437⟩ : Tile) :=
  Allowed.seam a (1 : Fin 3)

example : Allowed (⟨0,437,1,437⟩ : Tile) ∧ Allowed (⟨4,437,1,437⟩ : Tile) :=
  ⟨Allowed.seam (0 : Fin 3) (1 : Fin 3), Allowed.seam (2 : Fin 3) (1 : Fin 3)⟩

-- Even both horizontal edges being 1 does not force reset without nonseam.
example : Allowed (⟨1,437,1,437⟩ : Tile) ∧
    ¬ (∃ p ∈ [434,435,436], (⟨1,437,1,437⟩ : Tile) = ⟨1,438,1,p⟩) := by
  refine ⟨Allowed.seam (1 : Fin 3) (1 : Fin 3), ?_⟩
  rintro ⟨p,hp,he⟩
  have hn := congrArg Tile.north he
  norm_num at hn

-- A forged reset with an unlisted south color is excluded.
example : ¬ Allowed (⟨1,438,1,433⟩ : Tile) := by
  intro h
  obtain ⟨p,hp,he⟩ := west_1_nonseam h rfl (by decide)
  have hs := congrArg Tile.south he
  simp only at hs
  subst p
  norm_num at hp

example (i : Fin 942) (hw : (tile i).west = 1) (hn : (tile i).north ≠ 437) :
    ∃ p ∈ [434,435,436], tile i = ⟨1,438,1,p⟩ :=
  west_1_nonseam (tile_allowed i) hw hn

example (i : Fin 942) (he : (tile i).east = 1) (hn : (tile i).north ≠ 437) :
    (tile i).north = 438 :=
  north_438_of_horizontal_one_nonseam (tile_allowed i) (Or.inr he) hn

example {t : Tile} (ht : Allowed t) (h1 : t.west = 1 ∨ t.east = 1)
    (hn : t.north ≠ 437) : t.west = 1 ∧ t.east = 1 := by
  obtain ⟨p,hp,rfl⟩ := horizontal_one_nonseam ht h1 hn
  exact ⟨rfl,rfl⟩

#print axioms horizontal_one_cases
#print axioms west_1_iff_reset_or_seam
#print axioms east_1_iff_reset_or_seam
#print axioms west_1_nonseam
#print axioms east_1_nonseam
#print axioms horizontal_one_nonseam
#print axioms north_438_of_horizontal_one_nonseam

end DiophantineConsistency.WangTiles942ResetHorizontalChecks
