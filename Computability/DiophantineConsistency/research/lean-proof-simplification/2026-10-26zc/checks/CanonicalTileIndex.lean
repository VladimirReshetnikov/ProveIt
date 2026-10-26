import DiophantineConsistency.WangTiles942HelicalQuotient

/-! A computable decoder for allowed literal tiles. The algorithm is the
existing recoveredIndex; the membership proof is used only to certify
the finite bound. This file is an additive comparison with the legacy
choice-based word. -/

namespace CanonicalTileIndex

open DiophantineConsistency DiophantineConsistency.WangTiles942
open DiophantineConsistency.WangTiles942Language
open DiophantineConsistency.WangTiles942HelicalQuotient

theorem recoveredIndex_lt {t : Tile} (ht : Allowed t) : recoveredIndex t < 942 := by
  obtain ⟨i, rfl⟩ := (allowed_iff_tile t).mp ht
  simpa only [recovered_tile] using i.isLt

def indexOfAllowed (t : Tile) (ht : Allowed t) : Fin 942 :=
  ⟨recoveredIndex t, recoveredIndex_lt ht⟩

@[simp] theorem indexOfAllowed_tile (i : Fin 942) :
    indexOfAllowed (tile i) (tile_allowed i) = i :=
  Fin.ext (recovered_tile i)

@[simp] theorem tile_indexOfAllowed (t : Tile) (ht : Allowed t) :
    tile (indexOfAllowed t ht) = t := by
  obtain ⟨i, rfl⟩ := (allowed_iff_tile t).mp ht
  rw [indexOfAllowed_tile]

def quotientWordExplicit (T : ℤ → ℤ → Tile) (hA : ∀ x t, Allowed (T x t))
    (w H : ℕ) (z : ZMod (w*H)) : Fin 942 :=
  indexOfAllowed (T (-(z.val : ℤ)) 0) (hA _ _)

theorem quotientWordExplicit_tile (T : ℤ → ℤ → Tile)
    (hA : ∀ x t, Allowed (T x t)) (w H : ℕ) (z : ZMod (w*H)) :
    tile (quotientWordExplicit T hA w H z) = T (-(z.val : ℤ)) 0 :=
  tile_indexOfAllowed _ _

/-- The word is extensionally unchanged at every modulus, including zero. -/
theorem quotientWordExplicit_eq_legacy (T : ℤ → ℤ → Tile)
    (hA : ∀ x t, Allowed (T x t)) (w H : ℕ) :
    quotientWordExplicit T hA w H = quotientWord T hA w H := by
  funext z
  apply tile_injective
  exact (quotientWordExplicit_tile T hA w H z).trans (quotientWord_tile T hA w H z).symm

/-- Existing geometric conclusions transport through the exact word equality. -/
theorem quotientWordExplicit_marked (T : ℤ → ℤ → Tile)
    (hA : ∀ x t, Allowed (T x t)) (w H : ℕ) [NeZero (w*H)]
    (hH : ∀ x t, (T (x+1) t).west = (T x t).east)
    (hTime : ∀ x t, (T x (t+1)).north = (T x t).south)
    (hStart : T 0 0 = start)
    (hhelix : ∀ x t, T (x+(w : ℤ)) (t-1) = T x t)
    (hvertical : ∀ x t, T x (t+(H : ℤ)) = T x t) :
    DiophantineConsistency.WangTiles942Periodic.MarkedWord
      (w*H) (w : ℤ) (quotientWordExplicit T hA w H) := by
  rw [quotientWordExplicit_eq_legacy]
  exact quotientWord_marked T hA w H hH hTime hStart hhelix hvertical

example : indexOfAllowed start Allowed.start = 0 := rfl
example : indexOfAllowed ⟨2,434,2,0⟩ Allowed.initLeft = 927 := rfl
example : indexOfAllowed ⟨3,436,4,4⟩ Allowed.initHead = 928 := rfl

#print axioms indexOfAllowed
#print axioms tile_indexOfAllowed
#print axioms quotientWordExplicit
#print axioms quotientWordExplicit_eq_legacy

end CanonicalTileIndex
