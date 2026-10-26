import DiophantineConsistency.WangTiles942Boundary

/-!
Draft simplification against b310142330df89e48413c8fce62e7de223e1c7d5.
NOT compiled in this environment. Existing classifiers are imported only
for their high_north_cases/high_south_cases elimination lemmas.
The short corollaries below do not invoke their original exact-color counterparts.
-/

namespace DiophantineConsistency.Round2BoundaryFibers

open WangTiles942 WangTiles942Language WangTiles942Boundary

/-- Exact guarded north-color fiber above the ordinary head range.
The 436 branch retains the actual initializer south color 4. -/
theorem high_north_fiber {t : Tile} (ht : Allowed t) (c : ℕ) (hc : 434 ≤ c) :
    t.north = c ↔
      (c = 435 ∧ t = start) ∨
      (c = 434 ∧ t = ⟨2,434,2,0⟩) ∨
      (c = 436 ∧ (t = ⟨3,436,4,4⟩ ∨ t = ⟨4,436,4,0⟩)) ∨
      (c = 438 ∧ ∃ p ∈ [434,435,436], t = ⟨1,438,1,p⟩) ∨
      (c = 437 ∧ ∃ a b : Fin 3, t = ⟨a.val^2,437,b.val,437⟩) := by
  constructor
  · intro hn
    rcases high_north_cases ht (by omega) with
      rfl | rfl | rfl | rfl | ⟨p,hp,rfl⟩ | ⟨a,b,rfl⟩
    · exact Or.inl ⟨hn.symm,rfl⟩
    · exact Or.inr (Or.inl ⟨hn.symm,rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hn.symm,Or.inl rfl⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨hn.symm,Or.inr rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hn.symm,p,hp,rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hn.symm,a,b,rfl⟩)))
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl | rfl⟩ |
      ⟨rfl,p,hp,rfl⟩ | ⟨rfl,a,b,rfl⟩) <;> rfl

/-- The reset branch is indexed by the requested south color, eliminating
an existential reset parameter and subsequent equality substitution. -/
theorem high_south_fiber {t : Tile} (ht : Allowed t) (c : ℕ) (hc : 434 ≤ c) :
    t.south = c ↔
      (c = 438 ∧ ∃ a b : Fin 2, t = ⟨0,432*a.val+b.val,0,438⟩) ∨
      (c ∈ [434,435,436] ∧ t = ⟨1,438,1,c⟩) ∨
      (c = 437 ∧ ∃ a b : Fin 3, t = ⟨a.val^2,437,b.val,437⟩) := by
  constructor
  · intro hs
    rcases high_south_cases ht (by omega) with
      ⟨a,b,rfl⟩ | ⟨p,hp,rfl⟩ | ⟨a,b,rfl⟩
    · exact Or.inl ⟨hs.symm,a,b,rfl⟩
    · change p = c at hs
      subst p
      exact Or.inr (Or.inl ⟨hp,rfl⟩)
    · exact Or.inr (Or.inr ⟨hs.symm,a,b,rfl⟩)
  · rintro (⟨rfl,a,b,rfl⟩ | ⟨hp,rfl⟩ | ⟨rfl,a,b,rfl⟩) <;> rfl

theorem north_435_iff_start_short {t : Tile} (ht : Allowed t) :
    t.north = 435 ↔ t = start := by
  simpa using high_north_fiber ht 435 (by decide)

theorem north_434_iff_initLeft_short {t : Tile} (ht : Allowed t) :
    t.north = 434 ↔ t = ⟨2,434,2,0⟩ := by
  simpa using high_north_fiber ht 434 (by decide)

theorem north_436_iff_initializers_short {t : Tile} (ht : Allowed t) :
    t.north = 436 ↔ t = ⟨3,436,4,4⟩ ∨ t = ⟨4,436,4,0⟩ := by
  simpa using high_north_fiber ht 436 (by decide)

theorem north_438_iff_reset_short {t : Tile} (ht : Allowed t) :
    t.north = 438 ↔ ∃ p ∈ [434,435,436], t = ⟨1,438,1,p⟩ := by
  simpa using high_north_fiber ht 438 (by decide)

theorem north_437_iff_seam_short {t : Tile} (ht : Allowed t) :
    t.north = 437 ↔ ∃ a b : Fin 3, t = ⟨a.val^2,437,b.val,437⟩ := by
  simpa using high_north_fiber ht 437 (by decide)

theorem south_438_iff_finish_short {t : Tile} (ht : Allowed t) :
    t.south = 438 ↔ ∃ a b : Fin 2, t = ⟨0,432*a.val+b.val,0,438⟩ := by
  simpa using high_south_fiber ht 438 (by decide)

theorem south_437_iff_seam_short {t : Tile} (ht : Allowed t) :
    t.south = 437 ↔ ∃ a b : Fin 3, t = ⟨a.val^2,437,b.val,437⟩ := by
  simpa using high_south_fiber ht 437 (by decide)

theorem south_reset_iff_short {t : Tile} (ht : Allowed t) (p : ℕ)
    (hp : p ∈ [434,435,436]) : t.south = p ↔ t = ⟨1,438,1,p⟩ := by
  have hb : 434 ≤ p ∧ p ≤ 436 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    omega
  have h437 : p ≠ 437 := by omega
  have h438 : p ≠ 438 := by omega
  simpa [h437, h438, hp] using high_south_fiber ht p hb.1

#print axioms high_north_fiber
#print axioms high_south_fiber
#print axioms north_435_iff_start_short
#print axioms north_434_iff_initLeft_short
#print axioms north_436_iff_initializers_short
#print axioms north_438_iff_reset_short
#print axioms north_437_iff_seam_short
#print axioms south_438_iff_finish_short
#print axioms south_437_iff_seam_short
#print axioms south_reset_iff_short

end DiophantineConsistency.Round2BoundaryFibers
