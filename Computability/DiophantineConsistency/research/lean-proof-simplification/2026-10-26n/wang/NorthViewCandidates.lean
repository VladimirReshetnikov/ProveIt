import DiophantineConsistency.WangTiles942Boundary

/-!
UNCOMPILED proposal at ProveIt b310142330df89e48413c8fce62e7de223e1c7d5.
Keep the original Allowed language, literal colors and public statements.
The new helper uses only high_north_cases, not the classification theorems
whose proof bodies are being proposed for replacement.
-/
namespace DiophantineConsistency.WangNorthViewProposal
open WangTiles942 WangTiles942Language WangTiles942Boundary

/-- A color-indexed result; no search over all 942 table indices. -/
def NorthView (n : ℕ) (t : Tile) : Prop :=
  match n with
  | 434 => t = ⟨2,434,2,0⟩
  | 435 => t = start
  | 436 => t = ⟨3,436,4,4⟩ ∨ t = ⟨4,436,4,0⟩
  | 437 => ∃ a b : Fin 3, t = ⟨a.val^2,437,b.val,437⟩
  | 438 => ∃ p ∈ [434,435,436], t = ⟨1,438,1,p⟩
  | _ => False

theorem north_view {t : Tile} (ht : Allowed t) (hn : 434 ≤ t.north) :
    NorthView t.north t := by
  rcases high_north_cases ht hn with
    rfl | rfl | rfl | rfl | ⟨p,hp,rfl⟩ | ⟨a,b,rfl⟩
  · exact rfl
  · exact rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact ⟨p,hp,rfl⟩
  · exact ⟨a,b,rfl⟩

theorem north_435_iff_start_candidate {t : Tile} (ht : Allowed t) :
    t.north = 435 ↔ t = start := by
  constructor
  · intro hn
    simpa only [hn, NorthView] using north_view ht (by omega)
  · rintro rfl
    rfl

theorem north_434_iff_initLeft_candidate {t : Tile} (ht : Allowed t) :
    t.north = 434 ↔ t = ⟨2,434,2,0⟩ := by
  constructor
  · intro hn
    simpa only [hn, NorthView] using north_view ht (by omega)
  · rintro rfl
    rfl

theorem north_436_iff_initializers_candidate {t : Tile} (ht : Allowed t) :
    t.north = 436 ↔ t = ⟨3,436,4,4⟩ ∨ t = ⟨4,436,4,0⟩ := by
  constructor
  · intro hn
    simpa only [hn, NorthView] using north_view ht (by omega)
  · rintro (rfl | rfl) <;> rfl

theorem north_438_iff_reset_candidate {t : Tile} (ht : Allowed t) :
    t.north = 438 ↔ ∃ p ∈ [434,435,436], t = ⟨1,438,1,p⟩ := by
  constructor
  · intro hn
    simpa only [hn, NorthView] using north_view ht (by omega)
  · rintro ⟨p,hp,rfl⟩
    rfl

theorem north_437_iff_seam_candidate {t : Tile} (ht : Allowed t) :
    t.north = 437 ↔ ∃ a b : Fin 3, t = ⟨a.val^2,437,b.val,437⟩ := by
  constructor
  · intro hn
    simpa only [hn, NorthView] using north_view ht (by omega)
  · rintro ⟨a,b,rfl⟩
    rfl

#print axioms DiophantineConsistency.WangNorthViewProposal.north_view
#print axioms DiophantineConsistency.WangNorthViewProposal.north_435_iff_start_candidate
#print axioms DiophantineConsistency.WangNorthViewProposal.north_434_iff_initLeft_candidate
#print axioms DiophantineConsistency.WangNorthViewProposal.north_436_iff_initializers_candidate
#print axioms DiophantineConsistency.WangNorthViewProposal.north_438_iff_reset_candidate
#print axioms DiophantineConsistency.WangNorthViewProposal.north_437_iff_seam_candidate
end DiophantineConsistency.WangNorthViewProposal
