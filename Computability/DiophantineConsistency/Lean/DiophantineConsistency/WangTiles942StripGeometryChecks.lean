import DiophantineConsistency.WangTiles942StripGeometry

namespace DiophantineConsistency.WangTiles942StripGeometryChecks

open WangTiles942 WangTiles942Periodic WangTiles942StripGeometry

set_option Elab.async false

/-- The exact initialization is seeded, rather than an everywhere-zero
South row; the unique operational head has color4. -/
example {T : ℤ → ℤ → Tile} {N L R : ℕ} (h : PersistentStrip T N L R) :
    (T 0 0).south = 1 ∧ (T 1 0).south = 4 := by
  rw [h.initial.start_at_zero, h.initial.head_at_one]
  exact ⟨rfl,rfl⟩

/-- No assumption about a run, a unique global Start or rectangular
quotient is needed to obtain the bounded, persistent strip. -/
example {N : ℕ} [NeZero N] {s : ℤ} {a : ZMod N → Fin 942}
    (h : MarkedWord N s a) : ∃ L R : ℕ,
      0 < L ∧ L ≤ N ∧ 2 ≤ R ∧ R ≤ N+1 ∧
      (∀ x : ℤ, -(L : ℤ) < x → x < (R : ℤ) →
        ∀ t : ℤ, (plane N s a x t).north ≠ 437 ∧ (plane N s a x t).south ≠ 437) := by
  obtain ⟨L,R,hs⟩ := marked_persistent_strip h
  exact ⟨L,R,hs.initial.left_pos,hs.initial.left_le,hs.initial.right_min,
    hs.initial.right_le,hs.interior⟩

/-- Both distinguished positions lie strictly between the walls, including
when no additional left or right initializer tail is present. -/
example {T : ℤ → ℤ → Tile} {N L R : ℕ} (h : PersistentStrip T N L R) (t : ℤ) :
    (T 0 t).north ≠ 437 ∧ (T 1 t).north ≠ 437 := by
  have hl := h.initial.left_pos
  have hr := h.initial.right_min
  exact ⟨(h.interior 0 (by omega) (by omega) t).1,
    (h.interior 1 (by omega) (by omega) t).1⟩

#print axioms initial_tile
#print axioms initial_vertical_nonseam
#print axioms initial_south
#print axioms persistent_of_initial
#print axioms marked_persistent_strip

end DiophantineConsistency.WangTiles942StripGeometryChecks
