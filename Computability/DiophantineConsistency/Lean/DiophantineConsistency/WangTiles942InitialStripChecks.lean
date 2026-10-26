import DiophantineConsistency.WangTiles942InitialStrip

namespace DiophantineConsistency.WangTiles942InitialStripChecks

open WangTiles942 WangTiles942Language WangTiles942Periodic WangTiles942InitialStrip

set_option Elab.async false
set_option maxRecDepth 10000

-- The exact requested wall bounds and complete initializer tails follow
-- without a wall, unique-Start, or machine premise.
example (T : ℤ → Tile) (hallowed : ∀ x, Allowed (T x))
    (hH : ∀ x, (T (x+1)).west = (T x).east)
    (N : ℕ) (hN : 0 < N) (hperiod : Function.Periodic T (N : ℤ))
    (hstart : T 0 = start) :
    ∃ L R : ℕ, 0 < L ∧ L ≤ N ∧ 2 ≤ R ∧ R ≤ N+1 ∧
      (T (-(L : ℤ))).north = 437 ∧ (T (R : ℤ)).north = 437 ∧
      (∀ j : ℕ, 1 ≤ j → j < L → T (-(j : ℤ)) = ⟨2,434,2,0⟩) ∧
      T 1 = ⟨3,436,4,4⟩ ∧
      (∀ j : ℕ, 2 ≤ j → j < R → T (j : ℤ) = ⟨4,436,4,0⟩) := by
  obtain ⟨L,R,h⟩ := periodic_initial_strip T hallowed hH N hN hperiod hstart
  exact ⟨L,R,h.left_pos,h.left_le,h.right_min,h.right_le,
    h.wall_north.1,h.wall_north.2,h.left_inside,h.head_at_one,h.right_inside⟩

-- The north labels encode the left/head/right initialization blocks.
-- The south labels are blank0 except Start's1 and the actual head color4.
example {T : ℤ → Tile} {N L R : ℕ} (h : InitialStrip T N L R) :
    (T 0).south = 1 ∧ (T 1).south = 4 ∧
    (∀ j : ℕ, 1 ≤ j → j < L →
      (T (-(j : ℤ))).north = 434 ∧ (T (-(j : ℤ))).south = 0) ∧
    (∀ j : ℕ, 2 ≤ j → j < R →
      (T (j : ℤ)).north = 436 ∧ (T (j : ℤ)).south = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h.start_at_zero]
    rfl
  · rw [h.head_at_one]
  · intro j hj hl
    rw [h.left_inside j hj hl]
    exact ⟨rfl,rfl⟩
  · intro j hj hr
    rw [h.right_inside j hj hr]
    exact ⟨rfl,rfl⟩

-- Both walls retain their precise facing colors and south seam color.
example {T : ℤ → Tile} {N L R : ℕ} (h : InitialStrip T N L R) :
    (T (-(L : ℤ))).east = 2 ∧ (T (R : ℤ)).west = 4 ∧
    (T (-(L : ℤ))).south = 437 ∧ (T (R : ℤ)).south = 437 := by
  obtain ⟨a,ha⟩ := h.left_wall
  obtain ⟨b,hb⟩ := h.right_wall
  rw [ha,hb]
  exact ⟨rfl,rfl,rfl,rfl⟩

-- Marked cyclic words need no additional strip or coprimality hypothesis.
example {N : ℕ} [NeZero N] {s : ℤ} {a : ZMod N → Fin 942}
    (h : MarkedWord N s a) :
    ∃ L R : ℕ, InitialStrip (fun x => plane N s a x 0) N L R :=
  marked_initial_strip h

#print axioms head_after_start
#print axioms left_wall_exists
#print axioms right_wall_exists
#print axioms periodic_initial_strip
#print axioms InitialStrip.wall_north
#print axioms marked_initial_strip

end DiophantineConsistency.WangTiles942InitialStripChecks
