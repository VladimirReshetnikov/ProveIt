import SquaredSquare.Basic

/-!
# Duijvestijn's perfect squared square of order 21

A. J. W. Duijvestijn's 1978 dissection cuts the square of side `112` into `21`
squares with pairwise distinct sides

`2, 4, 6, 7, 8, 9, 11, 15, 16, 17, 18, 19, 24, 25, 27, 29, 33, 35, 37, 42, 50`.

The placement data below (bottom-left corner and side of each piece, integer
coordinates) is the decoded Bouwkamp code
`(50, 35, 27) (8, 19) (15, 17, 11) (6, 24) (29, 25, 9, 2) (7, 18) (16) (42)
(4, 37) (33)`.

All combinatorial facts about the data — in-bounds placement, pairwise
separation of the open pieces, distinct sides, and coverage of every unit grid
cell — are decidable statements about natural numbers discharged by `decide`,
i.e. checked by the Lean kernel.  The real-plane statements are then obtained
by elementary lifting lemmas: a point of `[0, 112]²` lies in the unit cell of
its coordinates' floors, and that cell is contained in one of the 21 closed
pieces.
-/

namespace LeanProofs

namespace SquaredSquare

/-- Bottom-left corners and sides `(x, y, s)` of the 21 pieces of
Duijvestijn's order-21 perfect squared square of side 112. -/
def tileData : List (ℕ × ℕ × ℕ) :=
  [(0, 62, 50), (50, 77, 35), (85, 85, 27), (85, 77, 8), (93, 66, 19),
   (50, 62, 15), (65, 60, 17), (82, 66, 11), (82, 60, 6), (88, 42, 24),
   (0, 33, 29), (29, 37, 25), (54, 53, 9), (63, 60, 2), (63, 53, 7),
   (70, 42, 18), (54, 37, 16), (70, 0, 42), (29, 33, 4), (33, 0, 37),
   (0, 0, 33)]

theorem tileData_length : tileData.length = 21 := rfl

/-- Every piece has a positive side and fits inside `[0, 112]²`. -/
theorem tileData_bounds :
    ∀ t ∈ tileData, 0 < t.2.2 ∧ t.1 + t.2.2 ≤ 112 ∧ t.2.1 + t.2.2 ≤ 112 := by
  decide

/-- Any two distinct pieces are separated by an axis-parallel line, so their
open interiors are disjoint. -/
theorem tileData_sep : tileData.Pairwise fun t u =>
    t.1 + t.2.2 ≤ u.1 ∨ u.1 + u.2.2 ≤ t.1 ∨
    t.2.1 + t.2.2 ≤ u.2.1 ∨ u.2.1 + u.2.2 ≤ t.2.1 := by
  decide

/-- The sides are pairwise distinct (and positive). -/
theorem tileData_sides : tileData.Pairwise fun t u =>
    0 < t.2.2 ∧ 0 < u.2.2 ∧ t.2.2 ≠ u.2.2 := by
  decide

set_option maxRecDepth 100000 in
/-- Every unit grid cell `[i, i+1] × [j, j+1]` of `[0, 112]²` is contained in
one of the pieces.  This is the exact-cover certificate; it is checked
directly by the kernel. -/
theorem tileData_cells : ∀ i < 112, ∀ j < 112, ∃ t ∈ tileData,
    t.1 ≤ i ∧ i + 1 ≤ t.1 + t.2.2 ∧ t.2.1 ≤ j ∧ j + 1 ≤ t.2.1 + t.2.2 := by
  decide +kernel

/-- Interpret an integer data triple as a placed square in the plane. -/
def toSq (t : ℕ × ℕ × ℕ) : Sq :=
  ⟨(t.1 : ℝ), (t.2.1 : ℝ), (t.2.2 : ℝ)⟩

/-- The 21 pieces of Duijvestijn's dissection as real placed squares. -/
def duijvestijnTiles : List Sq :=
  tileData.map toSq

theorem duijvestijnTiles_length : duijvestijnTiles.length = 21 := by
  rw [duijvestijnTiles, List.length_map, tileData_length]

theorem duijvestijn_pos : ∀ q ∈ duijvestijnTiles, 0 < q.s := by
  intro q hq
  rw [duijvestijnTiles, List.mem_map] at hq
  obtain ⟨t, ht, rfl⟩ := hq
  have h := (tileData_bounds t ht).1
  show (0 : ℝ) < (t.2.2 : ℝ)
  exact_mod_cast h

theorem duijvestijn_disj :
    duijvestijnTiles.Pairwise fun p q => Disjoint p.inn q.inn := by
  rw [duijvestijnTiles, List.pairwise_map]
  refine tileData_sep.imp ?_
  intro t u h
  rw [Set.disjoint_left]
  intro p hp hp'
  rw [Sq.mem_inn] at hp hp'
  rcases h with h | h | h | h
  · have hc : (t.1 : ℝ) + (t.2.2 : ℝ) ≤ (u.1 : ℝ) := by exact_mod_cast h
    have := hp.1.2
    have := hp'.1.1
    simp only [toSq] at *
    linarith
  · have hc : (u.1 : ℝ) + (u.2.2 : ℝ) ≤ (t.1 : ℝ) := by exact_mod_cast h
    have := hp'.1.2
    have := hp.1.1
    simp only [toSq] at *
    linarith
  · have hc : (t.2.1 : ℝ) + (t.2.2 : ℝ) ≤ (u.2.1 : ℝ) := by exact_mod_cast h
    have := hp.2.2
    have := hp'.2.1
    simp only [toSq] at *
    linarith
  · have hc : (u.2.1 : ℝ) + (u.2.2 : ℝ) ≤ (t.2.1 : ℝ) := by exact_mod_cast h
    have := hp'.2.2
    have := hp.2.1
    simp only [toSq] at *
    linarith

theorem duijvestijn_subset :
    (⋃ q ∈ duijvestijnTiles, q.toSet) ⊆ bigSquare 112 := by
  intro p hp
  simp only [Set.mem_iUnion, exists_prop] at hp
  obtain ⟨q, hq, hpq⟩ := hp
  rw [duijvestijnTiles, List.mem_map] at hq
  obtain ⟨t, ht, rfl⟩ := hq
  obtain ⟨-, hx, hy⟩ := tileData_bounds t ht
  rw [Sq.mem_toSet] at hpq
  have hx' : (t.1 : ℝ) + (t.2.2 : ℝ) ≤ 112 := by exact_mod_cast hx
  have hy' : (t.2.1 : ℝ) + (t.2.2 : ℝ) ≤ 112 := by exact_mod_cast hy
  have hx0 : (0 : ℝ) ≤ (t.1 : ℝ) := Nat.cast_nonneg _
  have hy0 : (0 : ℝ) ≤ (t.2.1 : ℝ) := Nat.cast_nonneg _
  simp only [toSq] at hpq
  rw [mem_bigSquare]
  exact ⟨⟨by linarith [hpq.1.1], by linarith [hpq.1.2]⟩,
    by linarith [hpq.2.1], by linarith [hpq.2.2]⟩

/-- A coordinate of `[0, 112]` lies in the unit interval of its (clamped)
floor. -/
theorem exists_unit_cell {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 112) :
    ∃ i : ℕ, i < 112 ∧ (i : ℝ) ≤ u ∧ u ≤ (i : ℝ) + 1 := by
  rcases le_or_gt (⌊u⌋₊) 111 with h | h
  · refine ⟨⌊u⌋₊, by omega, Nat.floor_le h0, (Nat.lt_floor_add_one u).le⟩
  · refine ⟨111, by omega, ?_, ?_⟩
    · have h112 : (112 : ℕ) ≤ ⌊u⌋₊ := h
      have : ((112 : ℕ) : ℝ) ≤ u := by
        exact_mod_cast (Nat.le_floor_iff h0).mp h112
      norm_num at this ⊢
      linarith
    · norm_num
      linarith

theorem bigSquare_subset_duijvestijn :
    bigSquare 112 ⊆ ⋃ q ∈ duijvestijnTiles, q.toSet := by
  intro p hp
  rw [mem_bigSquare] at hp
  obtain ⟨⟨hu0, hu1⟩, hv0, hv1⟩ := hp
  obtain ⟨i, hi, hiu, hiu'⟩ := exists_unit_cell hu0 hu1
  obtain ⟨j, hj, hjv, hjv'⟩ := exists_unit_cell hv0 hv1
  obtain ⟨t, ht, h1, h2, h3, h4⟩ := tileData_cells i hi j hj
  simp only [Set.mem_iUnion, exists_prop]
  refine ⟨toSq t, List.mem_map_of_mem ht, ?_⟩
  rw [Sq.mem_toSet]
  have c1 : (t.1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast h1
  have c2 : (i : ℝ) + 1 ≤ (t.1 : ℝ) + (t.2.2 : ℝ) := by exact_mod_cast h2
  have c3 : (t.2.1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast h3
  have c4 : (j : ℝ) + 1 ≤ (t.2.1 : ℝ) + (t.2.2 : ℝ) := by exact_mod_cast h4
  simp only [toSq]
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- Duijvestijn's 21 squares dissect the square of side 112. -/
theorem duijvestijn_isDissection : IsDissection 112 duijvestijnTiles :=
  ⟨duijvestijn_pos, duijvestijn_disj,
    Set.Subset.antisymm duijvestijn_subset bigSquare_subset_duijvestijn⟩

/-- The 21 pieces are pairwise non-congruent: their sides are pairwise
distinct. -/
theorem duijvestijn_noncongruent :
    duijvestijnTiles.Pairwise fun p q => ¬Congruent p.toSet q.toSet := by
  rw [duijvestijnTiles, List.pairwise_map]
  refine tileData_sides.imp ?_
  intro t u h
  refine noncongruent_of_side_ne ?_ ?_ ?_
  · show (0 : ℝ) < (t.2.2 : ℝ)
    exact_mod_cast h.1
  · show (0 : ℝ) < (u.2.2 : ℝ)
    exact_mod_cast h.2.1
  · show (t.2.2 : ℝ) ≠ (u.2.2 : ℝ)
    exact_mod_cast h.2.2

/-- **Duijvestijn's perfect squared square.**  The square of side 112 is cut
into 21 pairwise non-congruent squares. -/
theorem duijvestijn_perfect : IsPerfectSquaredSquare 112 duijvestijnTiles :=
  ⟨duijvestijn_isDissection, by rw [duijvestijnTiles_length]; norm_num,
    duijvestijn_noncongruent⟩

/-- **Squaring the square (existence).**  Some square can be cut into finitely
many pairwise non-congruent squares — indeed into 21 of them. -/
theorem exists_perfect_squared_square :
    ∃ l : List Sq, l.length = 21 ∧ IsPerfectSquaredSquare 112 l :=
  ⟨duijvestijnTiles, duijvestijnTiles_length, duijvestijn_perfect⟩

end SquaredSquare

end LeanProofs
