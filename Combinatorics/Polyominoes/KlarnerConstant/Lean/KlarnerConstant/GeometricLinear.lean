import KlarnerConstant.Patterns
import KlarnerConstant.Counting

/-!
# The five linear pattern partitions in Bui's system

The same-size identities

`F = G + P`, `G = E + Q`, `H = D + S`, `R = Y + W`, and `T = X + V`

are finite geometric partitions, not asymptotic estimates.  Four split the
same anchor set according to whether one cell to the east is occupied.  The
first splits an `F` anchor according to occupancy immediately west; in the
occupied branch, translating the anchor one cell west gives a `P` anchor.

This file proves the identities first for every individual cell set, then for
the aggregate occurrence counts over all normalized `n`-cell polyominoes, and
finally for their rational coefficient sequences.
-/

namespace LeanProofs.KlarnerConstant

private def westOffset : Cell := (-1, 0)
private def eastOffset : Cell := (1, 0)
private def twoEastOffset : Cell := (2, 0)

namespace OffsetPattern

/-- Add one offset to the required part of a local pattern. -/
def requireOffset (pattern : OffsetPattern) (offset : Cell) : OffsetPattern where
  required := insert offset pattern.required
  forbidden := pattern.forbidden

/-- Add one offset to the forbidden part of a local pattern. -/
def forbidOffset (pattern : OffsetPattern) (offset : Cell) : OffsetPattern where
  required := pattern.required
  forbidden := insert offset pattern.forbidden

theorem occursAt_requireOffset_iff (pattern : OffsetPattern) (offset : Cell)
    (cells : Finset Cell) (anchor : Cell) :
    (pattern.requireOffset offset).OccursAt cells anchor ↔
      pattern.OccursAt cells anchor ∧ anchor + offset ∈ cells := by
  constructor
  · rintro ⟨hrequired, hforbidden⟩
    refine ⟨⟨?_, hforbidden⟩, ?_⟩
    · intro other hother
      exact hrequired other (Finset.mem_insert_of_mem hother)
    · exact hrequired offset (Finset.mem_insert_self offset pattern.required)
  · rintro ⟨⟨hrequired, hforbidden⟩, hoffset⟩
    refine ⟨?_, hforbidden⟩
    intro other hother
    change other ∈ insert offset pattern.required at hother
    rw [Finset.mem_insert] at hother
    rcases hother with rfl | hother
    · exact hoffset
    · exact hrequired other hother

theorem occursAt_forbidOffset_iff (pattern : OffsetPattern) (offset : Cell)
    (cells : Finset Cell) (anchor : Cell) :
    (pattern.forbidOffset offset).OccursAt cells anchor ↔
      pattern.OccursAt cells anchor ∧ anchor + offset ∉ cells := by
  constructor
  · rintro ⟨hrequired, hforbidden⟩
    refine ⟨⟨hrequired, ?_⟩, ?_⟩
    · intro other hother
      exact hforbidden other (Finset.mem_insert_of_mem hother)
    · exact hforbidden offset (Finset.mem_insert_self offset pattern.forbidden)
  · rintro ⟨⟨hrequired, hforbidden⟩, hoffset⟩
    refine ⟨hrequired, ?_⟩
    intro other hother
    change other ∈ insert offset pattern.forbidden at hother
    rw [Finset.mem_insert] at hother
    rcases hother with rfl | hother
    · exact hoffset
    · exact hforbidden other hother

theorem occurrenceAnchors_requireOffset (pattern : OffsetPattern) (offset : Cell)
    (cells : Finset Cell) :
    (pattern.requireOffset offset).occurrenceAnchors cells =
      (pattern.occurrenceAnchors cells).filter
        (fun anchor => anchor + offset ∈ cells) := by
  ext anchor
  simp only [occurrenceAnchors, Finset.mem_filter,
    occursAt_requireOffset_iff]
  constructor
  · rintro ⟨hanchor, hpattern, hoffset⟩
    exact ⟨⟨hanchor, hpattern⟩, hoffset⟩
  · rintro ⟨⟨hanchor, hpattern⟩, hoffset⟩
    exact ⟨hanchor, hpattern, hoffset⟩

theorem occurrenceAnchors_forbidOffset (pattern : OffsetPattern) (offset : Cell)
    (cells : Finset Cell) :
    (pattern.forbidOffset offset).occurrenceAnchors cells =
      (pattern.occurrenceAnchors cells).filter
        (fun anchor => anchor + offset ∉ cells) := by
  ext anchor
  simp only [occurrenceAnchors, Finset.mem_filter,
    occursAt_forbidOffset_iff]
  constructor
  · rintro ⟨hanchor, hpattern, hoffset⟩
    exact ⟨⟨hanchor, hpattern⟩, hoffset⟩
  · rintro ⟨⟨hanchor, hpattern⟩, hoffset⟩
    exact ⟨hanchor, hpattern, hoffset⟩

/-- Every occurrence set splits into the branches in which one distinguished
offset is respectively absent and present. -/
theorem occurrenceCount_eq_forbid_add_require (pattern : OffsetPattern)
    (offset : Cell) (cells : Finset Cell) :
    pattern.occurrenceCount cells =
      (pattern.forbidOffset offset).occurrenceCount cells +
      (pattern.requireOffset offset).occurrenceCount cells := by
  classical
  unfold occurrenceCount
  rw [occurrenceAnchors_forbidOffset, occurrenceAnchors_requireOffset]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := pattern.occurrenceAnchors cells)
    (p := fun anchor => anchor + offset ∈ cells)
  simpa only [add_comm] using hsplit.symm

end OffsetPattern

private theorem offsetPattern_ext {a b : OffsetPattern}
    (hrequired : a.required = b.required)
    (hforbidden : a.forbidden = b.forbidden) : a = b := by
  cases a with
  | mk ar af =>
      cases b with
      | mk br bf =>
          dsimp at hrequired hforbidden
          cases hrequired
          cases hforbidden
          rfl

private theorem buiGPattern_eq_forbid_f_west :
    buiGPattern = buiFPattern.forbidOffset westOffset := by
  apply offsetPattern_ext
  · ext offset
    simp [buiGPattern, buiFPattern, OffsetPattern.forbidOffset,
      westOffset, or_assoc, or_left_comm, or_comm]
  · ext offset
    simp [buiGPattern, buiFPattern, OffsetPattern.forbidOffset,
      westOffset, or_assoc, or_left_comm, or_comm]

private theorem buiEPattern_eq_forbid_g_east :
    buiEPattern = buiGPattern.forbidOffset eastOffset := by
  apply offsetPattern_ext
  · ext offset
    simp [buiEPattern, buiGPattern, OffsetPattern.forbidOffset,
      eastOffset, or_assoc, or_left_comm, or_comm]
  · ext offset
    simp [buiEPattern, buiGPattern, OffsetPattern.forbidOffset,
      eastOffset, or_assoc, or_left_comm, or_comm]

private theorem buiQPattern_eq_require_g_east :
    buiQPattern = buiGPattern.requireOffset eastOffset := by
  apply offsetPattern_ext
  · ext offset
    simp [buiQPattern, buiGPattern, OffsetPattern.requireOffset,
      eastOffset, or_assoc, or_left_comm, or_comm]
  · ext offset
    simp [buiQPattern, buiGPattern, OffsetPattern.requireOffset,
      eastOffset, or_assoc, or_left_comm, or_comm]

private theorem buiDPattern_eq_forbid_h_east :
    buiDPattern = buiHPattern.forbidOffset eastOffset := by
  apply offsetPattern_ext
  · ext offset
    simp [buiDPattern, buiHPattern, OffsetPattern.forbidOffset,
      eastOffset, or_assoc, or_left_comm, or_comm]
  · ext offset
    simp [buiDPattern, buiHPattern, OffsetPattern.forbidOffset,
      eastOffset, or_assoc, or_left_comm, or_comm]

private theorem buiSPattern_eq_require_h_east :
    buiSPattern = buiHPattern.requireOffset eastOffset := by
  apply offsetPattern_ext
  · ext offset
    simp [buiSPattern, buiHPattern, OffsetPattern.requireOffset,
      eastOffset, or_assoc, or_left_comm, or_comm]
  · ext offset
    simp [buiSPattern, buiHPattern, OffsetPattern.requireOffset,
      eastOffset, or_assoc, or_left_comm, or_comm]

private theorem buiYPattern_eq_forbid_r_twoEast :
    buiYPattern = buiRPattern.forbidOffset twoEastOffset := by
  apply offsetPattern_ext
  · ext offset
    simp [buiYPattern, buiRPattern, OffsetPattern.forbidOffset,
      twoEastOffset, or_assoc, or_left_comm, or_comm]
  · ext offset
    simp [buiYPattern, buiRPattern, OffsetPattern.forbidOffset,
      twoEastOffset, or_assoc, or_left_comm, or_comm]

private theorem buiWPattern_eq_require_r_twoEast :
    buiWPattern = buiRPattern.requireOffset twoEastOffset := by
  apply offsetPattern_ext
  · ext offset
    simp [buiWPattern, buiRPattern, OffsetPattern.requireOffset,
      twoEastOffset, or_assoc, or_left_comm, or_comm]
  · ext offset
    simp [buiWPattern, buiRPattern, OffsetPattern.requireOffset,
      twoEastOffset, or_assoc, or_left_comm, or_comm]

private theorem buiXPattern_eq_forbid_t_twoEast :
    buiXPattern = buiTPattern.forbidOffset twoEastOffset := by
  apply offsetPattern_ext
  · ext offset
    simp [buiXPattern, buiTPattern, OffsetPattern.forbidOffset,
      twoEastOffset, or_assoc, or_left_comm, or_comm]
  · ext offset
    simp [buiXPattern, buiTPattern, OffsetPattern.forbidOffset,
      twoEastOffset, or_assoc, or_left_comm, or_comm]

private theorem buiVPattern_eq_require_t_twoEast :
    buiVPattern = buiTPattern.requireOffset twoEastOffset := by
  apply offsetPattern_ext
  · ext offset
    simp [buiVPattern, buiTPattern, OffsetPattern.requireOffset,
      twoEastOffset, or_assoc, or_left_comm, or_comm]
  · ext offset
    simp [buiVPattern, buiTPattern, OffsetPattern.requireOffset,
      twoEastOffset, or_assoc, or_left_comm, or_comm]

/-- Requiring the western neighbor of an `F` anchor is the same local
configuration as a `P` occurrence reanchored one cell west. -/
private theorem occursAt_require_f_west_iff_p (cells : Finset Cell)
    (anchor : Cell) :
    (buiFPattern.requireOffset westOffset).OccursAt cells anchor ↔
      buiPPattern.OccursAt cells (anchor + westOffset) := by
  rw [OffsetPattern.occursAt_requireOffset_iff]
  simp [OffsetPattern.OccursAt, buiFPattern, buiPPattern, westOffset,
    add_assoc, and_assoc, and_left_comm, and_comm]

private theorem require_f_west_image_eq_p_anchors (cells : Finset Cell) :
    ((buiFPattern.requireOffset westOffset).occurrenceAnchors cells).image
        (fun anchor => anchor + westOffset) =
      buiPPattern.occurrenceAnchors cells := by
  classical
  ext anchor
  constructor
  · intro hanchor
    rcases Finset.mem_image.mp hanchor with ⟨source, hsource, rfl⟩
    rw [OffsetPattern.occurrenceAnchors, Finset.mem_filter] at hsource ⊢
    have hsplit :=
      (OffsetPattern.occursAt_requireOffset_iff
        buiFPattern westOffset cells source).mp hsource.2
    exact ⟨hsplit.2, (occursAt_require_f_west_iff_p cells source).mp hsource.2⟩
  · intro hanchor
    rw [OffsetPattern.occurrenceAnchors, Finset.mem_filter] at hanchor
    refine Finset.mem_image.mpr ⟨anchor + eastOffset, ?_, ?_⟩
    · rw [OffsetPattern.occurrenceAnchors, Finset.mem_filter]
      have heast : anchor + eastOffset ∈ cells := by
        exact hanchor.2.1 eastOffset (by simp [buiPPattern, eastOffset])
      refine ⟨heast, ?_⟩
      apply (occursAt_require_f_west_iff_p cells (anchor + eastOffset)).mpr
      have heq : (anchor + eastOffset) + westOffset = anchor := by
        apply Prod.ext <;> simp [eastOffset, westOffset]
      simpa only [heq] using hanchor.2
    · simp [eastOffset, westOffset, add_assoc]

private theorem require_f_west_count_eq_p (cells : Finset Cell) :
    (buiFPattern.requireOffset westOffset).occurrenceCount cells =
      buiPPattern.occurrenceCount cells := by
  classical
  unfold OffsetPattern.occurrenceCount
  let translateWest : Cell → Cell := fun anchor => anchor + westOffset
  have hinjective : Function.Injective translateWest := by
    intro a b hab
    exact add_right_cancel hab
  calc
    ((buiFPattern.requireOffset westOffset).occurrenceAnchors cells).card =
        (((buiFPattern.requireOffset westOffset).occurrenceAnchors cells).image
          translateWest).card :=
      (Finset.card_image_of_injective _ hinjective).symm
    _ = (buiPPattern.occurrenceAnchors cells).card := by
      rw [require_f_west_image_eq_p_anchors]

/-- The first same-size partition, including its one-cell reanchoring. -/
theorem buiF_occurrenceCount_eq_g_add_p (cells : Finset Cell) :
    buiFPattern.occurrenceCount cells =
      buiGPattern.occurrenceCount cells + buiPPattern.occurrenceCount cells := by
  calc
    buiFPattern.occurrenceCount cells =
        (buiFPattern.forbidOffset westOffset).occurrenceCount cells +
        (buiFPattern.requireOffset westOffset).occurrenceCount cells :=
      OffsetPattern.occurrenceCount_eq_forbid_add_require _ _ _
    _ = buiGPattern.occurrenceCount cells + buiPPattern.occurrenceCount cells := by
      rw [← buiGPattern_eq_forbid_f_west, require_f_west_count_eq_p]

/-- Split a `G` anchor by occupancy immediately east. -/
theorem buiG_occurrenceCount_eq_e_add_q (cells : Finset Cell) :
    buiGPattern.occurrenceCount cells =
      buiEPattern.occurrenceCount cells + buiQPattern.occurrenceCount cells := by
  rw [buiEPattern_eq_forbid_g_east, buiQPattern_eq_require_g_east]
  exact OffsetPattern.occurrenceCount_eq_forbid_add_require _ _ _

/-- Split an `H` anchor by occupancy immediately east. -/
theorem buiH_occurrenceCount_eq_d_add_s (cells : Finset Cell) :
    buiHPattern.occurrenceCount cells =
      buiDPattern.occurrenceCount cells + buiSPattern.occurrenceCount cells := by
  rw [buiDPattern_eq_forbid_h_east, buiSPattern_eq_require_h_east]
  exact OffsetPattern.occurrenceCount_eq_forbid_add_require _ _ _

/-- Split an `R` anchor by occupancy two cells east. -/
theorem buiR_occurrenceCount_eq_y_add_w (cells : Finset Cell) :
    buiRPattern.occurrenceCount cells =
      buiYPattern.occurrenceCount cells + buiWPattern.occurrenceCount cells := by
  rw [buiYPattern_eq_forbid_r_twoEast, buiWPattern_eq_require_r_twoEast]
  exact OffsetPattern.occurrenceCount_eq_forbid_add_require _ _ _

/-- Split a `T` anchor by occupancy two cells east. -/
theorem buiT_occurrenceCount_eq_x_add_v (cells : Finset Cell) :
    buiTPattern.occurrenceCount cells =
      buiXPattern.occurrenceCount cells + buiVPattern.occurrenceCount cells := by
  rw [buiXPattern_eq_forbid_t_twoEast, buiVPattern_eq_require_t_twoEast]
  exact OffsetPattern.occurrenceCount_eq_forbid_add_require _ _ _

/-- Aggregate occurrences of one named pattern over all normalized
`n`-cell polyominoes. -/
noncomputable def BuiNeighborhood.aggregateOccurrenceCount
    (kind : BuiNeighborhood) (n : ℕ) : ℕ :=
  ∑ P : NormalizedPolyomino n, kind.occurrenceCount P.toPolyomino

/-- The rational coefficient corresponding to the aggregate named-pattern
count. -/
noncomputable def BuiNeighborhood.coefficient
    (kind : BuiNeighborhood) (n : ℕ) : ℚ :=
  kind.aggregateOccurrenceCount n

private theorem aggregate_eq_add_of_pointwise
    {left right₁ right₂ : BuiNeighborhood}
    (h : ∀ P : Polyomino,
      left.occurrenceCount P = right₁.occurrenceCount P + right₂.occurrenceCount P)
    (n : ℕ) :
    left.aggregateOccurrenceCount n =
      right₁.aggregateOccurrenceCount n + right₂.aggregateOccurrenceCount n := by
  classical
  unfold BuiNeighborhood.aggregateOccurrenceCount
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun P _ => h P.toPolyomino

theorem buiF_aggregateOccurrenceCount_eq_g_add_p (n : ℕ) :
    BuiNeighborhood.f.aggregateOccurrenceCount n =
      BuiNeighborhood.g.aggregateOccurrenceCount n +
        BuiNeighborhood.p.aggregateOccurrenceCount n := by
  apply aggregate_eq_add_of_pointwise
  intro P
  exact buiF_occurrenceCount_eq_g_add_p P.cells

theorem buiG_aggregateOccurrenceCount_eq_e_add_q (n : ℕ) :
    BuiNeighborhood.g.aggregateOccurrenceCount n =
      BuiNeighborhood.e.aggregateOccurrenceCount n +
        BuiNeighborhood.q.aggregateOccurrenceCount n := by
  apply aggregate_eq_add_of_pointwise
  intro P
  exact buiG_occurrenceCount_eq_e_add_q P.cells

theorem buiH_aggregateOccurrenceCount_eq_d_add_s (n : ℕ) :
    BuiNeighborhood.h.aggregateOccurrenceCount n =
      BuiNeighborhood.d.aggregateOccurrenceCount n +
        BuiNeighborhood.s.aggregateOccurrenceCount n := by
  apply aggregate_eq_add_of_pointwise
  intro P
  exact buiH_occurrenceCount_eq_d_add_s P.cells

theorem buiR_aggregateOccurrenceCount_eq_y_add_w (n : ℕ) :
    BuiNeighborhood.r.aggregateOccurrenceCount n =
      BuiNeighborhood.y.aggregateOccurrenceCount n +
        BuiNeighborhood.w.aggregateOccurrenceCount n := by
  apply aggregate_eq_add_of_pointwise
  intro P
  exact buiR_occurrenceCount_eq_y_add_w P.cells

theorem buiT_aggregateOccurrenceCount_eq_x_add_v (n : ℕ) :
    BuiNeighborhood.t.aggregateOccurrenceCount n =
      BuiNeighborhood.x.aggregateOccurrenceCount n +
        BuiNeighborhood.v.aggregateOccurrenceCount n := by
  apply aggregate_eq_add_of_pointwise
  intro P
  exact buiT_occurrenceCount_eq_x_add_v P.cells

private theorem coefficient_eq_add_of_aggregate
    {left right₁ right₂ : BuiNeighborhood} {n : ℕ}
    (h : left.aggregateOccurrenceCount n =
      right₁.aggregateOccurrenceCount n + right₂.aggregateOccurrenceCount n) :
    left.coefficient n = right₁.coefficient n + right₂.coefficient n := by
  change (left.aggregateOccurrenceCount n : ℚ) =
    (right₁.aggregateOccurrenceCount n : ℚ) +
      (right₂.aggregateOccurrenceCount n : ℚ)
  exact_mod_cast h

/-- The five exact same-index coefficient identities. -/
theorem buiF_coefficient_eq_g_add_p (n : ℕ) :
    BuiNeighborhood.f.coefficient n =
      BuiNeighborhood.g.coefficient n + BuiNeighborhood.p.coefficient n :=
  coefficient_eq_add_of_aggregate (buiF_aggregateOccurrenceCount_eq_g_add_p n)

theorem buiG_coefficient_eq_e_add_q (n : ℕ) :
    BuiNeighborhood.g.coefficient n =
      BuiNeighborhood.e.coefficient n + BuiNeighborhood.q.coefficient n :=
  coefficient_eq_add_of_aggregate (buiG_aggregateOccurrenceCount_eq_e_add_q n)

theorem buiH_coefficient_eq_d_add_s (n : ℕ) :
    BuiNeighborhood.h.coefficient n =
      BuiNeighborhood.d.coefficient n + BuiNeighborhood.s.coefficient n :=
  coefficient_eq_add_of_aggregate (buiH_aggregateOccurrenceCount_eq_d_add_s n)

theorem buiR_coefficient_eq_y_add_w (n : ℕ) :
    BuiNeighborhood.r.coefficient n =
      BuiNeighborhood.y.coefficient n + BuiNeighborhood.w.coefficient n :=
  coefficient_eq_add_of_aggregate (buiR_aggregateOccurrenceCount_eq_y_add_w n)

theorem buiT_coefficient_eq_x_add_v (n : ℕ) :
    BuiNeighborhood.t.coefficient n =
      BuiNeighborhood.x.coefficient n + BuiNeighborhood.v.coefficient n :=
  coefficient_eq_add_of_aggregate (buiT_aggregateOccurrenceCount_eq_x_add_v n)

end LeanProofs.KlarnerConstant
