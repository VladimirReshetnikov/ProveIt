import DiophantineConsistency.WangTiles942Language

/-!
# Exact local boundary-color classification for the actual Wang table

Only the literal finite `Allowed` language is used. Transition input heads
are at most 431; receiving output heads, including halt target 215, are at
most 433. Thus the boundary colors 434 through 438 have exactly the cases
listed below. No strip, run, halting, or tiling hypothesis is present.
-/

namespace DiophantineConsistency.WangTiles942Boundary

open WangTiles942 WangTiles942Language

set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The source states are 0 through 214, so transition heads stop at 431. -/
theorem transition_north_bound (j : Fin 430) : (transitionRow j).2.north ≤ 431 := by
  change 2 * (j.val / 2) + j.val % 2 + 2 ≤ 431
  have hj := j.isLt
  omega

/-- A receiving row may target the halt state 215, giving head 432 or 433. -/
theorem receive_south_bound {d : Bool} {q : ℕ} (hq : q ∈ targets d) (b : Fin 2) :
    headColor q b.val ≤ 433 := by
  have hq' := target_bounds d q (List.mem_toFinset.mp hq)
  have hb := b.isLt
  unfold headColor
  omega

theorem plain_or_halt_bound (a b : Fin 2) : 432*a.val+b.val ≤ 433 := by
  have ha := a.isLt
  have hb := b.isLt
  omega

/-- Complete possibilities above the nonboundary north-color range. -/
theorem high_north_cases {t : Tile} (ht : Allowed t) (hn : 434 ≤ t.north) :
    t = start ∨ t = ⟨2,434,2,0⟩ ∨ t = ⟨3,436,4,4⟩ ∨ t = ⟨4,436,4,0⟩ ∨
    (∃ p ∈ [434,435,436], t = ⟨1,438,1,p⟩) ∨
    (∃ a b : Fin 3, t = ⟨a.val^2,437,b.val,437⟩) := by
  cases ht with
  | start => exact Or.inl rfl
  | transition j => have h := transition_north_bound j; omega
  | pass a b => have h := plain_or_halt_bound a b; simp only at *; omega
  | receive d q hq b => have h := b.isLt; simp only at hn; omega
  | finish a b => have h := plain_or_halt_bound a b; simp only at hn; omega
  | initLeft => exact Or.inr (Or.inl rfl)
  | initHead => exact Or.inr (Or.inr (Or.inl rfl))
  | initRight => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | reset p hp => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p,hp,rfl⟩))))
  | seam a b => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a,b,rfl⟩))))

/-- Complete possibilities above the nonboundary south-color range. -/
theorem high_south_cases {t : Tile} (ht : Allowed t) (hs : 434 ≤ t.south) :
    (∃ a b : Fin 2, t = ⟨0,432*a.val+b.val,0,438⟩) ∨
    (∃ p ∈ [434,435,436], t = ⟨1,438,1,p⟩) ∨
    (∃ a b : Fin 3, t = ⟨a.val^2,437,b.val,437⟩) := by
  cases ht with
  | start => simp only [start] at hs; omega
  | transition j =>
      have h := Bool.toNat_le (action j).1
      dsimp only [transitionRow] at hs
      omega
  | pass a b => have h := plain_or_halt_bound a b; simp only at *; omega
  | receive d q hq b => have h := receive_south_bound hq b; simp only at hs; omega
  | finish a b => exact Or.inl ⟨a,b,rfl⟩
  | initLeft => simp only at hs; omega
  | initHead => simp only at hs; omega
  | initRight => simp only at hs; omega
  | reset p hp => exact Or.inr (Or.inl ⟨p,hp,rfl⟩)
  | seam a b => exact Or.inr (Or.inr ⟨a,b,rfl⟩)

theorem north_435_iff_start {t : Tile} (ht : Allowed t) : t.north = 435 ↔ t = start := by
  constructor
  · intro hn
    rcases high_north_cases ht (by omega) with
      rfl | rfl | rfl | rfl | ⟨p,hp,rfl⟩ | ⟨a,b,rfl⟩
    · rfl
    all_goals norm_num at hn
  · rintro rfl
    rfl

theorem north_434_iff_initLeft {t : Tile} (ht : Allowed t) :
    t.north = 434 ↔ t = ⟨2,434,2,0⟩ := by
  constructor
  · intro hn
    rcases high_north_cases ht (by omega) with
      rfl | rfl | rfl | rfl | ⟨p,hp,rfl⟩ | ⟨a,b,rfl⟩
    · norm_num [start] at hn
    · rfl
    all_goals norm_num at hn
  · rintro rfl
    rfl

/-- The head initializer has south color 4, not the old state-93 color 188. -/
theorem north_436_iff_initializers {t : Tile} (ht : Allowed t) :
    t.north = 436 ↔ t = ⟨3,436,4,4⟩ ∨ t = ⟨4,436,4,0⟩ := by
  constructor
  · intro hn
    rcases high_north_cases ht (by omega) with
      rfl | rfl | rfl | rfl | ⟨p,hp,rfl⟩ | ⟨a,b,rfl⟩
    · norm_num [start] at hn
    · norm_num at hn
    · exact Or.inl rfl
    · exact Or.inr rfl
    all_goals norm_num at hn
  · rintro (rfl | rfl) <;> rfl

theorem north_438_iff_reset {t : Tile} (ht : Allowed t) :
    t.north = 438 ↔ ∃ p ∈ [434,435,436], t = ⟨1,438,1,p⟩ := by
  constructor
  · intro hn
    rcases high_north_cases ht (by omega) with
      rfl | rfl | rfl | rfl | ⟨p,hp,rfl⟩ | ⟨a,b,rfl⟩
    · norm_num [start] at hn
    · norm_num at hn
    · norm_num at hn
    · norm_num at hn
    · exact ⟨p,hp,rfl⟩
    · norm_num at hn
  · rintro ⟨p,hp,rfl⟩
    rfl

theorem north_437_iff_seam {t : Tile} (ht : Allowed t) :
    t.north = 437 ↔ ∃ a b : Fin 3, t = ⟨a.val^2,437,b.val,437⟩ := by
  constructor
  · intro hn
    rcases high_north_cases ht (by omega) with
      rfl | rfl | rfl | rfl | ⟨p,hp,rfl⟩ | ⟨a,b,rfl⟩
    · norm_num [start] at hn
    · norm_num at hn
    · norm_num at hn
    · norm_num at hn
    · norm_num at hn
    · exact ⟨a,b,rfl⟩
  · rintro ⟨a,b,rfl⟩
    rfl

theorem south_438_iff_finish {t : Tile} (ht : Allowed t) :
    t.south = 438 ↔ ∃ a b : Fin 2, t = ⟨0,432*a.val+b.val,0,438⟩ := by
  constructor
  · intro hs
    rcases high_south_cases ht (by omega) with
      ⟨a,b,rfl⟩ | ⟨p,hp,rfl⟩ | ⟨a,b,rfl⟩
    · exact ⟨a,b,rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      simp only at hs
      omega
    · norm_num at hs
  · rintro ⟨a,b,rfl⟩
    rfl

theorem south_437_iff_seam {t : Tile} (ht : Allowed t) :
    t.south = 437 ↔ ∃ a b : Fin 3, t = ⟨a.val^2,437,b.val,437⟩ := by
  constructor
  · intro hs
    rcases high_south_cases ht (by omega) with
      ⟨a,b,rfl⟩ | ⟨p,hp,rfl⟩ | ⟨a,b,rfl⟩
    · norm_num at hs
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      simp only at hs
      omega
    · exact ⟨a,b,rfl⟩
  · rintro ⟨a,b,rfl⟩
    rfl

/-- A seam color on either vertical edge forces a full seam tile. -/
theorem north_437_iff_south_437 {t : Tile} (ht : Allowed t) :
    t.north = 437 ↔ t.south = 437 :=
  (north_437_iff_seam ht).trans (south_437_iff_seam ht).symm

/-- Each of the three initialization colors, when on a south edge,
determines its exact matching reset tile. -/
theorem south_reset_iff {t : Tile} (ht : Allowed t) (p : ℕ) (hp : p ∈ [434,435,436]) :
    t.south = p ↔ t = ⟨1,438,1,p⟩ := by
  have hb : 434 ≤ p ∧ p ≤ 436 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    omega
  constructor
  · intro hs
    rcases high_south_cases ht (by omega) with
      ⟨a,b,rfl⟩ | ⟨q,hq,rfl⟩ | ⟨a,b,rfl⟩
    · simp only at hs
      omega
    · simp only at hs
      subst q
      rfl
    · simp only at hs
      omega
  · rintro rfl
    rfl

/-- All nine finite seam combinations are actually present in the indexed table. -/
theorem seam_tile_exists (a b : Fin 3) :
    ∃ i : Fin 942, tile i = ⟨a.val^2,437,b.val,437⟩ :=
  (allowed_iff_tile _).mp (Allowed.seam a b)

end DiophantineConsistency.WangTiles942Boundary
