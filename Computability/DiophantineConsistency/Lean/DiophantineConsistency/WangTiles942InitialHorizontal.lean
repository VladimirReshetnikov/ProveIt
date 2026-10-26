import DiophantineConsistency.WangTiles942Language

/-!
# Exact horizontal initialization colors in the actual finite tile language

Every valid direction-specific rail has color at least6. Thus colors2,3,4
on a horizontal edge come only from Start, the three initializers, or the
explicit seam family. These are local classifications, with no row, strip,
periodicity, computation, or tiling premise.
-/

namespace DiophantineConsistency.WangTiles942InitialHorizontal

open WangTiles942 WangTiles942Language

set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The only allowed families with a horizontal edge between2 and4. -/
theorem small_horizontal_cases {t : Tile} (ht : Allowed t)
    (hs : (2 ≤ t.west ∧ t.west ≤ 4) ∨ (2 ≤ t.east ∧ t.east ≤ 4)) :
    t = start ∨ t = ⟨2,434,2,0⟩ ∨ t = ⟨3,436,4,4⟩ ∨ t = ⟨4,436,4,0⟩ ∨
      ∃ a b : Fin 3, t = ⟨a.val^2,437,b.val,437⟩ := by
  cases ht with
  | start => exact Or.inl rfl
  | transition j =>
      have hr := (valid_rail_range (action_target_mem j)).1
      dsimp only [transitionRow] at hs
      cases hd : (action j).2.1 <;>
        simp only [hd, Bool.toNat_false, Bool.toNat_true, Nat.sub_zero,
          Nat.sub_self, Nat.one_mul, Nat.zero_mul] at * <;> omega
  | pass a b => simp only at hs; omega
  | receive d q hq b =>
      have hr := (valid_rail_range hq).1
      cases d <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.sub_zero,
        Nat.sub_self, Nat.one_mul, Nat.zero_mul] at hs hr <;> omega
  | finish a b => simp only at hs; omega
  | initLeft => exact Or.inr (Or.inl rfl)
  | initHead => exact Or.inr (Or.inr (Or.inl rfl))
  | initRight => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | reset p hp => simp only at hs; omega
  | seam a b => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a,b,rfl⟩)))

/-- East2 either continues the left initializer or enters a seam with b=2. -/
theorem east_2_iff_initLeft_or_seam {t : Tile} (ht : Allowed t) :
    t.east = 2 ↔ t = ⟨2,434,2,0⟩ ∨ ∃ a : Fin 3, t = ⟨a.val^2,437,2,437⟩ := by
  constructor
  · intro he
    rcases small_horizontal_cases ht (Or.inr (by omega)) with
      rfl | rfl | rfl | rfl | ⟨a,b,rfl⟩
    · norm_num [start] at he
    · exact Or.inl rfl
    · norm_num at he
    · norm_num at he
    · exact Or.inr ⟨a, by simp only [show b.val = 2 from he]⟩
  · rintro (rfl | ⟨a,rfl⟩) <;> rfl

/-- West3 determines the actual head initializer, whose south color is4. -/
theorem west_3_iff_initHead {t : Tile} (ht : Allowed t) :
    t.west = 3 ↔ t = ⟨3,436,4,4⟩ := by
  constructor
  · intro hw
    rcases small_horizontal_cases ht (Or.inl (by omega)) with
      rfl | rfl | rfl | rfl | ⟨a,b,rfl⟩
    · norm_num [start] at hw
    · norm_num at hw
    · rfl
    · norm_num at hw
    · have ha := a.isLt
      simp only at hw
      interval_cases a.val <;> norm_num at hw
  · rintro rfl
    rfl

/-- West4 either continues the right initializer or enters a seam with a=2. -/
theorem west_4_iff_initRight_or_seam {t : Tile} (ht : Allowed t) :
    t.west = 4 ↔ t = ⟨4,436,4,0⟩ ∨ ∃ b : Fin 3, t = ⟨4,437,b.val,437⟩ := by
  constructor
  · intro hw
    rcases small_horizontal_cases ht (Or.inl (by omega)) with
      rfl | rfl | rfl | rfl | ⟨a,b,rfl⟩
    · norm_num [start] at hw
    · norm_num at hw
    · norm_num at hw
    · exact Or.inl rfl
    · exact Or.inr ⟨b, by simp only [show a.val^2 = 4 from hw]⟩
  · rintro (rfl | ⟨b,rfl⟩) <;> rfl

/-- East3 uniquely identifies Start in the entire allowed finite language. -/
theorem east_3_iff_start {t : Tile} (ht : Allowed t) : t.east = 3 ↔ t = start := by
  constructor
  · intro he
    rcases small_horizontal_cases ht (Or.inr (by omega)) with
      rfl | rfl | rfl | rfl | ⟨a,b,rfl⟩
    · rfl
    · norm_num at he
    · norm_num at he
    · norm_num at he
    · have hb := b.isLt
      simp only at he
      omega
  · rintro rfl
    rfl

/-- West2 cannot be a seam square; it is exactly Start or initLeft. -/
theorem west_2_iff_start_or_initLeft {t : Tile} (ht : Allowed t) :
    t.west = 2 ↔ t = start ∨ t = ⟨2,434,2,0⟩ := by
  constructor
  · intro hw
    rcases small_horizontal_cases ht (Or.inl (by omega)) with
      rfl | rfl | rfl | rfl | ⟨a,b,rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · norm_num at hw
    · norm_num at hw
    · have ha := a.isLt
      simp only at hw
      interval_cases a.val <;> norm_num at hw
  · rintro (rfl | rfl) <;> rfl

/-- The seam exception must be excluded explicitly to force initLeft. -/
theorem east_2_nonseam {t : Tile} (ht : Allowed t) (he : t.east = 2)
    (hn : t.north ≠ 437) : t = ⟨2,434,2,0⟩ := by
  rcases (east_2_iff_initLeft_or_seam ht).mp he with he | ⟨a,rfl⟩
  · exact he
  · exact False.elim (hn rfl)

/-- The seam exception must be excluded explicitly to force initRight. -/
theorem west_4_nonseam {t : Tile} (ht : Allowed t) (hw : t.west = 4)
    (hn : t.north ≠ 437) : t = ⟨4,436,4,0⟩ := by
  rcases (west_4_iff_initRight_or_seam ht).mp hw with hw | ⟨b,rfl⟩
  · exact hw
  · exact False.elim (hn rfl)

end DiophantineConsistency.WangTiles942InitialHorizontal
