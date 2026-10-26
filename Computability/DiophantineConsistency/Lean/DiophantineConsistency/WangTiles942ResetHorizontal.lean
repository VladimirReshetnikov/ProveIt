import DiophantineConsistency.WangTiles942Language

/-!
# Exact horizontal reset color in the actual finite tile language

A horizontal color 1 belongs only to a reset tile or an explicit seam
tile. The seam exception is retained in both directions. These are local
finite-table statements, not a claim that any whole row is a reset row.
-/

namespace DiophantineConsistency.WangTiles942ResetHorizontal

open WangTiles942 WangTiles942Language

set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Every possible allowed tile with a horizontal edge of color 1. -/
theorem horizontal_one_cases {t : Tile} (ht : Allowed t)
    (h1 : t.west = 1 ∨ t.east = 1) :
    (∃ p ∈ [434,435,436], t = ⟨1,438,1,p⟩) ∨
    (∃ a b : Fin 3, t = ⟨a.val^2,437,b.val,437⟩) := by
  cases ht with
  | start => norm_num [start] at h1
  | transition j =>
      have hr := (valid_rail_range (action_target_mem j)).1
      dsimp only [transitionRow] at h1
      cases hd : (action j).2.1 <;>
        simp only [hd, Bool.toNat_false, Bool.toNat_true, Nat.sub_zero,
          Nat.sub_self, Nat.one_mul, Nat.zero_mul] at * <;> omega
  | pass a b => norm_num at h1
  | receive d q hq b =>
      have hr := (valid_rail_range hq).1
      cases d <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.sub_zero,
        Nat.sub_self, Nat.one_mul, Nat.zero_mul] at h1 hr <;> omega
  | finish a b => norm_num at h1
  | initLeft => norm_num at h1
  | initHead => norm_num at h1
  | initRight => norm_num at h1
  | reset p hp => exact Or.inl ⟨p,hp,rfl⟩
  | seam a b => exact Or.inr ⟨a,b,rfl⟩

/-- West 1 may also be a seam with its square parameter equal to 1. -/
theorem west_1_iff_reset_or_seam {t : Tile} (ht : Allowed t) :
    t.west = 1 ↔ (∃ p ∈ [434,435,436], t = ⟨1,438,1,p⟩) ∨
      (∃ b : Fin 3, t = ⟨1,437,b.val,437⟩) := by
  constructor
  · intro hw
    rcases horizontal_one_cases ht (Or.inl hw) with hr | ⟨a,b,rfl⟩
    · exact Or.inl hr
    · exact Or.inr ⟨b, by simp only [show a.val^2 = 1 from hw]⟩
  · rintro (⟨p,hp,rfl⟩ | ⟨b,rfl⟩) <;> rfl

/-- East 1 may be a seam with any of the three west square parameters. -/
theorem east_1_iff_reset_or_seam {t : Tile} (ht : Allowed t) :
    t.east = 1 ↔ (∃ p ∈ [434,435,436], t = ⟨1,438,1,p⟩) ∨
      (∃ a : Fin 3, t = ⟨a.val^2,437,1,437⟩) := by
  constructor
  · intro he
    rcases horizontal_one_cases ht (Or.inr he) with hr | ⟨a,b,rfl⟩
    · exact Or.inl hr
    · exact Or.inr ⟨a, by simp only [show b.val = 1 from he]⟩
  · rintro (⟨p,hp,rfl⟩ | ⟨a,rfl⟩) <;> rfl

/-- The nonseam premise is explicit; without it a seam counterexample remains. -/
theorem west_1_nonseam {t : Tile} (ht : Allowed t) (hw : t.west = 1)
    (hn : t.north ≠ 437) : ∃ p ∈ [434,435,436], t = ⟨1,438,1,p⟩ := by
  rcases (west_1_iff_reset_or_seam ht).mp hw with hr | ⟨b,rfl⟩
  · exact hr
  · exact False.elim (hn rfl)

theorem east_1_nonseam {t : Tile} (ht : Allowed t) (he : t.east = 1)
    (hn : t.north ≠ 437) : ∃ p ∈ [434,435,436], t = ⟨1,438,1,p⟩ := by
  rcases (east_1_iff_reset_or_seam ht).mp he with hr | ⟨a,rfl⟩
  · exact hr
  · exact False.elim (hn rfl)

theorem horizontal_one_nonseam {t : Tile} (ht : Allowed t)
    (h1 : t.west = 1 ∨ t.east = 1) (hn : t.north ≠ 437) :
    ∃ p ∈ [434,435,436], t = ⟨1,438,1,p⟩ := by
  rcases h1 with hw | he
  · exact west_1_nonseam ht hw hn
  · exact east_1_nonseam ht he hn

/-- A direct local corollary for subsequent color matching. -/
theorem north_438_of_horizontal_one_nonseam {t : Tile} (ht : Allowed t)
    (h1 : t.west = 1 ∨ t.east = 1) (hn : t.north ≠ 437) : t.north = 438 := by
  obtain ⟨p,hp,rfl⟩ := horizontal_one_nonseam ht h1 hn
  rfl

end DiophantineConsistency.WangTiles942ResetHorizontal
