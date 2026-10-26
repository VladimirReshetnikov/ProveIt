import DiophantineConsistency.WangTiles942InputLanguage

/-!
# Local signal matching in the actual 942-tile language

Plain-input neighbors cannot match a nonzero signal to one another. A
transition's outgoing signal forces the appropriate receive tile with exactly
its actual target, including target 215. No whole-row or run assumption is used.
-/

namespace DiophantineConsistency.WangTiles942Signals

open WangTiles942 WangTiles942Language WangTiles942InputLanguage

set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Only a left-moving receive tile has nonzero east color at a plain input. -/
theorem plain_east_eq_zero_or_left_receive {t : Tile} (ht : Allowed t)
    (b : Fin 2) (hn : t.north = b.val) :
    t.east = 0 ∨ ∃ q : ℕ, q ∈ targets false ∧
      t = ⟨0,b.val,rail false q,headColor q b.val⟩ := by
  rcases (north_plain_iff ht b).mp hn with rfl | rfl | ⟨d,q,hq,rfl⟩
  · exact Or.inl rfl
  · exact Or.inl rfl
  · cases d
    · exact Or.inr ⟨q,hq,by simp⟩
    · exact Or.inl (by simp)

/-- Only a right-moving receive tile has nonzero west color at a plain input. -/
theorem plain_west_eq_zero_or_right_receive {t : Tile} (ht : Allowed t)
    (b : Fin 2) (hn : t.north = b.val) :
    t.west = 0 ∨ ∃ q : ℕ, q ∈ targets true ∧
      t = ⟨rail true q,b.val,0,headColor q b.val⟩ := by
  rcases (north_plain_iff ht b).mp hn with rfl | rfl | ⟨d,q,hq,rfl⟩
  · exact Or.inl rfl
  · exact Or.inl rfl
  · cases d
    · exact Or.inl (by simp)
    · exact Or.inr ⟨q,hq,by simp⟩

/-- Small east colors, including every seam west color, force zero. -/
theorem plain_east_small_eq_zero {t : Tile} (ht : Allowed t)
    (b : Fin 2) (hn : t.north = b.val) (he : t.east < 6) : t.east = 0 := by
  rcases plain_east_eq_zero_or_left_receive ht b hn with hz | ⟨q,hq,rfl⟩
  · exact hz
  · have hpos := (left_rail_range hq).1
    simp only at he ⊢
    omega

/-- Small west colors, including every seam east color, force zero. -/
theorem plain_west_small_eq_zero {t : Tile} (ht : Allowed t)
    (b : Fin 2) (hn : t.north = b.val) (hw : t.west < 6) : t.west = 0 := by
  rcases plain_west_eq_zero_or_right_receive ht b hn with hz | ⟨q,hq,rfl⟩
  · exact hz
  · have hpos := (right_rail_range hq).1
    simp only at hw ⊢
    omega

/-- Directional rail ranges exclude receive/receive ghost signals. -/
theorem plain_pair_edge_zero {t u : Tile} (ht : Allowed t) (hu : Allowed u)
    (b c : Fin 2) (htn : t.north = b.val) (hun : u.north = c.val)
    (hmatch : t.east = u.west) : t.east = 0 := by
  rcases plain_east_eq_zero_or_left_receive ht b htn with he | ⟨p,hp,rfl⟩
  · exact he
  · rcases plain_west_eq_zero_or_right_receive hu c hun with hw | ⟨q,hq,rfl⟩
    · have hpos := (left_rail_range hp).1
      simp only at hmatch ⊢
      omega
    · exact False.elim (directional_rails_disjoint hp hq hmatch)

/-- A right transition forces the exact target-bearing receive tile on its right. -/
theorem right_transition_receiver (j : Fin 430) (hd : (action j).2.1 = true)
    {u : Tile} (hu : Allowed u) (c : Fin 2) (hn : u.north = c.val)
    (hmatch : (transitionRow j).2.east = u.west) :
    u = ⟨rail true (action j).2.2,c.val,0,headColor (action j).2.2 c.val⟩ := by
  have ht : (action j).2.2 ∈ targets true := by
    simpa only [hd] using action_target_mem j
  have he : (transitionRow j).2.east = rail true (action j).2.2 := by
    simp only [transitionRow, hd, Bool.toNat_true, Nat.one_mul]
  rw [he] at hmatch
  rcases plain_west_eq_zero_or_right_receive hu c hn with hw | ⟨q,hq,rfl⟩
  · have hpos := (right_rail_range ht).1
    omega
  · have heq : (action j).2.2 = q := rail_injective_on true ht hq hmatch
    rw [heq]

/-- A left transition forces the exact target-bearing receive tile on its left. -/
theorem left_transition_receiver (j : Fin 430) (hd : (action j).2.1 = false)
    {t : Tile} (ht : Allowed t) (b : Fin 2) (hn : t.north = b.val)
    (hmatch : t.east = (transitionRow j).2.west) :
    t = ⟨0,b.val,rail false (action j).2.2,headColor (action j).2.2 b.val⟩ := by
  have htarget : (action j).2.2 ∈ targets false := by
    simpa only [hd] using action_target_mem j
  have hw : (transitionRow j).2.west = rail false (action j).2.2 := by
    simp only [transitionRow, hd, Bool.toNat_false, Nat.sub_zero, Nat.one_mul]
  rw [hw] at hmatch
  rcases plain_east_eq_zero_or_left_receive ht b hn with he | ⟨q,hq,rfl⟩
  · have hpos := (left_rail_range htarget).1
    omega
  · have heq : q = (action j).2.2 := rail_injective_on false hq htarget hmatch
    rw [heq]

/-- Zero horizontal edges retain both pass and finish until finish is excluded. -/
theorem plain_zero_edges_iff_pass_or_finish {t : Tile} (ht : Allowed t)
    (b : Fin 2) (hn : t.north = b.val) :
    (t.west = 0 ∧ t.east = 0) ↔
      t = ⟨0,b.val,0,b.val⟩ ∨ t = ⟨0,b.val,0,438⟩ := by
  constructor
  · rintro ⟨hw,he⟩
    rcases (north_plain_iff ht b).mp hn with hp | hf | ⟨d,q,hq,rfl⟩
    · exact Or.inl hp
    · exact Or.inr hf
    · have hpos := (valid_rail_range hq).1
      cases d <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.sub_zero,
        Nat.sub_self, Nat.one_mul, Nat.zero_mul] at hw he hpos <;> omega
  · rintro (rfl | rfl) <;> exact ⟨rfl,rfl⟩

/-- A plain tile with zero edges passes its input if its south is not finish 438. -/
theorem plain_zero_edges_nonfinish {t : Tile} (ht : Allowed t)
    (b : Fin 2) (hn : t.north = b.val) (hw : t.west = 0) (he : t.east = 0)
    (hs : t.south ≠ 438) : t = ⟨0,b.val,0,b.val⟩ := by
  rcases (plain_zero_edges_iff_pass_or_finish ht b hn).mp ⟨hw,he⟩ with hp | hf
  · exact hp
  · exact False.elim (hs (congrArg Tile.south hf))

end DiophantineConsistency.WangTiles942Signals
