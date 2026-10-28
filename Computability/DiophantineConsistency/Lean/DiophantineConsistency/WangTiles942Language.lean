import DiophantineConsistency.WangTiles942Core

/-!
# The finite language of the actual 942 Wang tiles

This module classifies the literal table into its printed families. Rail
injectivity is restricted to actual direction-specific targets, including
halting target 215. It does not assert a tiling or machine-run equivalence.
-/

namespace DiophantineConsistency.WangTiles942Language

open WangTiles942

set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

/-- Every actual action lands in the target set for its own direction. -/
theorem action_target_mem (j : Fin 430) : (action j).2.2 ∈ targets (action j).2.1 := by
  rw [targets_eq_cache]
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨action j, ?_, rfl⟩
  apply List.mem_filter.mpr
  exact ⟨List.mem_ofFn.mpr ⟨j, rfl⟩, by simp⟩

theorem decoded_action_target_mem (j : Fin 430) :
    (DecimalMachine215.action j.val).2.2 ∈
      targets (DecimalMachine215.action j.val).2.1 := by
  simpa only [← action_eq_decoder j] using action_target_mem j

/-- The target sets have neither missing targets nor extra unattested targets. -/
theorem mem_targets_iff (d : Bool) (q : ℕ) : q ∈ targets d ↔
    ∃ j : Fin 430, (action j).2.1 = d ∧ (action j).2.2 = q := by
  constructor
  · intro h
    rw [targets_eq_cache] at h
    obtain ⟨a, ha, hq⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
    obtain ⟨hma, hda⟩ := List.mem_filter.mp ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hma
    exact ⟨j, by simpa using hda, hq⟩
  · rintro ⟨j, hdir, htarget⟩
    simpa only [hdir, htarget] using action_target_mem j

theorem mem_targets_iff_decoded (d : Bool) (q : ℕ) : q ∈ targets d ↔
    ∃ j : Fin 430, (DecimalMachine215.action j.val).2.1 = d ∧
      (DecimalMachine215.action j.val).2.2 = q := by
  simpa only [action_eq_decoder] using mem_targets_iff d q

/-- The rank of a member is strictly less than the number of targets. -/
theorem target_prefix_card_lt {d : Bool} {q : ℕ} (hq : q ∈ targets d) :
    (targets d ∩ Finset.range q).card < (targets d).card := by
  apply Finset.card_lt_card
  exact (Finset.ssubset_iff_of_subset Finset.inter_subset_left).2 ⟨q, hq, by simp⟩

/-- A target strictly below another number makes the corresponding ranks strict. -/
theorem rail_strict_mono {d : Bool} {p q : ℕ}
    (hp : p ∈ targets d) (hpq : p < q) : rail d p < rail d q := by
  have hc : (targets d ∩ Finset.range p).card < (targets d ∩ Finset.range q).card := by
    apply Finset.card_lt_card
    refine (Finset.ssubset_iff_of_subset
      (Finset.inter_subset_inter_left (Finset.range_mono (Nat.le_of_lt hpq)))).2 ?_
    exact ⟨p, by simp [hp, hpq], by simp⟩
  rw [rail_eq_formula, rail_eq_formula]
  unfold railFormula
  omega

/-- No injectivity is claimed away from the actual direction target set. -/
theorem rail_injective_on (d : Bool) : Set.InjOn (rail d) (↑(targets d) : Set ℕ) := by
  intro p hp q hq he
  rcases lt_trichotomy p q with hl | rfl | hl
  · have := rail_strict_mono hp hl
    omega
  · rfl
  · have := rail_strict_mono hq hl
    omega

theorem right_rail_range {q : ℕ} (hq : q ∈ targets true) :
    6 ≤ rail true q ∧ rail true q < 205 := by
  have hc := target_prefix_card_lt hq
  rw [target_counts.2] at hc
  rw [rail_eq_formula]
  simp only [railFormula, Bool.toNat_true, Nat.mul_one]
  omega

theorem left_rail_range {q : ℕ} (hq : q ∈ targets false) :
    205 ≤ rail false q ∧ rail false q < 250 := by
  have hc := target_prefix_card_lt hq
  rw [target_counts.1] at hc
  rw [rail_eq_formula]
  simp only [railFormula, Bool.toNat_false, Nat.mul_zero, Nat.sub_zero]
  omega

theorem directional_rails_disjoint {p q : ℕ}
    (hp : p ∈ targets false) (hq : q ∈ targets true) :
    rail false p ≠ rail true q := by
  obtain ⟨hl, _⟩ := left_rail_range hp
  obtain ⟨_, hr⟩ := right_rail_range hq
  omega

theorem valid_rail_range {d : Bool} {q : ℕ} (hq : q ∈ targets d) :
    6 ≤ rail d q ∧ rail d q < 250 := by
  cases d
  · obtain ⟨hl, hu⟩ := left_rail_range hq
    omega
  · obtain ⟨hl, hu⟩ := right_rail_range hq
    omega

/-- The ten printed families. The transition row is already proved equal to
its exact decimal-decoded action in `transitionRow_eq_decoded`. -/
inductive Allowed : Tile → Prop
  | start : Allowed start
  | transition (j : Fin 430) : Allowed (transitionRow j).2
  | pass (a b : Fin 2) : Allowed ⟨0, 432*a.val+b.val, 0, 432*a.val+b.val⟩
  | receive (d : Bool) (q : ℕ) (hq : q ∈ targets d) (b : Fin 2) :
      Allowed ⟨d.toNat*rail d q, b.val, (1-d.toNat)*rail d q, headColor q b.val⟩
  | finish (a b : Fin 2) : Allowed ⟨0, 432*a.val+b.val, 0, 438⟩
  | initLeft : Allowed ⟨2, 434, 2, 0⟩
  | initHead : Allowed ⟨3, 436, 4, 4⟩
  | initRight : Allowed ⟨4, 436, 4, 0⟩
  | reset (p : ℕ) (hp : p ∈ [434,435,436]) : Allowed ⟨1,438,1,p⟩
  | seam (a b : Fin 3) : Allowed ⟨a.val^2,437,b.val,437⟩

private theorem copy_allowed {a : ℕ} (ha : a < 2) {row : ℕ × Tile}
    (hr : row ∈ copyRows a) : Allowed row.2 := by
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hr
  exact Allowed.pass ⟨a,ha⟩ ⟨b,List.mem_range.mp hb⟩

private theorem signal_allowed {d : Bool} {row : ℕ × Tile}
    (hr : row ∈ signalRows d) : Allowed row.2 := by
  obtain ⟨q, hq, hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hr
  exact Allowed.receive d q (List.mem_toFinset.mpr hq) ⟨b,List.mem_range.mp hb⟩

private theorem tail_allowed {row : ℕ × Tile} (hr : row ∈ tailRows) : Allowed row.2 := by
  simp only [tailRows, List.mem_append] at hr
  rcases hr with ((h | h) | h) | h
  · obtain ⟨a, ha, h⟩ := List.mem_flatMap.mp h
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h
    exact Allowed.finish ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact Allowed.initLeft
    · exact Allowed.initHead
    · exact Allowed.initRight
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
    exact Allowed.reset p hp
  · obtain ⟨a, ha, h⟩ := List.mem_flatMap.mp h
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h
    exact Allowed.seam ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩

theorem row_allowed {row : ℕ × Tile} (hr : row ∈ indexedRows) : Allowed row.2 := by
  simp only [indexedRows, List.mem_append, List.mem_singleton, List.mem_ofFn] at hr
  rcases hr with (((rfl | ⟨j,rfl⟩) | (h | h)) | (h | h)) | h
  · exact Allowed.start
  · exact Allowed.transition j
  · exact copy_allowed (by decide) h
  · exact copy_allowed (by decide) h
  · exact signal_allowed h
  · exact signal_allowed h
  · exact tail_allowed h

private theorem copy_row_mem (a b : Fin 2) :
    (433-2*a.val+b.val, (⟨0,432*a.val+b.val,0,432*a.val+b.val⟩ : Tile)) ∈
      copyRows 0 ++ copyRows 1 := by
  have hm : (433-2*a.val+b.val, (⟨0,432*a.val+b.val,0,432*a.val+b.val⟩ : Tile)) ∈
      copyRows a.val := List.mem_map.mpr ⟨b.val,List.mem_range.mpr b.isLt,rfl⟩
  have ha := a.isLt
  have hv : a.val = 0 ∨ a.val = 1 := by omega
  rcases hv with hv | hv
  · apply List.mem_append_left
    simpa only [hv] using hm
  · apply List.mem_append_right
    simpa only [hv] using hm

private theorem signal_row_mem (d : Bool) (q : ℕ) (hq : q ∈ targets d) (b : Fin 2) :
    (423+2*rail d q+b.val,
      (⟨d.toNat*rail d q,b.val,(1-d.toNat)*rail d q,headColor q b.val⟩ : Tile)) ∈
      signalRows false ++ signalRows true := by
  have hm : (423+2*rail d q+b.val,
      (⟨d.toNat*rail d q,b.val,(1-d.toNat)*rail d q,headColor q b.val⟩ : Tile)) ∈
      signalRows d := List.mem_flatMap.mpr ⟨q,List.mem_toFinset.mp hq,
        List.mem_map.mpr ⟨b.val,List.mem_range.mpr b.isLt,rfl⟩⟩
  cases d
  · exact List.mem_append_left _ hm
  · exact List.mem_append_right _ hm

theorem allowed_row {t : Tile} (ht : Allowed t) : ∃ row ∈ indexedRows, row.2 = t := by
  cases ht with
  | start => exact ⟨(0,start), by simp only [indexedRows, List.mem_append,
      List.mem_singleton, true_or], rfl⟩
  | transition j =>
      refine ⟨transitionRow j, ?_, rfl⟩
      simp only [indexedRows, List.mem_append, List.mem_singleton, List.mem_ofFn]
      exact Or.inl (Or.inl (Or.inl (Or.inr ⟨j,rfl⟩)))
  | pass a b =>
      refine ⟨(433-2*a.val+b.val, _), ?_, rfl⟩
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      exact copy_row_mem a b
  | receive d q hq b =>
      refine ⟨(423+2*rail d q+b.val, _), ?_, rfl⟩
      apply List.mem_append_left
      apply List.mem_append_right
      exact signal_row_mem d q hq b
  | finish a b =>
      refine ⟨(923+2*a.val+b.val,_), List.mem_append_right _ ?_, rfl⟩
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      exact List.mem_flatMap.mpr ⟨a.val,List.mem_range.mpr a.isLt,
        List.mem_map.mpr ⟨b.val,List.mem_range.mpr b.isLt,rfl⟩⟩
  | initLeft => exact ⟨(927,_), List.mem_append_right _ (by simp [tailRows]), rfl⟩
  | initHead => exact ⟨(928,_), List.mem_append_right _ (by simp [tailRows]), rfl⟩
  | initRight => exact ⟨(929,_), List.mem_append_right _ (by simp [tailRows]), rfl⟩
  | reset p hp =>
      refine ⟨(496+p,_), List.mem_append_right _ ?_, rfl⟩
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨p,hp,rfl⟩
  | seam a b =>
      refine ⟨(933+3*a.val+b.val,_), List.mem_append_right _ ?_, rfl⟩
      apply List.mem_append_right
      exact List.mem_flatMap.mpr ⟨a.val,List.mem_range.mpr a.isLt,
        List.mem_map.mpr ⟨b.val,List.mem_range.mpr b.isLt,rfl⟩⟩

/-- Exact membership, in both directions, for the actual indexed table. -/
theorem allowed_iff_tile (t : Tile) : Allowed t ↔ ∃ i : Fin 942, tile i = t := by
  constructor
  · intro ht
    obtain ⟨row, hr, he⟩ := allowed_row ht
    have hm := ordered_rows_perm.mem_iff.mpr hr
    obtain ⟨i, hi, hir⟩ := List.mem_iff_getElem.mp hm
    exact ⟨⟨i, by simpa only [ordered_count] using hi⟩, by
      dsimp only [tile]
      rw [hir, he]⟩
  · rintro ⟨i,rfl⟩
    exact row_allowed (ordered_rows_perm.mem_iff.mp (List.getElem_mem _))

theorem tile_allowed (i : Fin 942) : Allowed (tile i) :=
  (allowed_iff_tile _).mpr ⟨i,rfl⟩

/-- Valid rails are at most 249; every other horizontal color is at most 4. -/
theorem allowed_horizontal_bound {t : Tile} (ht : Allowed t) :
    t.west < 250 ∧ t.east < 250 := by
  cases ht with
  | start => decide
  | transition j =>
      have hr := (valid_rail_range (action_target_mem j)).2
      dsimp only [transitionRow]
      cases hd : (action j).2.1 <;>
        simp only [hd, Bool.toNat_false, Bool.toNat_true, Nat.sub_zero, Nat.sub_self,
          Nat.one_mul, Nat.zero_mul] at * <;> omega
  | pass a b => simp
  | receive d q hq b =>
      have hr := (valid_rail_range hq).2
      cases d <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.sub_zero,
        Nat.sub_self, Nat.one_mul, Nat.zero_mul] <;> omega
  | finish a b => simp
  | initLeft => decide
  | initHead => decide
  | initRight => decide
  | reset p hp => simp
  | seam a b =>
      have ha := a.isLt
      have hb := b.isLt
      dsimp only
      constructor
      · interval_cases a.val <;> decide
      · omega

theorem tile_horizontal_bound (i : Fin 942) :
    (tile i).west < 250 ∧ (tile i).east < 250 :=
  allowed_horizontal_bound (tile_allowed i)

/-- Both complemented horizontal labels are strictly positive in every tile. -/
theorem complemented_horizontal_positive (i : Fin 942) :
    0 < 255 - (tile i).west ∧ 0 < 255 - (tile i).east := by
  obtain ⟨hw,he⟩ := tile_horizontal_bound i
  omega

end DiophantineConsistency.WangTiles942Language
