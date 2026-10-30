import DiophantineConsistency.ArithmeticCellTable
import DiophantineConsistency.MFWangTiles942Permutation
import DiophantineConsistency.ArithmeticMaskKernel
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! **Matrix-free standard facts about the 942-tile table and the fixed kernel**
(soundness spec §2), importable next to Foundation.

The table facts (colour bounds, the left inverse of the table, the strict-rank
description of `physicalPosition` and its bijectivity) are those of the Matrix-free
clones `MFWangTiles942Core`/`MFWangTiles942Permutation`, re-exported here under the
names the internal cell decoding uses. This module adds what those clones lack:
the row facts of `ArithmeticCellTable` (west bound `< 250`, the unique south-45
row), the kernel geometry of reflected sources (as in `CurrentReflectedGeometry2011`;
importing its Matrix-free clone would add ~350 modules to every cell module), and
the exact physical selector tail (`tail_source_bound`, after
`CurrentSelectorTail2011`). -/

namespace DiophantineConsistency.ArithmeticCellPhysical

open WangTiles942 CurrentKernel2011
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option exponentiation.threshold 1024

export MF.WangTiles942 (TightColorsBounded weight_small strictRank strictRank_eq_sum nonStartWeight
  nonStart_rows physicalPosition_zero physicalPosition_succ physicalPosition_lt
  physicalPosition_injective physicalEquiv physical_lt_iff_weight)

theorem tile_mem (i : Fin 942) :
    (orderedRows[i.val]'(by rw [ordered_count]; exact i.isLt)) ∈ orderedRows :=
  List.getElem_mem _

theorem tile_tight (i : Fin 942) : TightColorsBounded (tile i) :=
  MF.WangTiles942.all_rows_tight _ (tile_mem i)

theorem tile_west_lt (i : Fin 942) : (tile i).west < 250 := (rows_facts _ (tile_mem i)).1

theorem rows_south45 : ∀ row ∈ orderedRows, row.2.south = 45 → row.2 = cutoffTile :=
  fun r h => (rows_facts r h).2

theorem start_tile : tile 0 = ⟨2, 435, 3, 1⟩ := MF.WangTiles942.start_zero

/-- Sums over tiles at their physical positions are sums over positions. -/
theorem phys_sum (g : ℕ → ℕ) :
    (∑ i : Fin 942, g (physicalPosition i)) = ∑ p ∈ Finset.range 942, g p := by
  have he := Equiv.sum_comp physicalEquiv (fun p : Fin 942 => g p.val)
  change (∑ i : Fin 942, g (physicalPosition i)) = ∑ p : Fin 942, g p.val at he
  rw [he]
  exact Fin.sum_univ_eq_sum_range g 942

/-! ### Kernel geometry (after `CurrentReflectedGeometry2011`) -/

theorem position_le (e : Entry) : position e ≤ 985 := by
  rcases e with i | j | j | j | j
  · have := physicalPosition_lt i
    simp only [position]; omega
  all_goals simp only [position]; omega

theorem position_injective : Function.Injective position := by
  intro e f he
  rcases e with i | i | i | i | i <;>
    rcases f with j | j | j | j | j
  all_goals simp only [position] at he
  · exact congrArg Sum.inl (physicalPosition_injective he)
  all_goals try have hi := physicalPosition_lt i
  all_goals try have hj := physicalPosition_lt j
  all_goals try omega
  all_goals simp only [Sum.inl.injEq, Sum.inr.injEq]
  all_goals apply Fin.ext; omega

theorem doubled_weight_lt (e : Entry) : 2 * weight e < 2 ^ 45 := by
  rcases e with i | j | j | j | j
  · have hh := weight_small i
    change 2 * selectorWeight (tile i) < 2 ^ 45
    omega
  all_goals
    change 2 * 2 ^ _ < 2 ^ 45
    fin_cases j <;> decide

abbrev Control := Fin 8 ⊕ (Fin 9 ⊕ (Fin 8 ⊕ Fin 9))

theorem doubled_control_mass :
    (∑ e : Fin 8 ⊕ (Fin 9 ⊕ (Fin 8 ⊕ Fin 9)), 2 * weight (.inr e)) = 2 ^ 45 - 2048 := by
  decide +kernel

theorem selector_position_lt (i : Fin 942) : position (.inl i) < 942 :=
  physicalPosition_lt i

noncomputable def source (h : ℕ) (e : Entry) : ℕ := h + position e - 1005

theorem source_le {h : ℕ} (hh : h ≤ 1004) (e : Entry) : source h e ≤ 984 := by
  have hp := position_le e
  unfold source
  omega

theorem source_nonselector_coefficient {h : ℕ} (hh : h ≤ 1004) (e : Entry)
    (hs : 942 ≤ source h e) : 943 ≤ position e := by
  unfold source at hs
  omega

noncomputable def selectorEntries (h : ℕ) : Finset Entry :=
  Finset.univ.filter (fun e => 1005 ≤ h + position e ∧ source h e < 942)


theorem reflected_split (h : ℕ) (f : Entry → ℕ) :
    (∑ e : Entry, if 1005 ≤ h + position e then f e else 0) =
      (∑ e ∈ selectorEntries h, f e) +
      (∑ e : Entry, if 1005 ≤ h + position e ∧ 942 ≤ source h e then f e else 0) := by
  rw [selectorEntries, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have hge : 942 ≤ source h e ↔ ¬source h e < 942 := by omega
  by_cases hv : 1005 ≤ h + position e <;>
    by_cases hf : source h e < 942 <;>
      simp only [hv, hf, hge, not_true_eq_false, not_false_eq_true,
        and_true, and_false, if_true, if_false, zero_add, add_zero]

private def controlCoefficient : Entry → ℕ
  | .inl _ => 0
  | .inr e => 2 * weight (.inr e)

theorem reflected_control_le {h : ℕ} (hh : h ≤ 1004) (f : Entry → ℕ)
    (hf : ∀ e, f e ≤ 1) :
    (∑ e : Entry, if 1005 ≤ h + position e ∧ 942 ≤ source h e then
      2 * weight e * f e else 0) ≤ 2 ^ 45 - 2048 := by
  have hm (e : Entry) :
      (if 1005 ≤ h + position e ∧ 942 ≤ source h e then
        2 * weight e * f e else 0) ≤ controlCoefficient e := by
    rcases e with i | e
    · have hp := selector_position_lt i
      have hz : ¬(1005 ≤ h + position (.inl i) ∧ 942 ≤ source h (.inl i)) := by
        intro hs
        have he := source_nonselector_coefficient hh (.inl i) hs.2
        omega
      simp only [if_neg hz, controlCoefficient, le_refl]
    · simp only [controlCoefficient]
      split_ifs
      · exact (Nat.mul_le_mul_left (2 * weight (.inr e)) (hf _)).trans_eq (Nat.mul_one _)
      · exact Nat.zero_le _
  have hs := Finset.sum_le_sum (fun e (_ : e ∈ (Finset.univ : Finset Entry)) => hm e)
  have hmass : (∑ e : Entry, controlCoefficient e) = 2 ^ 45 - 2048 := by
    rw [Fintype.sum_sum_type]
    simp only [controlCoefficient, Finset.sum_const_zero, zero_add]
    exact doubled_control_mass
  rw [hmass] at hs
  exact hs

theorem selector_source_injective (h : ℕ) :
    Set.InjOn (source h) (selectorEntries h : Set Entry) := by
  intro e he f hf hef
  have he' := (Finset.mem_filter.mp he).2.1
  have hf' := (Finset.mem_filter.mp hf).2.1
  apply position_injective
  unfold source at hef
  omega


theorem selector_sum_le (h : ℕ) (f : ℕ → ℕ) :
    (∑ e ∈ selectorEntries h, f (source h e)) ≤ ∑ j ∈ Finset.range 942, f j := by
  have hsub : (selectorEntries h).image (source h) ⊆ Finset.range 942 := by
    intro j hj
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (Finset.mem_filter.mp he).2.2
  calc
    _ = ∑ j ∈ (selectorEntries h).image (source h), f j := by
      symm
      exact Finset.sum_image (selector_source_injective h)
    _ ≤ _ := Finset.sum_le_sum_of_subset hsub

theorem selector_weighted_lt (h : ℕ) (f : ℕ → ℕ)
    (hone : (∑ e ∈ selectorEntries h, f (source h e)) ≤ 1) :
    (∑ e ∈ selectorEntries h, 2 * weight e * f (source h e)) < 2 ^ 45 := by
  have hm : (∑ e ∈ selectorEntries h, 2 * weight e * f (source h e)) ≤
      (2 ^ 45 - 1) * (∑ e ∈ selectorEntries h, f (source h e)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e _
    apply Nat.mul_le_mul_right
    have hh := doubled_weight_lt e
    omega
  have hh := Nat.mul_le_mul_left (2 ^ 45 - 1) hone
  omega

/-! ### The physical selector tail (after `CurrentSelectorTail2011`) -/

noncomputable def cutoff : ℕ := 1575850607617

theorem cutoff_tile : tile 866 = cutoffTile := by decide +kernel

theorem cutoff_weight : selectorWeight cutoffTile = cutoff := by decide +kernel

theorem weight_le_cutoff_iff (i : Fin 942) :
    selectorWeight (tile i) ≤ cutoff ↔ (tile i).south ≤ 45 := by
  obtain ⟨hw, he, hn, hs⟩ := tile_tight i
  by_cases h45 : (tile i).south = 45
  · have ht' : tile i = cutoffTile := rows_south45 _ (tile_mem i) h45
    rw [ht', cutoff_weight]
    decide
  · dsimp only [selectorWeight, cutoff]
    omega

noncomputable def lowMass (t : Tile) : ℕ := if t.south ≤ 45 then selectorWeight t else 0

private theorem sum_map_congr {α : Type*} (l : List α) (f g : α → ℕ)
    (h : ∀ a ∈ l, f a = g a) : (l.map f).sum = (l.map g).sum :=
  congrArg List.sum (List.map_congr_left h)

private theorem transition_low (j : Fin 430) : (transitionRow j).2.south ≤ 45 := by
  have h := Bool.toNat_le (action j).1
  change (action j).1.toNat ≤ 45
  omega

private theorem transition_low_mass :
    ((List.ofFn transitionRow).map (fun row => lowMass row.2)).sum = 11139798681006 :=
  (sum_map_congr (List.ofFn transitionRow) (fun row => lowMass row.2)
    (fun row => selectorWeight row.2)
    (by
      intro row hr
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
      exact if_pos (transition_low j))).trans ArithmeticMaskKernel.transition_mass

private theorem copy_low_mass :
    ((copyRows 1 ++ copyRows 0).map (fun row => lowMass row.2)).sum = 34360002562 := by
  decide +kernel
private theorem right_low_mass :
    ((signalRows true).map (fun row => lowMass row.2)).sum = 6562712006670 := by decide +kernel
private theorem left_low_mass :
    ((signalRows false).map (fun row => lowMass row.2)).sum = 33441962035234 := by decide +kernel
private theorem tail_low_mass :
    (tailRows.map (fun row => lowMass row.2)).sum = 139123503107 := by decide +kernel

private theorem sum_families {α : Type*} (a : α) (f : α → ℕ)
    (l₁ l₂ l₃ l₄ l₅ : List α) (v₁ v₂ v₃ v₄ v₅ : ℕ)
    (h₁ : (l₁.map f).sum = v₁) (h₂ : (l₂.map f).sum = v₂)
    (h₃ : (l₃.map f).sum = v₃) (h₄ : (l₄.map f).sum = v₄)
    (h₅ : (l₅.map f).sum = v₅) :
    ((([a] ++ l₁ ++ l₂ ++ (l₃ ++ l₄) ++ l₅).drop 1).map f).sum =
      v₁ + v₂ + v₃ + v₄ + v₅ := by
  simp only [List.append_assoc, List.cons_append, List.nil_append,
    List.drop_succ_cons, List.drop_zero, List.map_append, List.sum_append]
  rw [h₁, h₂, h₃, h₄, h₅]
  omega

theorem selected_mass :
    ((orderedRows.drop 1).map (fun row => lowMass row.2)).sum = 51317956228579 :=
  sum_families (0,start) (fun row => lowMass row.2)
    (List.ofFn transitionRow) (copyRows 1 ++ copyRows 0)
    (signalRows true) (signalRows false) tailRows
    11139798681006 34360002562 6562712006670 33441962035234 139123503107
    transition_low_mass copy_low_mass right_low_mass left_low_mass tail_low_mass

theorem sum_nonStart (f : Tile → ℕ) :
    (∑ j : Fin 941, f (tile j.succ)) =
      ((orderedRows.drop 1).map (fun row => f row.2)).sum := by
  have h := congrArg (fun ts : List Tile => (ts.map f).sum) nonStart_rows
  simpa only [List.map_map, List.map_ofFn, List.sum_ofFn, Function.comp_def, Fin.succ] using h.symm

theorem lowMass_sum : (∑ j : Fin 941, lowMass (tile j.succ)) = 51317956228579 :=
  (sum_nonStart lowMass).trans selected_mass

noncomputable def lowCount (t : Tile) : ℕ := if t.south ≤ 45 then 1 else 0

private theorem sum_map_const {α : Type*} (l : List α) (f : α → ℕ) (v : ℕ)
    (h : ∀ a ∈ l, f a = v) : (l.map f).sum = v * l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]
      simp only [Nat.mul_succ, Nat.add_comm]

private theorem transition_low_count :
    ((List.ofFn transitionRow).map (fun row => lowCount row.2)).sum = 430 := by
  have h := sum_map_const (List.ofFn transitionRow) (fun row => lowCount row.2) 1
    (by
      intro row hr
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
      exact if_pos (transition_low j))
  simpa only [List.length_ofFn, Nat.one_mul] using h

private theorem copy_low_count :
    ((copyRows 1 ++ copyRows 0).map (fun row => lowCount row.2)).sum = 2 := by decide +kernel
private theorem right_low_count :
    ((signalRows true).map (fun row => lowCount row.2)).sum = 14 := by decide +kernel
private theorem left_low_count :
    ((signalRows false).map (fun row => lowCount row.2)).sum = 34 := by decide +kernel
private theorem tail_low_count :
    (tailRows.map (fun row => lowCount row.2)).sum = 3 := by decide +kernel

theorem selected_count :
    ((orderedRows.drop 1).map (fun row => lowCount row.2)).sum = 483 :=
  sum_families (0,start) (fun row => lowCount row.2)
    (List.ofFn transitionRow) (copyRows 1 ++ copyRows 0)
    (signalRows true) (signalRows false) tailRows 430 2 14 34 3
    transition_low_count copy_low_count right_low_count left_low_count tail_low_count

theorem lowCount_sum : (∑ j : Fin 941, lowCount (tile j.succ)) = 483 :=
  (sum_nonStart lowCount).trans selected_count

theorem upper_plus_low (j : Fin 941) :
    (if cutoff < nonStartWeight j then 1 else 0) + lowCount (tile j.succ) = 1 := by
  have he := weight_le_cutoff_iff j.succ
  dsimp only [nonStartWeight, lowCount]
  by_cases hs : (tile j.succ).south ≤ 45
  · have hw := he.mpr hs
    simp only [if_pos hs, if_neg (not_lt_of_ge hw), zero_add]
  · have hw : cutoff < selectorWeight (tile j.succ) := by
      have hn : ¬selectorWeight (tile j.succ) ≤ cutoff := fun h => hs (he.mp h)
      omega
    simp only [if_neg hs, if_pos hw, add_zero]

attribute [local irreducible] WangTiles942.tile WangTiles942.orderedRows nonStartWeight

theorem split_count (c : ℕ) (w l : Fin 941 → ℕ)
    (hpl : ∀ j, (if c < w j then 1 else 0) + l j = 1) (hl : ∑ j, l j = 483) :
    (∑ j : Fin 941, if c < w j then 1 else 0) = 458 := by
  have hs : (∑ j : Fin 941, ((if c < w j then 1 else 0) + l j)) = ∑ _j : Fin 941, (1:ℕ) :=
    Finset.sum_congr rfl (fun j _ => hpl j)
  rw [Finset.sum_add_distrib, hl, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one] at hs
  omega

theorem upper_cutoff_sum :
    (∑ j : Fin 941, if cutoff < nonStartWeight j then 1 else 0) = 458 :=
  split_count cutoff nonStartWeight (fun j => lowCount (tile j.succ)) upper_plus_low lowCount_sum

theorem cutoff_rank : strictRank nonStartWeight (865 : Fin 941) = 458 := by
  rw [strictRank_eq_sum]
  have hw : nonStartWeight 865 = cutoff := by
    unfold nonStartWeight
    rw [show (865 : Fin 941).succ = (866 : Fin 942) from Fin.ext rfl, cutoff_tile, cutoff_weight]
  rw [hw]
  exact upper_cutoff_sum

theorem cutoff_position : physicalPosition 866 = 459 := by
  have h := physicalPosition_succ (865 : Fin 941)
  have e : (865 : Fin 941).succ = (866 : Fin 942) := Fin.ext rfl
  rw [cutoff_rank, e] at h
  rw [h]

theorem tail_position (i : Fin 942) (hp : 459 ≤ physicalPosition i) :
    i ≠ 0 ∧ (tile i).south ≤ 45 := by
  have hi : i ≠ 0 := by
    rintro rfl
    rw [physicalPosition_zero] at hp
    omega
  refine ⟨hi, (weight_le_cutoff_iff i).mp ?_⟩
  have hr := physical_lt_iff_weight i 866 hi (by decide)
  rw [cutoff_position, cutoff_tile, cutoff_weight] at hr
  exact le_of_not_gt (fun hw => (not_lt_of_ge hp) (hr.mpr hw))

noncomputable def tailTerm (e : Entry) : ℕ :=
  if 459 ≤ position e then 2 * weight e else 0

theorem control_tail_mass :
    (∑ e : Fin 8 ⊕ (Fin 9 ⊕ (Fin 8 ⊕ Fin 9)), tailTerm (.inr e)) = 35184372086784 := by
  decide +kernel

theorem sum_le_succ (f : Fin 942 → ℕ) (g : Fin 941 → ℕ) (h0 : f 0 = 0)
    (hs : ∀ j, f j.succ ≤ g j) : (∑ i, f i) ≤ ∑ j, g j := by
  rw [Fin.sum_univ_succ, h0, zero_add]
  exact Finset.sum_le_sum (fun j _ => hs j)

theorem tailTerm_zero : tailTerm (.inl 0) = 0 := by
  unfold tailTerm
  exact if_neg (by
    show ¬ 459 ≤ physicalPosition 0
    rw [physicalPosition_zero]
    exact of_decide_eq_false rfl)

theorem weight_inl (i : Fin 942) : weight (.inl i) = selectorWeight (tile i) := rfl

theorem tailTerm_succ (j : Fin 941) : tailTerm (.inl j.succ) ≤ 2 * lowMass (tile j.succ) := by
  unfold tailTerm lowMass
  by_cases hp : 459 ≤ position (Sum.inl j.succ)
  · rw [if_pos hp, if_pos (tail_position j.succ hp).2, weight_inl]
  · rw [if_neg hp]
    exact Nat.zero_le _

theorem tail_bound_generic (f : Fin 942 → ℕ) (g : Fin 941 → ℕ) (M : ℕ) (h0 : f 0 = 0)
    (hs : ∀ j, f j.succ ≤ 2 * g j) (hg : ∑ j, g j = M) : (∑ i, f i) ≤ 2 * M := by
  rw [Fin.sum_univ_succ, h0, zero_add, ← hg, Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => hs j)

theorem selector_tail_le :
    (∑ i : Fin 942, tailTerm (.inl i)) ≤ 102635912457158 :=
  tail_bound_generic (fun i => tailTerm (.inl i)) (fun j => lowMass (tile j.succ))
    51317956228579 tailTerm_zero tailTerm_succ lowMass_sum

theorem entry_bound (f : Entry → ℕ) (h1 : (∑ i : Fin 942, f (.inl i)) ≤ 102635912457158)
    (h2 : (∑ e : Fin 8 ⊕ (Fin 9 ⊕ (Fin 8 ⊕ Fin 9)), f (.inr e)) = 35184372086784) :
    (∑ e : Entry, f e) ≤ 137820284543942 := by
  rw [Fintype.sum_sum_type]
  omega

theorem tailMass_le : (∑ e : Entry, tailTerm e) ≤ 137820284543942 :=
  entry_bound tailTerm selector_tail_le control_tail_mass

/-- An arbitrary Boolean selection confined to the physical suffix is bounded
by the exact tail (`CurrentSelectorTail2011.tail_source_bound`). -/
theorem tail_source_bound (a : Entry → ℕ) (ha : ∀ e, a e ≤ 1)
    (hz : ∀ e, position e < 459 → a e = 0) :
    (∑ e, 2 * weight e * a e) ≤ 137820284543942 := by
  refine le_trans (Finset.sum_le_sum (fun e _ => ?_)) tailMass_le
  by_cases hp : 459 ≤ position e
  · rw [tailTerm, if_pos hp]
    exact le_trans (Nat.mul_le_mul_left _ (ha e)) (by simp)
  · rw [hz e (Nat.lt_of_not_le hp), mul_zero]
    exact Nat.zero_le _

theorem early_reset_numeric : 137820284543942 + 2^10 + 60 < 2 ^ 47 := by norm_num

end DiophantineConsistency.ArithmeticCellPhysical
