import DiophantineConsistency.ArithmeticCellTable
import DiophantineConsistency.ArithmeticMaskKernel
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! **Matrix-free standard facts about the 942-tile table and the fixed kernel**
(soundness spec §2), importable next to Foundation.

The accepted ℕ proofs of these facts live in `WangTiles942Core`,
`WangTiles942Permutation`, `CurrentKernel2011`, `CurrentReflectedGeometry2011` and
`CurrentSelectorTail2011`, whose `Mathlib.Tactic` imports pull in Mathlib's `Matrix`
and therefore clash with `Foundation.Vorspiel.Matrix`. This module reproves exactly
what the internal cell decoding needs from the Matrix-free data
`WangTiles942TableData`/`CurrentKernelData2011`: colour bounds and the left inverse
of the table (by `decide +kernel` over the 942 rows), the strict-rank description
of `physicalPosition` and its bijectivity (copied from `WangTiles942Permutation`),
the kernel geometry of reflected sources, and the exact physical selector tail
(`tail_source_bound`, after `CurrentSelectorTail2011`). -/

namespace DiophantineConsistency.ArithmeticCellPhysical

open WangTiles942 CurrentKernel2011
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option exponentiation.threshold 1024

theorem tile_mem (i : Fin 942) :
    (orderedRows[i.val]'(by rw [ordered_count]; exact i.isLt)) ∈ orderedRows :=
  List.getElem_mem _

theorem tile_tight (i : Fin 942) : Tight (tile i) := rows_tight _ (tile_mem i)

theorem tile_west_lt (i : Fin 942) : (tile i).west < 250 := rows_west_lt _ (tile_mem i)

theorem weight_small (i : Fin 942) : selectorWeight (tile i) < 2 ^ 44 := by
  obtain ⟨hw, he, hn, hs⟩ := tile_tight i
  dsimp only [selectorWeight]
  omega

theorem start_tile : tile 0 = ⟨2, 435, 3, 1⟩ := by decide +kernel

theorem recovered_tile (i : Fin 942) : recoveredIndex (tile i) = i.val := by
  have h := rows_recovered _ (tile_mem i)
  have hi : (orderedRows[i.val]'(by rw [ordered_count]; exact i.isLt)).1 = i.val := by
    have ho : i.val < orderedRows.length := by rw [ordered_count]; exact i.isLt
    have hr : i.val < (List.range 942).length := by simpa only [List.length_range] using i.isLt
    have he := congrArg (fun xs : List ℕ => xs[i.val]?) row_indices_exact
    rw [List.getElem?_map, List.getElem?_eq_getElem ho, List.getElem?_eq_getElem hr] at he
    simpa only [List.getElem_range, Option.map_some, Option.some.injEq] using he
  exact h.trans hi

theorem tile_injective : Function.Injective tile := by
  intro i j h
  apply Fin.ext
  exact (recovered_tile i).symm.trans ((congrArg recoveredIndex h).trans (recovered_tile j))

theorem tile_weight_injective :
    Function.Injective (fun i : Fin 942 => selectorWeight (tile i)) := by
  intro i j h
  apply tile_injective
  have hi := tile_tight i
  have hj := tile_tight j
  simp only at h
  generalize tile i = t at hi h ⊢
  generalize tile j = u at hj h ⊢
  obtain ⟨tw, te, tn, ts⟩ := hi
  obtain ⟨uw, ue, un, us⟩ := hj
  dsimp only [selectorWeight] at h
  cases t
  cases u
  simp only [Tile.mk.injEq]
  dsimp only at *
  omega

/-! ### Strict ranks (copied from `WangTiles942Permutation`) -/

section GenericRank

variable {α : Type*} [Fintype α]

noncomputable def strictUpper (w : α → ℕ) (i : α) : Finset α :=
  Finset.univ.filter (fun j => w i < w j)

noncomputable def strictRank (w : α → ℕ) (i : α) : ℕ := (strictUpper w i).card

theorem strictRank_lt_card (w : α → ℕ) (i : α) : strictRank w i < Fintype.card α := by
  exact Finset.card_lt_card (Finset.filter_ssubset.mpr
    ⟨i, Finset.mem_univ i, Nat.lt_irrefl (w i)⟩)

theorem strictRank_antitone {w : α → ℕ} {i j : α} (h : w i < w j) :
    strictRank w j < strictRank w i := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro k hk
    simp only [strictUpper, Finset.mem_filter, Finset.mem_univ, true_and] at *
    exact h.trans hk
  · intro he
    have hj : j ∈ strictUpper w i := by
      simp only [strictUpper, Finset.mem_filter, Finset.mem_univ, true_and]
      exact h
    have hj' : j ∈ strictUpper w j := he.symm ▸ hj
    simp only [strictUpper, Finset.mem_filter, Finset.mem_univ, true_and,
      lt_self_iff_false] at hj'

theorem strictRank_injective {w : α → ℕ} (hw : Function.Injective w) :
    Function.Injective (strictRank w) := by
  intro i j he
  apply hw
  rcases lt_trichotomy (w i) (w j) with h | h | h
  · have := strictRank_antitone h
    omega
  · exact h
  · have := strictRank_antitone h
    omega

theorem strictRank_lt_iff (w : α → ℕ) (i j : α) :
    strictRank w i < strictRank w j ↔ w j < w i := by
  constructor
  · intro hr
    rcases lt_trichotomy (w i) (w j) with h | h | h
    · have := strictRank_antitone h
      omega
    · have he : strictRank w i = strictRank w j := by
        simp only [strictRank, strictUpper, h]
      omega
    · exact h
  · exact strictRank_antitone

theorem strictRank_eq_sum (w : α → ℕ) (i : α) :
    strictRank w i = ∑ j : α, if w i < w j then 1 else 0 := by
  simp only [strictRank, strictUpper, Finset.card_eq_sum_ones, Finset.sum_filter]

end GenericRank

/-! ### The physical positions -/

theorem floor_weight_indicator (a b : ℕ) (ha : a < 2^44) (hb : b < 2^44) :
    (2^44 - 1 + b - a) / 2^44 = if a < b then 1 else 0 := by
  split_ifs <;> omega

noncomputable def nonStartWeight (j : Fin 941) : ℕ := selectorWeight (tile j.succ)

theorem nonStartWeight_injective : Function.Injective nonStartWeight := by
  intro i j h
  have he : i.succ = j.succ := tile_weight_injective h
  apply Fin.ext
  have hv : i.val+1 = j.val+1 := congrArg Fin.val he
  omega

theorem nonStart_rows : (orderedRows.drop 1).map Prod.snd =
    List.ofFn (fun j : Fin 941 => tile ⟨j.val + 1, by omega⟩) := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_drop, List.length_ofFn, ordered_count]
  · intro j h₁ h₂
    simp only [List.getElem_map, List.getElem_drop, List.getElem_ofFn, tile,
      Nat.add_comm]

theorem physicalPosition_eq_printed (i : Fin 942) : physicalPosition i =
    if i.val = 0 then 0 else 1 + ∑ j : Fin 941,
      (2 ^ 44 - 1 + selectorWeight (tile ⟨j.val + 1, by omega⟩) -
        selectorWeight (tile i)) / 2 ^ 44 := by
  unfold physicalPosition
  have hs := congrArg (fun ts : List Tile =>
    (ts.map (fun t => (2 ^ 44 - 1 + selectorWeight t - selectorWeight (tile i)) /
      2 ^ 44)).sum) nonStart_rows
  simpa only [List.map_map, List.map_ofFn, List.sum_ofFn, Function.comp_def] using
    congrArg (fun x : ℕ => if i.val = 0 then 0 else 1 + x) hs

theorem physicalPosition_zero : physicalPosition 0 = 0 := rfl

theorem physicalPosition_succ (i : Fin 941) :
    physicalPosition i.succ = 1 + strictRank nonStartWeight i := by
  rw [physicalPosition_eq_printed, if_neg (by exact Nat.succ_ne_zero i.val)]
  apply congrArg (fun n : ℕ => 1+n)
  calc
    _ = ∑ j : Fin 941, if nonStartWeight i < nonStartWeight j then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      exact floor_weight_indicator _ _ (weight_small i.succ) (weight_small j.succ)
    _ = strictRank nonStartWeight i := (strictRank_eq_sum _ _).symm

theorem physicalPosition_lt (i : Fin 942) : physicalPosition i < 942 := by
  cases i using Fin.cases with
  | zero => rw [physicalPosition_zero]; omega
  | succ j =>
      rw [physicalPosition_succ]
      have h : strictRank nonStartWeight j < 941 := by
        have := strictRank_lt_card nonStartWeight j
        simpa using this
      omega

theorem physicalPosition_injective : Function.Injective physicalPosition := by
  intro i j h
  cases i using Fin.cases <;> cases j using Fin.cases
  · rfl
  · rw [physicalPosition_zero, physicalPosition_succ] at h
    omega
  · rw [physicalPosition_succ, physicalPosition_zero] at h
    omega
  · rename_i i j
    rw [physicalPosition_succ, physicalPosition_succ] at h
    have he : strictRank nonStartWeight i = strictRank nonStartWeight j := by omega
    exact congrArg Fin.succ (strictRank_injective nonStartWeight_injective he)

noncomputable def physicalMap (i : Fin 942) : Fin 942 := ⟨physicalPosition i, physicalPosition_lt i⟩

theorem physicalMap_injective : Function.Injective physicalMap := by
  intro i j h
  exact physicalPosition_injective (congrArg Fin.val h)

theorem physicalMap_bijective : Function.Bijective physicalMap :=
  ⟨physicalMap_injective, Finite.surjective_of_injective physicalMap_injective⟩

noncomputable def physicalEquiv : Fin 942 ≃ Fin 942 :=
  Equiv.ofBijective physicalMap physicalMap_bijective

theorem physicalEquiv_val (i : Fin 942) : (physicalEquiv i).val = physicalPosition i := rfl

theorem physical_symm (p : Fin 942) : physicalPosition (physicalEquiv.symm p) = p.val := by
  rw [← physicalEquiv_val, Equiv.apply_symm_apply]

/-- Sums over tiles at their physical positions are sums over positions. -/
theorem phys_sum (g : ℕ → ℕ) :
    (∑ i : Fin 942, g (physicalPosition i)) = ∑ p ∈ Finset.range 942, g p := by
  have he := Equiv.sum_comp physicalEquiv (fun p : Fin 942 => g p.val)
  change (∑ i : Fin 942, g (physicalPosition i)) = ∑ p : Fin 942, g p.val at he
  rw [he]
  exact Fin.sum_univ_eq_sum_range g 942

theorem physical_lt_iff_weight (i j : Fin 942) (hi : i ≠ 0) (hj : j ≠ 0) :
    physicalPosition i < physicalPosition j ↔
      selectorWeight (tile j) < selectorWeight (tile i) := by
  cases i using Fin.cases with
  | zero => exact False.elim (hi rfl)
  | succ a =>
      cases j using Fin.cases with
      | zero => exact False.elim (hj rfl)
      | succ b =>
          rw [physicalPosition_succ, physicalPosition_succ, Nat.add_lt_add_iff_left]
          exact strictRank_lt_iff _ _ _

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

theorem selector_source_injective (h : ℕ) :
    Set.InjOn (source h) (selectorEntries h : Set Entry) := by
  intro e he f hf hef
  have he' := (Finset.mem_filter.mp he).2.1
  have hf' := (Finset.mem_filter.mp hf).2.1
  apply position_injective
  unfold source at hef
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
