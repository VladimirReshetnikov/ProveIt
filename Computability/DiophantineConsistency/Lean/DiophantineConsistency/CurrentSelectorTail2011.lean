import DiophantineConsistency.WangTiles942Permutation
import DiophantineConsistency.CurrentKernel2011

/-!
# The exact physical selector tail used by the early padding reset

The cutoff is abstract tile866, whose physical position is459. The proof
uses the complete table and a South-coordinate threshold, not an evaluated
941-by941 floor table. All sums refer to the actual printed coefficients.
-/

namespace DiophantineConsistency.CurrentSelectorTail2011

open WangTiles942
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option exponentiation.threshold 1024

def cutoffTile : Tile := ⟨0,1,221,45⟩
def cutoff : ℕ := 1575850607617

theorem cutoff_tile : tile 866 = cutoffTile := by decide +kernel

theorem cutoff_weight : selectorWeight cutoffTile = cutoff := by decide +kernel

private theorem transition_no_south45 (j : Fin 430) :
    (transitionRow j).2.south ≠ 45 := by
  have h := Bool.toNat_le (action j).1
  change (action j).1.toNat ≠ 45
  omega

private theorem copies_no_south45 : ∀ a : Fin 2, ∀ row ∈ copyRows a.val,
    row.2.south ≠ 45 := by decide +kernel

private theorem tail_no_south45 : ∀ row ∈ tailRows, row.2.south ≠ 45 := by decide +kernel

private theorem right_target21_absent : 21 ∉ targetList true := by decide +kernel
private theorem left_rail21 : rail false 21 = 221 := by decide +kernel

private theorem signals_south45 (d : Bool) : ∀ row ∈ signalRows d,
    row.2.south = 45 → row.2 = cutoffTile := by
  intro row hr hs
  obtain ⟨q,hq,hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hr
  have hb' : b < 2 := List.mem_range.mp hb
  change headColor q b = 45 at hs
  have hq' : q = 21 := by dsimp only [headColor] at hs; omega
  have hb' : b = 1 := by dsimp only [headColor] at hs; omega
  subst q
  subst b
  cases d
  · simp only [cutoffTile, Bool.toNat_false, Nat.zero_mul, Nat.sub_zero,
      Nat.one_mul, left_rail21, headColor]
  · exact False.elim (right_target21_absent hq)

private theorem rows_south45 : ∀ row ∈ orderedRows,
    row.2.south = 45 → row.2 = cutoffTile := by
  simp only [orderedRows, List.forall_mem_append]
  refine ⟨⟨⟨⟨by decide +kernel, ?_⟩, ?_⟩,
    ⟨signals_south45 true, signals_south45 false⟩⟩, ?_⟩
  · intro row hr h
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
    exact False.elim (transition_no_south45 j h)
  · constructor <;> intro row hr h
    · exact False.elim (copies_no_south45 1 row hr h)
    · exact False.elim (copies_no_south45 0 row hr h)
  · intro row hr h
    exact False.elim (tail_no_south45 row hr h)

/-- On the actual full table, the weight threshold has exactly this simple form. -/
theorem weight_le_cutoff_iff (i : Fin 942) :
    selectorWeight (tile i) ≤ cutoff ↔ (tile i).south ≤ 45 := by
  have ht := tile_bounded i
  obtain ⟨hw,he,hn,hs⟩ := ht
  by_cases h45 : (tile i).south = 45
  · have ht' : tile i = cutoffTile := rows_south45 _ (List.getElem_mem _) h45
    rw [ht', cutoff_weight]
    decide
  · dsimp only [selectorWeight, cutoff]
    omega

def lowCount (t : Tile) : ℕ := if t.south ≤ 45 then 1 else 0
def lowMass (t : Tile) : ℕ := if t.south ≤ 45 then selectorWeight t else 0

private theorem sum_map_congr {α : Type*} (l : List α) (f g : α → ℕ)
    (h : ∀ a ∈ l, f a = g a) : (l.map f).sum = (l.map g).sum :=
  congrArg List.sum (List.map_congr_left h)

private theorem sum_map_const {α : Type*} (l : List α) (f : α → ℕ) (v : ℕ)
    (h : ∀ a ∈ l, f a = v) : (l.map f).sum = v * l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]
      simp only [Nat.mul_succ, Nat.add_comm]

private theorem transition_low (j : Fin 430) : (transitionRow j).2.south ≤ 45 := by
  have h := Bool.toNat_le (action j).1
  change (action j).1.toNat ≤ 45
  omega

private theorem transition_low_count :
    ((List.ofFn transitionRow).map (fun row => lowCount row.2)).sum = 430 := by
  have h := sum_map_const (List.ofFn transitionRow) (fun row => lowCount row.2) 1
    (by
      intro row hr
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
      exact if_pos (transition_low j))
  simpa only [List.length_ofFn, Nat.one_mul] using h

private theorem transition_low_mass :
    ((List.ofFn transitionRow).map (fun row => lowMass row.2)).sum = 11139798681006 :=
  (sum_map_congr (List.ofFn transitionRow) (fun row => lowMass row.2)
    (fun row => selectorWeight row.2)
    (by
      intro row hr
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
      exact if_pos (transition_low j))).trans CurrentKernel2011.transition_mass

private theorem copy_low_count :
    ((copyRows 1 ++ copyRows 0).map (fun row => lowCount row.2)).sum = 2 := by decide +kernel
private theorem copy_low_mass :
    ((copyRows 1 ++ copyRows 0).map (fun row => lowMass row.2)).sum = 34360002562 := by decide +kernel

private theorem right_low_count :
    ((signalRows true).map (fun row => lowCount row.2)).sum = 14 := by decide +kernel
private theorem right_low_mass :
    ((signalRows true).map (fun row => lowMass row.2)).sum = 6562712006670 := by decide +kernel
private theorem left_low_count :
    ((signalRows false).map (fun row => lowCount row.2)).sum = 34 := by decide +kernel
private theorem left_low_mass :
    ((signalRows false).map (fun row => lowMass row.2)).sum = 33441962035234 := by decide +kernel

private theorem tail_low_count :
    (tailRows.map (fun row => lowCount row.2)).sum = 3 := by decide +kernel
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

theorem selected_count :
    ((orderedRows.drop 1).map (fun row => lowCount row.2)).sum = 483 :=
  sum_families (0,start) (fun row => lowCount row.2)
    (List.ofFn transitionRow) (copyRows 1 ++ copyRows 0)
    (signalRows true) (signalRows false) tailRows 430 2 14 34 3
    transition_low_count copy_low_count right_low_count left_low_count tail_low_count

theorem selected_mass :
    ((orderedRows.drop 1).map (fun row => lowMass row.2)).sum = 51317956228579 :=
  sum_families (0,start) (fun row => lowMass row.2)
    (List.ofFn transitionRow) (copyRows 1 ++ copyRows 0)
    (signalRows true) (signalRows false) tailRows
    11139798681006 34360002562 6562712006670 33441962035234 139123503107
    transition_low_mass copy_low_mass right_low_mass left_low_mass tail_low_mass

private theorem sum_nonStart (f : Tile → ℕ) :
    (∑ j : Fin 941, f (tile j.succ)) =
      ((orderedRows.drop 1).map (fun row => f row.2)).sum := by
  have h := congrArg (fun ts : List Tile => (ts.map f).sum) nonStart_rows
  simpa only [List.map_map, List.map_ofFn, List.sum_ofFn, Function.comp_def, Fin.succ] using h.symm

private theorem lowCount_sum : (∑ j : Fin 941, lowCount (tile j.succ)) = 483 :=
  (sum_nonStart lowCount).trans selected_count

private theorem lowMass_sum : (∑ j : Fin 941, lowMass (tile j.succ)) = 51317956228579 :=
  (sum_nonStart lowMass).trans selected_mass

private theorem upper_plus_low (j : Fin 941) :
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

private theorem sum_pair_card {α : Type*} [Fintype α] (f g : α → ℕ)
    (h : ∀ a, f a + g a = 1) : (∑ a, f a) + (∑ a, g a) = Fintype.card α := by
  rw [← Finset.sum_add_distrib]
  simp only [h, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]

private theorem sum_pair_remainder {α : Type*} [Fintype α] (f g : α → ℕ)
    (a b : ℕ) (h : ∀ x, f x + g x = 1) (hg : (∑ x, g x) = a)
    (hc : a+b = Fintype.card α) : (∑ x, f x) = b := by
  have hs := sum_pair_card f g h
  rw [hg] at hs
  omega

private theorem upper_cutoff_sum :
    (∑ j : Fin 941, if cutoff < nonStartWeight j then 1 else 0) = 458 :=
  sum_pair_remainder (fun j : Fin 941 => if cutoff < nonStartWeight j then 1 else 0)
    (fun j => lowCount (tile j.succ)) 483 458 upper_plus_low lowCount_sum (by decide)

private theorem rank_at_value {α : Type*} [Fintype α] (w : α → ℕ)
    (i : α) (v : ℕ) (h : w i = v) :
    strictRank w i = ∑ j, if v < w j then 1 else 0 := by
  rw [strictRank_eq_sum, h]

private theorem cutoff_abstract_weight : selectorWeight (tile 866) = cutoff :=
  (congrArg selectorWeight cutoff_tile).trans cutoff_weight

private theorem cutoff_rank : strictRank nonStartWeight (865 : Fin 941) = 458 :=
  (rank_at_value nonStartWeight 865 cutoff cutoff_abstract_weight).trans upper_cutoff_sum

/-- Exact position459 follows from the entire strict-upper-set count458. -/
theorem cutoff_position : physicalPosition 866 = 459 := by
  have h := physicalPosition_succ (865 : Fin 941)
  rw [cutoff_rank] at h
  exact h

/-- This characterizes the physical suffix, including the excluded Start slot. -/
theorem tail_position_iff (i : Fin 942) :
    459 ≤ physicalPosition i ↔ i ≠ 0 ∧ (tile i).south ≤ 45 := by
  by_cases hi : i = 0
  · subst i
    simp only [physicalPosition_zero, ne_eq, not_true_eq_false, false_and]
    decide
  · have hr := physical_lt_iff_weight i 866 hi (by decide)
    rw [cutoff_position, cutoff_abstract_weight] at hr
    rw [and_iff_right hi, ← weight_le_cutoff_iff]
    simpa only [Nat.not_lt] using not_congr hr

/-- The literal physical tail of the doubled Phi coefficients. Repeated
positions, if present in a stencil representation, would be summed once
per source monomial; the imported permutation also proves selector uniqueness. -/
def tailTerm (e : CurrentKernel2011.Entry) : ℕ :=
  if 459 ≤ CurrentKernel2011.position e then 2 * CurrentKernel2011.weight e else 0

def tailMass : ℕ := ∑ e : CurrentKernel2011.Entry, tailTerm e

private def selectorTailTerm (i : Fin 942) : ℕ :=
  if 459 ≤ physicalPosition i then 2 * selectorWeight (tile i) else 0

private theorem selectorTail_zero : selectorTailTerm 0 = 0 := by
  simp only [selectorTailTerm, physicalPosition_zero]
  decide

private theorem selectorTail_succ (j : Fin 941) :
    selectorTailTerm j.succ = 2 * lowMass (tile j.succ) := by
  simp only [selectorTailTerm, tail_position_iff, ne_eq, Fin.succ_ne_zero,
    not_false_eq_true, true_and, lowMass, mul_ite, mul_zero]

private theorem sum_zero_succ {n : ℕ} (f : Fin (n+1) → ℕ) (g : Fin n → ℕ)
    (h₀ : f 0 = 0) (hs : ∀ j, f j.succ = g j) : (∑ i, f i) = ∑ j, g j := by
  rw [Fin.sum_univ_succ, h₀, zero_add]
  exact Finset.sum_congr rfl (fun j _ => hs j)

private theorem sum_double {α : Type*} [Fintype α] (f : α → ℕ) (v : ℕ)
    (h : (∑ a, f a) = v) : (∑ a, 2 * f a) = 2 * v := by
  rw [← Finset.mul_sum, h]

private theorem selector_tail_mass : (∑ i : Fin 942, selectorTailTerm i) = 102635912457158 :=
  (sum_zero_succ selectorTailTerm (fun j => 2 * lowMass (tile j.succ))
    selectorTail_zero selectorTail_succ).trans
    (sum_double (fun j : Fin 941 => lowMass (tile j.succ)) 51317956228579 lowMass_sum)

private theorem control_tail_mass :
    (∑ e : Fin 8 ⊕ (Fin 9 ⊕ (Fin 8 ⊕ Fin 9)), tailTerm (.inr e)) = 35184372086784 := by
  decide +kernel

private theorem sum_types {α β : Type*} [Fintype α] [Fintype β]
    (f : α ⊕ β → ℕ) (g : α → ℕ) (h : β → ℕ) (a b : ℕ)
    (he : f = Sum.elim g h) (hg : (∑ x, g x) = a) (hh : (∑ y, h y) = b) :
    (∑ z, f z) = a+b := by
  rw [he, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, hg, hh]

/-- The complete exact T459, including all34 label coefficients. -/
theorem tailMass_eq : tailMass = 137820284543942 :=
  sum_types tailTerm selectorTailTerm (fun e => tailTerm (.inr e))
    102635912457158 35184372086784
    (by funext e; cases e <;> rfl) selector_tail_mass control_tail_mass

/-- An arbitrary Boolean source selection confined to the physical suffix
is bounded by the exact full tail; no tile/label decoding is a premise. -/
theorem tail_source_bound (a : CurrentKernel2011.Entry → ℕ)
    (ha : ∀ e, a e ≤ 1)
    (hz : ∀ e, CurrentKernel2011.position e < 459 → a e = 0) :
    (∑ e, 2 * CurrentKernel2011.weight e * a e) ≤ 137820284543942 := by
  rw [← tailMass_eq]
  apply Finset.sum_le_sum
  intro e _
  by_cases hp : 459 ≤ CurrentKernel2011.position e
  · rw [tailTerm, if_pos hp]
    exact le_trans (Nat.mul_le_mul_left _ (ha e)) (by simp)
  · rw [hz e (by omega), mul_zero]
    exact Nat.zero_le _

theorem early_reset_numeric : 137820284543942 + 2^10 + 60 < CurrentKernel2011.radix := by
  decide +kernel

/-- The full early raw contribution plus all incoming carry remains below
rho whenever the source indices are at least459. -/
theorem early_reset_bound (a : CurrentKernel2011.Entry → ℕ)
    (ha : ∀ e, a e ≤ 1)
    (hz : ∀ e, CurrentKernel2011.position e < 459 → a e = 0)
    (units temporal incoming : ℕ) (hu : units ≤ 3) (ht : temporal ≤ 2^10)
    (hk : incoming ≤ 57) :
    (∑ e, 2 * CurrentKernel2011.weight e * a e) + units + temporal + incoming <
      CurrentKernel2011.radix := by
  have hb := tail_source_bound a ha hz
  have hn := early_reset_numeric
  omega

end DiophantineConsistency.CurrentSelectorTail2011
