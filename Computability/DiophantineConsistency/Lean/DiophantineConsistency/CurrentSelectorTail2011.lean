import DiophantineConsistency.WangTiles942Permutation
import DiophantineConsistency.CurrentKernel2011
import DiophantineConsistency.ArithmeticCellPhysical

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

/-- On the actual full table, the weight threshold has exactly this simple form. -/
theorem weight_le_cutoff_iff (i : Fin 942) :
    selectorWeight (tile i) ≤ cutoff ↔ (tile i).south ≤ 45 :=
  ArithmeticCellPhysical.weight_le_cutoff_iff i

def lowCount (t : Tile) : ℕ := if t.south ≤ 45 then 1 else 0
def lowMass (t : Tile) : ℕ := if t.south ≤ 45 then selectorWeight t else 0

theorem selected_count :
    ((orderedRows.drop 1).map (fun row => lowCount row.2)).sum = 483 :=
  ArithmeticCellPhysical.selected_count

theorem selected_mass :
    ((orderedRows.drop 1).map (fun row => lowMass row.2)).sum = 51317956228579 :=
  ArithmeticCellPhysical.selected_mass

private theorem sum_nonStart (f : Tile → ℕ) :
    (∑ j : Fin 941, f (tile j.succ)) =
      ((orderedRows.drop 1).map (fun row => f row.2)).sum := by
  have h := congrArg (fun ts : List Tile => (ts.map f).sum) nonStart_rows
  simpa only [List.map_map, List.map_ofFn, List.sum_ofFn, Function.comp_def, Fin.succ] using h.symm

private theorem lowMass_sum : (∑ j : Fin 941, lowMass (tile j.succ)) = 51317956228579 :=
  (sum_nonStart lowMass).trans selected_mass

private theorem cutoff_abstract_weight : selectorWeight (tile 866) = cutoff :=
  (congrArg selectorWeight cutoff_tile).trans cutoff_weight

/-- Exact position459 follows from the entire strict-upper-set count458. -/
theorem cutoff_position : physicalPosition 866 = 459 :=
  ArithmeticCellPhysical.cutoff_position

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
    (∑ e, 2 * CurrentKernel2011.weight e * a e) ≤ 137820284543942 :=
  ArithmeticCellPhysical.tail_source_bound a ha hz

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
