import GowersSzemeredi.Proofs13BaseRowSelection
import GowersSzemeredi.ProofInfrastructure

/-!
# Selecting a progression cell in Lemma 13.7

A partition of the columns induces a partition of the selected upper
endpoints. Weighted averaging then preserves both Stage 13.6 density bounds
on one cell. This module assembles Stage 13.7 once an affine partition of the
selected base row, with the required progression lengths, is supplied.

`Stage137AffineBasePartition`, `lemma_13_7_of_affine_base_partitions`,
`lemma_13_7_of_affine_base_partitions_nonempty` and
`lemma_13_7_of_empty_heights` are in `Proofs13PartitionSelectionSide`, outside
the final route. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Finset

namespace LeanProofs.GowersSzemeredi

/-- A column partition partitions the selected upper endpoints exactly. -/
theorem stage137UpperEndpoints_partition {N q : Nat}
    (R I : Finset (ZMod N)) (P : Fin q → Finset (ZMod N))
    (Y : ZMod N → Finset (Pair N)) (y : ZMod N)
    (hP : IsPartition P R) :
    IsPartition (fun i ↦ stage137UpperEndpoints (P i) I Y y)
      (stage137UpperEndpoints R I Y y) := by
  constructor
  · intro z
    constructor
    · intro hz
      obtain ⟨hzprod, hzY⟩ := Finset.mem_filter.mp hz
      obtain ⟨hzR, hzI⟩ := Finset.mem_product.mp hzprod
      obtain ⟨i, hi⟩ := (hP.1 z.1).mp hzR
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hi, hzI⟩, hzY⟩⟩
    · rintro ⟨i, hi⟩
      obtain ⟨hzprod, hzY⟩ := Finset.mem_filter.mp hi
      obtain ⟨hzP, hzI⟩ := Finset.mem_product.mp hzprod
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hP.cell_subset i hzP, hzI⟩, hzY⟩
  · intro i j hij
    rw [Finset.disjoint_left]
    intro z hi hj
    exact Finset.disjoint_left.mp (hP.2 i j hij)
      (Finset.mem_product.mp (Finset.mem_filter.mp hi).1).1
      (Finset.mem_product.mp (Finset.mem_filter.mp hj).1).1

/-- Weighted averaging selects one column cell preserving a given density
of upper endpoints. No uniformity of cell sizes is assumed. -/
theorem exists_stage137_partition_cell {N q : Nat}
    (R I : Finset (ZMod N)) (P : Fin q → Finset (ZMod N))
    (Y : ZMod N → Finset (Pair N)) (y : ZMod N)
    (hR : R.Nonempty) (hP : IsPartition P R) {b : Real}
    (hb : b * R.card ≤ (stage137UpperEndpoints R I Y y).card) :
    ∃ i : Fin q, b * (P i).card ≤ (stage137UpperEndpoints (P i) I Y y).card := by
  obtain ⟨x, hx⟩ := hR
  obtain ⟨i, _⟩ := (hP.1 x).mp hx
  letI : Nonempty (Fin q) := ⟨i⟩
  have hsum : (∑ i, b * ((P i).card : Real)) ≤
      ∑ i, ((stage137UpperEndpoints (P i) I Y y).card : Real) := by
    rw [← Finset.mul_sum, ← Nat.cast_sum, hP.sum_card,
      ← Nat.cast_sum, (stage137UpperEndpoints_partition R I P Y y hP).sum_card]
    exact hb
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨i, hi⟩

/-- Preserve both density bounds on a single progression cell. -/
theorem exists_stage137_partition_cell_two_bounds {N q : Nat}
    (R I : Finset (ZMod N)) (P : Fin q → Finset (ZMod N))
    (Y : ZMod N → Finset (Pair N)) (y : ZMod N)
    (hR : R.Nonempty) (hP : IsPartition P R) {b₁ b₂ : Real}
    (h₁ : b₁ * R.card ≤ (stage137UpperEndpoints R I Y y).card)
    (h₂ : b₂ * R.card ≤ (stage137UpperEndpoints R I Y y).card) :
    ∃ i : Fin q,
      b₁ * (P i).card ≤ (stage137UpperEndpoints (P i) I Y y).card ∧
      b₂ * (P i).card ≤ (stage137UpperEndpoints (P i) I Y y).card := by
  obtain ⟨i, hi⟩ := exists_stage137_partition_cell R I P Y y hR hP
    (b := max b₁ b₂) (by
      rcases le_total b₁ b₂ with h | h
      · simpa only [max_eq_right h] using h₂
      · simpa only [max_eq_left h] using h₁)
  exact ⟨i,
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)).trans hi,
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg _)).trans hi⟩

/-- Stage 13.6's quantitative lower bound forces its progression to be
nonempty, even when the set of critical displacements is empty. -/
theorem stage136_progression_nonempty {N : Nat} [NeZero N]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (F : Stage136Data N) (hF : IsStage136Data S D E F) :
    F.R.carrier.Nonempty := by
  have hα := S.alpha_pos
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hζ : 0 < section13Zeta S.alpha := by unfold section13Zeta; positivity
  have hlen : (0 : Real) < F.R.length := lt_of_lt_of_le
    (by positivity) hF.2.2.2.1
  apply Finset.card_pos.mp
  have hcard : F.R.carrier.card = F.R.length := hF.2.2.1
  rw [hcard]
  exact_mod_cast hlen

/-- The Freiman hypothesis needed for the remaining base-row partition
follows by restriction from the original Section 13 context. -/
theorem section13_base_row_freiman {N : Nat} [NeZero N]
    (S : Section13Context N) (R : Finset (ZMod N)) (y : ZMod N) :
    FreimanHom 8 (R.filter fun x ↦ (x, y) ∈ S.A) (fun x ↦ S.phi (x, y)) := by
  apply IsAddFreimanHom.subset _ (S.separately_freiman.2 y) (Set.mapsTo_univ _ _)
  intro x hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩

end LeanProofs.GowersSzemeredi
