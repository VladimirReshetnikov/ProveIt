import GowersSzemeredi.Proofs13BaseRowSelection
import GowersSzemeredi.ProofInfrastructure

/-!
# Selecting a progression cell in Lemma 13.7

A partition of the columns induces a partition of the selected upper
endpoints. Weighted averaging then preserves both Stage 13.6 density bounds
on one cell. This module assembles Stage 13.7 once an affine partition of the
selected base row, with the required progression lengths, is supplied.
-/

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
  classical
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
  classical
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

/-- The precise progression-partition input still required by Lemma 13.7.
It concerns only the original-domain base row, not all upper rows. -/
def Stage137AffineBasePartition {N : Nat} [NeZero N]
    (S : Section13Context N) (F : Stage136Data N) (y : ZMod N) : Prop :=
  ∃ q : Nat, ∃ P : Fin q → ModAP N,
    IsPartition (fun i ↦ (P i).carrier) F.R.carrier ∧
    ∀ i, (P i).step != 0 ∧ (P i).IsProper ∧
      (F.R.length : Real) ^ ((2 : Real) ^ (-(100 : Int)) * S.alpha ^ 448) ≤
        (P i).length ∧
      LinearOn ((P i).carrier.filter fun x ↦ (x, y) ∈ S.A)
        (fun x ↦ S.phi (x, y))

/-- All of the selection and assembly of Lemma 13.7, given a suitably long
affine partition of each sufficiently dense base row. -/
theorem lemma_13_7_of_affine_base_partitions_nonempty {N : Nat} [NeZero N]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (F : Stage136Data N) (hF : IsStage136Data S D E F)
    (hR : F.R.carrier.Nonempty) (hI : (criticalHeights S D E).Nonempty)
    (hpart : ∀ y : ZMod N,
      (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224 * F.R.length ≤
        (F.R.carrier.filter fun x ↦ (x, y) ∈ S.A).card →
      Stage137AffineBasePartition S F y) :
    ∃ G : Stage137Data N, IsStage137Data S D E F G := by
  classical
  have hRcard : F.R.carrier.card = F.R.length := hF.2.2.1
  have hY := hF.2.2.2.2.1
  obtain ⟨y, hy₁, hy₂⟩ := stage136_exists_base_row S D E F hF
  have hdense : (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224 * F.R.length ≤
      (F.R.carrier.filter fun x ↦ (x, y) ∈ S.A).card := by
    have h := stage137_base_row_density S.A F.R.carrier (criticalHeights S D E)
      F.Y y hI (fun h hh ↦ (hY h hh).1)
      (δ := (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224)
      (by simpa only [hRcard] using hy₁)
    simpa only [hRcard] using h
  obtain ⟨q, P, hP, hcell⟩ := hpart y hdense
  obtain ⟨i, hi₁, hi₂⟩ := exists_stage137_partition_cell_two_bounds
    F.R.carrier (criticalHeights S D E) (fun i ↦ (P i).carrier) F.Y y hR hP
    (b₁ := (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224 * (criticalHeights S D E).card)
    (b₂ := (2 : Real) ^ (-(48 : Int)) * S.alpha ^ 256 * E.Q.length)
    (by simpa only [hRcard, mul_assoc, mul_left_comm, mul_comm] using hy₁)
    (by simpa only [hRcard] using hy₂)
  obtain ⟨hstep, hproper, hlength, hbase⟩ := hcell i
  have hcard : (P i).carrier.card = (P i).length := hproper
  let B := stage137UpperEndpoints (P i).carrier (criticalHeights S D E) F.Y y
  refine ⟨⟨y, P i, B⟩, ?_, ?_⟩
  · refine ⟨hstep, hproper, hP.cell_subset i, hlength, Finset.filter_subset _ _, ?_, ?_, ?_⟩
    · simpa only [hcard, mul_assoc, mul_left_comm, mul_comm] using hi₁
    · simpa only [hcard] using hi₂
    · exact stage137UpperEndpoints_rows_linear S.A S.phi F.R.carrier (P i).carrier
        (criticalHeights S D E) F.Y y (hP.cell_subset i)
        (fun h hh ↦ (hY h hh).1) hbase (fun h hh ↦ (hY h hh).2.2)
  · exact stage137UpperEndpoints_subset_domain S.A (P i).carrier
      (criticalHeights S D E) F.Y y (fun h hh ↦ (hY h hh).1)

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
  classical
  apply IsAddFreimanHom.subset _ (S.separately_freiman.2 y) (Set.mapsTo_univ _ _)
  intro x hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩

/-- If there are no critical displacements, the whole progression with an
empty retained set already satisfies Stage 13.7. -/
theorem lemma_13_7_of_empty_heights {N : Nat} [NeZero N]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (F : Stage136Data N) (hF : IsStage136Data S D E F)
    (hI : criticalHeights S D E = ∅) :
    ∃ G : Stage137Data N, IsStage137Data S D E F G := by
  classical
  have hR := stage136_progression_nonempty S D E F hF
  have hcard : F.R.carrier.card = F.R.length := hF.2.2.1
  have hn : 0 < F.R.length := by simpa only [hcard] using hR.card_pos
  have hnR : (0 : Real) < F.R.length := by exact_mod_cast hn
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hα := S.alpha_pos
  have hQ : E.Q.length = 0 := by
    by_contra hQ
    have hQpos : (0 : Real) < E.Q.length := by exact_mod_cast Nat.pos_of_ne_zero hQ
    have hb := hF.2.2.2.2.2.2
    rw [hI] at hb
    have hp : 0 < (2 : Real) ^ (-(48 : Int)) * S.alpha ^ 256 *
        E.Q.length * F.R.length * N := by positivity
    exact not_le_of_gt hp (by simpa only [Finset.sum_empty, Nat.cast_zero] using hb)
  have hexp : (2 : Real) ^ (-(100 : Int)) * S.alpha ^ 448 ≤ 1 := by
    calc
      _ ≤ (2 : Real) ^ (-(100 : Int)) * 1 := mul_le_mul_of_nonneg_left
        (pow_le_one₀ hα.le S.alpha_at_most_one) (by positivity)
      _ ≤ 1 := by norm_num
  have hwidth : (F.R.length : Real) ^
      ((2 : Real) ^ (-(100 : Int)) * S.alpha ^ 448) ≤ F.R.length :=
    Real.rpow_le_self_of_one_le (by exact_mod_cast hn) hexp
  refine ⟨⟨0, F.R, ∅⟩, ?_, Finset.empty_subset _⟩
  refine ⟨hF.2.1, hF.2.2.1, Finset.Subset.refl _, hwidth,
    Finset.empty_subset _, ?_, ?_, ?_⟩
  · simp [hI]
  · simp [hQ]
  · intro h hh
    simp only [hI, Finset.notMem_empty] at hh

/-- Lemma 13.7 is reduced solely to the quantitative affine partition of a
dense base row. All empty cases, averaging, domain containment, and upper-row
linearity are discharged here. -/
theorem lemma_13_7_of_affine_base_partitions {N : Nat} [NeZero N]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (F : Stage136Data N) (hF : IsStage136Data S D E F)
    (hpart : ∀ y : ZMod N,
      (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224 * F.R.length ≤
        (F.R.carrier.filter fun x ↦ (x, y) ∈ S.A).card →
      Stage137AffineBasePartition S F y) :
    ∃ G : Stage137Data N, IsStage137Data S D E F G := by
  classical
  by_cases hI : (criticalHeights S D E).Nonempty
  · exact lemma_13_7_of_affine_base_partitions_nonempty S D E F hF
      (stage136_progression_nonempty S D E F hF) hI hpart
  · exact lemma_13_7_of_empty_heights S D E F hF (Finset.not_nonempty_iff_eq_empty.mp hI)

end LeanProofs.GowersSzemeredi
