import GowersSzemeredi.Proofs13PartitionSelection

/-! Declarations of `Proofs13PartitionSelection` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Finset

namespace LeanProofs.GowersSzemeredi

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

/-- If there are no critical displacements, the whole progression with an
empty retained set already satisfies Stage 13.7. -/
theorem lemma_13_7_of_empty_heights {N : Nat} [NeZero N]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (F : Stage136Data N) (hF : IsStage136Data S D E F)
    (hI : criticalHeights S D E = ∅) :
    ∃ G : Stage137Data N, IsStage137Data S D E F G := by
  have hR := stage136_progression_nonempty S D E F hF
  have hcard : F.R.carrier.card = F.R.length := hF.2.2.1
  have hn : 0 < F.R.length := by simpa only [hcard] using hR.card_pos
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hα := S.alpha_pos
  have hQ : E.Q.length = 0 := by
    by_contra hQ
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
  by_cases hI : (criticalHeights S D E).Nonempty
  · exact lemma_13_7_of_affine_base_partitions_nonempty S D E F hF
      (stage136_progression_nonempty S D E F hF) hI hpart
  · exact lemma_13_7_of_empty_heights S D E F hF (Finset.not_nonempty_iff_eq_empty.mp hI)

end LeanProofs.GowersSzemeredi
