import GowersSzemeredi.ProgressionChunks
import GowersSzemeredi.Proofs05Lemma9Induction

/-!
# Prescribed target lengths for polynomial partitions

The degree induction in Corollary 5.6 needs an emergent number of nonempty
cells of length v-1 or v. We construct this refinement on ordinary progressions
and preserve containment, so any previously established diameter bound survives.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Finset

namespace LeanProofs.GowersSzemeredi

open BaseCase

private def chunkNatAP (L m : Nat) (j : Fin (L / m)) : NatAP where
  start := coarseChunkStart m (L % m) j
  step := 1
  length := coarseChunkLength m (L % m) j

private lemma chunkNatAP_mem (L m : Nat) (j : Fin (L / m)) (x : Nat) :
    x ∈ (chunkNatAP L m j).carrier ↔
      ∃ i : Nat, i < coarseChunkLength m (L % m) j ∧
        x = coarseChunkStart m (L % m) j + i := by
  simp only [NatAP.carrier, chunkNatAP, mem_image, mem_univ, true_and, mul_one]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.isLt, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

private lemma chunkNatAP_proper (L m : Nat) (j : Fin (L / m)) :
    (chunkNatAP L m j).IsProper := by
  refine ⟨by simp [chunkNatAP], ?_⟩
  unfold NatAP.carrier
  rw [Finset.card_image_of_injective]
  · simp
  · intro i j hij
    apply Fin.ext
    simpa [chunkNatAP] using hij

private lemma chunkNatAP_partition (L m : Nat) (hm : 0 < m) (hLm : m * m ≤ L) :
    IsNatAPPartition (chunkNatAP L m) (Finset.range L) := by
  constructor
  · intro x
    simp only [mem_range, chunkNatAP_mem]
    constructor
    · exact exists_coarseChunk hm hLm
    · rintro ⟨j, i, hi, rfl⟩
      exact coarseChunk_index_lt hm hLm j hi
  · intro j j' hne
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨i, hi, hxi⟩ := (chunkNatAP_mem L m j x).mp hx
    obtain ⟨i', hi', hxi'⟩ := (chunkNatAP_mem L m j' x).mp hx'
    exact (bne_iff_ne.mp hne) (coarseChunk_unique j j' i i' hi hi' hxi hxi')

/-- An interval at least as long as the square of the target admits a
partition into nonempty progressions of target length or target minus one. -/
theorem section5_target_interval_partition_unit_step (L v : Nat)
    (hv : 1 ≤ v) (hL : v ^ 2 ≤ L) :
    ∃ M : Nat, ∃ P : Fin M → NatAP,
      0 < M ∧ IsNatAPPartition P (Finset.range L) ∧
      (∀ j, (P j).IsProper ∧ 0 < (P j).length ∧
        ((P j).length = v - 1 ∨ (P j).length = v)) ∧
      ∀ j, (P j).step = 1 := by
  by_cases hv1 : v = 1
  · subst v
    have hLpos : 0 < L := by norm_num at hL; omega
    refine ⟨L / 1, chunkNatAP L 1, by simpa, chunkNatAP_partition L 1 (by omega)
      (by simpa using hL), ?_, fun _ => rfl⟩
    intro j
    refine ⟨chunkNatAP_proper L 1 j, ?_, Or.inr ?_⟩ <;>
      simp [chunkNatAP, coarseChunkLength, Nat.mod_one]
  · let m := v - 1
    have hm : 0 < m := by dsimp [m]; omega
    have hLm : m * m ≤ L := by
      have hmv : m ≤ v := Nat.sub_le _ _
      exact (Nat.mul_le_mul hmv hmv).trans (by simpa [pow_two] using hL)
    have hmL : m ≤ L := by nlinarith
    refine ⟨L / m, chunkNatAP L m, Nat.div_pos hmL hm,
      chunkNatAP_partition L m hm hLm, ?_, fun _ => rfl⟩
    intro j
    refine ⟨chunkNatAP_proper L m j, ?_, ?_⟩
    · exact lt_of_lt_of_le hm (coarseChunk_length_bounds hm j).1
    · dsimp only [chunkNatAP]
      unfold coarseChunkLength
      split_ifs
      · right; dsimp [m]; omega
      · exact Or.inl rfl

/-- The target partition with only its length and properness data exposed. -/
theorem section5_target_interval_partition (L v : Nat)
    (hv : 1 ≤ v) (hL : v ^ 2 ≤ L) :
    ∃ M : Nat, ∃ P : Fin M → NatAP,
      0 < M ∧ IsNatAPPartition P (Finset.range L) ∧
      ∀ j, (P j).IsProper ∧ 0 < (P j).length ∧
        ((P j).length = v - 1 ∨ (P j).length = v) := by
  obtain ⟨M, P, hM, hpart, hcells, _⟩ :=
    section5_target_interval_partition_unit_step L v hv hL
  exact ⟨M, P, hM, hpart, hcells⟩

/-- The target partition transported to an arbitrary proper natural progression. -/
theorem section5_target_progression_partition (P : NatAP) (v : Nat)
    (hP : P.IsProper) (hv : 1 ≤ v) (hL : v ^ 2 ≤ P.length) :
    ∃ M : Nat, ∃ Q : Fin M → NatAP,
      0 < M ∧ IsNatAPPartition Q P.carrier ∧
      (∀ j, (Q j).IsProper ∧ 0 < (Q j).length ∧
        ((Q j).length = v - 1 ∨ (Q j).length = v)) ∧
      ∀ j, (Q j).carrier ⊆ P.carrier := by
  obtain ⟨M, R, hM, hpart, hcells⟩ := section5_target_interval_partition P.length v hv hL
  refine ⟨M, fun j => section5NatTransport P (R j), hM,
    section5NatTransport_partition P R hP hpart, ?_, ?_⟩
  · intro j
    exact ⟨section5NatTransport_isProper P (R j) hP (hcells j).1,
      (hcells j).2⟩
  · intro j
    exact section5NatTransport_subset P (R j) (IsPartition.cell_subset hpart j)

/-- Refine a partition whose cells are sufficiently long to a common target
length, keeping every refined cell inside one original cell. -/
theorem section5_refine_target_lengths {M r v : Nat} (P : Fin M → NatAP)
    (hr : 0 < r) (hv : 1 ≤ v) (hpart : IsNatAPPartition P (Finset.range r))
    (hP : ∀ j, (P j).IsProper) (hlong : ∀ j, v ^ 2 ≤ (P j).length) :
    ∃ q : Nat, ∃ Q : Fin q → NatAP,
      0 < q ∧ IsNatAPPartition Q (Finset.range r) ∧
      (∀ j, (Q j).IsProper ∧ 0 < (Q j).length ∧
        ((Q j).length = v - 1 ∨ (Q j).length = v)) ∧
      ∀ j, ∃ i, (Q j).carrier ⊆ (P i).carrier := by
  classical
  choose L R hL hRpart hRcells hRsub using
    fun i => section5_target_progression_partition (P i) v (hP i) hv (hlong i)
  have hsum : 0 < ∑ i, L i := by
    obtain ⟨i, _⟩ := (hpart.1 0).mp (Finset.mem_range.mpr hr)
    exact (hL i).trans_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i))
  refine ⟨∑ i, L i, section5NatFlatten L R, hsum,
    section5NatFlatten_partition P _ L R hpart hRpart, ?_, ?_⟩
  · intro j
    let z := (section5NatFlattenEquiv L).symm j
    exact hRcells z.1 z.2
  · intro j
    let z := (section5NatFlattenEquiv L).symm j
    exact ⟨z.1, hRsub z.1 z.2⟩

end LeanProofs.GowersSzemeredi
