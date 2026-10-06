import GowersSzemeredi.Proofs05TargetPartition

/-!
# Target-length partitions with a prescribed difference

Partition an interval into residue classes modulo p, then cut each class into
consecutive chunks. The hypothesis p*v^2 ≤ r makes every residue class long
enough for the rounding-safe target partition. All output cells have common
difference p, as required after polynomial recurrence in Corollary 5.6.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Finset

namespace LeanProofs.GowersSzemeredi

private def residueNatAP (r p : Nat) (a : Fin p) : NatAP where
  start := a
  step := p
  length := (r - 1 - a) / p + 1

private lemma residueNatAP_index_lt {r p : Nat} (hp : 0 < p) (hpr : p ≤ r)
    (a : Fin p) (i : Nat) : i < (residueNatAP r p a).length ↔ a + i * p < r := by
  have har : (a : Nat) ≤ r - 1 := by omega
  change i < (r - 1 - a) / p + 1 ↔ _
  rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hp]
  omega

private lemma residueNatAP_mem (r p : Nat) (a : Fin p) (x : Nat) :
    x ∈ (residueNatAP r p a).carrier ↔
      ∃ i : Nat, i < (residueNatAP r p a).length ∧ a + i * p = x := by
  simp only [NatAP.carrier, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.isLt, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

private lemma residueNatAP_proper {r p : Nat} (hp : 0 < p) (a : Fin p) :
    (residueNatAP r p a).IsProper := by
  refine ⟨hp, ?_⟩
  unfold NatAP.carrier
  rw [Finset.card_image_of_injective]
  · simp
  · intro i j hij
    apply Fin.ext
    exact Nat.mul_right_cancel hp (Nat.add_left_cancel hij)

private lemma residueNatAP_partition {r p : Nat} (hp : 0 < p) (hpr : p ≤ r) :
    IsNatAPPartition (residueNatAP r p) (Finset.range r) := by
  constructor
  · intro x
    simp only [mem_range, residueNatAP_mem]
    constructor
    · intro hx
      refine ⟨⟨x % p, Nat.mod_lt _ hp⟩, x / p, ?_, ?_⟩
      · apply (residueNatAP_index_lt hp hpr _ _).2
        simpa [Nat.mul_comm, Nat.mod_add_div] using hx
      · simpa [Nat.mul_comm] using Nat.mod_add_div x p
    · rintro ⟨a, i, hi, rfl⟩
      exact (residueNatAP_index_lt hp hpr a i).1 hi
  · intro a b hne
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨i, hi, hix⟩ := (residueNatAP_mem r p a x).mp hx
    obtain ⟨j, hj, hjx⟩ := (residueNatAP_mem r p b x).mp hx'
    have hmod := congrArg (fun x : Nat => x % p) (hix.trans hjx.symm)
    have hab : a = b := by
      apply Fin.ext
      simpa [Nat.add_mod, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using hmod
    exact (bne_iff_ne.mp hne) hab

/-- Cut an interval into almost-equal nonempty progressions of a prescribed
common difference. The number of cells is determined by the construction. -/
theorem section5_residue_target_partition (r p v : Nat)
    (hp : 0 < p) (hv : 1 ≤ v) (hsize : p * v ^ 2 ≤ r) :
    ∃ M : Nat, ∃ Q : Fin M → NatAP,
      0 < M ∧ IsNatAPPartition Q (Finset.range r) ∧
      (∀ j, (Q j).IsProper ∧ 0 < (Q j).length ∧
        ((Q j).length = v - 1 ∨ (Q j).length = v)) ∧
      ∀ j, (Q j).step = p := by
  classical
  have hv2 : 1 ≤ v ^ 2 := one_le_pow₀ hv
  have hpr : p ≤ r := by nlinarith
  let P := residueNatAP r p
  have hlong (a : Fin p) : v ^ 2 ≤ (P a).length := by
    have hprod : p * (v ^ 2 - 1) + p ≤ r := by
      rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hv2]
      exact hsize
    have hi : (a : Nat) + (v ^ 2 - 1) * p < r := by nlinarith [a.isLt]
    have := (residueNatAP_index_lt hp hpr a (v ^ 2 - 1)).2 hi
    change v ^ 2 ≤ (residueNatAP r p a).length
    omega
  choose L R hL hRpart hRcells hRstep using
    fun a => section5_target_interval_partition_unit_step (P a).length v hv (hlong a)
  let T (a : Fin p) (i : Fin (L a)) := section5NatTransport (P a) (R a i)
  have hTpart (a : Fin p) : IsNatAPPartition (T a) (P a).carrier :=
    section5NatTransport_partition (P a) (R a) (residueNatAP_proper hp a) (hRpart a)
  have hsum : 0 < ∑ a, L a := by
    let a : Fin p := ⟨0, hp⟩
    exact (hL a).trans_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ a))
  refine ⟨∑ a, L a, section5NatFlatten L T, hsum,
    section5NatFlatten_partition P _ L T (residueNatAP_partition hp hpr) hTpart, ?_, ?_⟩
  · intro j
    let z := (section5NatFlattenEquiv L).symm j
    exact ⟨section5NatTransport_isProper (P z.1) (R z.1 z.2)
      (residueNatAP_proper hp z.1) (hRcells z.1 z.2).1, (hRcells z.1 z.2).2⟩
  · intro j
    let z := (section5NatFlattenEquiv L).symm j
    change (R z.1 z.2).step * (P z.1).step = p
    rw [hRstep]
    simp [P, residueNatAP]

end LeanProofs.GowersSzemeredi
