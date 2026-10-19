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

def residueNatAP (r p : Nat) (a : Fin p) : NatAP where
  start := a
  step := p
  length := (r - 1 - a) / p + 1

theorem residueNatAP_index_lt {r p : Nat} (hp : 0 < p) (hpr : p ≤ r)
    (a : Fin p) (i : Nat) : i < (residueNatAP r p a).length ↔ a + i * p < r := by
  change i < (r - 1 - a) / p + 1 ↔ _
  rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hp]
  omega

theorem residueNatAP_mem (r p : Nat) (a : Fin p) (x : Nat) :
    x ∈ (residueNatAP r p a).carrier ↔
      ∃ i : Nat, i < (residueNatAP r p a).length ∧ a + i * p = x := by
  simp only [NatAP.carrier, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.isLt, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

theorem residueNatAP_proper {r p : Nat} (hp : 0 < p) (a : Fin p) :
    (residueNatAP r p a).IsProper := by
  refine ⟨hp, ?_⟩
  unfold NatAP.carrier
  rw [Finset.card_image_of_injective]
  · simp
  · intro i j hij
    exact Fin.ext (Nat.mul_right_cancel hp (Nat.add_left_cancel hij))

theorem residueNatAP_partition {r p : Nat} (hp : 0 < p) (hpr : p ≤ r) :
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
    obtain ⟨i, _, hix⟩ := (residueNatAP_mem r p a x).mp hx
    obtain ⟨j, _, hjx⟩ := (residueNatAP_mem r p b x).mp hx'
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
  have hv2 : 1 ≤ v ^ 2 := one_le_pow₀ hv
  have hpr : p ≤ r := by nlinarith
  obtain ⟨w, hw⟩ : ∃ w, v ^ 2 = w + 1 := ⟨v ^ 2 - 1, by omega⟩
  let P := residueNatAP r p
  have hlong (a : Fin p) : v ^ 2 ≤ (residueNatAP r p a).length := by
    have := (residueNatAP_index_lt hp hpr a w).2 (by rw [hw] at hsize; nlinarith [a.isLt])
    omega
  choose L R hL hRpart hRcells hRstep using
    fun a => section5_target_interval_partition_unit_step (P a).length v hv (hlong a)
  let T (a : Fin p) (i : Fin (L a)) := section5NatTransport (P a) (R a i)
  refine ⟨∑ a, L a, section5NatFlatten L T,
    (hL ⟨0, hp⟩).trans_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ _)),
    section5NatFlatten_partition P _ L T (residueNatAP_partition hp hpr) fun a =>
      section5NatTransport_partition (P a) (R a) (residueNatAP_proper hp a) (hRpart a),
    fun j => ?_, fun j => ?_⟩
  · let z := (section5NatFlattenEquiv L).symm j
    exact ⟨section5NatTransport_isProper (P z.1) (R z.1 z.2)
      (residueNatAP_proper hp z.1) (hRcells z.1 z.2).1, (hRcells z.1 z.2).2⟩
  · change (R _ _).step * p = p
    rw [hRstep, one_mul]

end LeanProofs.GowersSzemeredi
