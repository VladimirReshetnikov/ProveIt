import GowersSzemeredi.Proofs18SmallArcUnwrap
import GowersSzemeredi.Proofs05BoxTransport

/-! Unwrapping a small-diameter modular partition gives a full partition
of an ordinary interval, with at most two pieces per original cell. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

/-- Intersecting the standard representatives of a modular partition with
an initial interval gives an exact finite-set partition of that interval. -/
theorem IsPartition.representatives_inter_range {N M L : Nat} [NeZero N]
    {P : Fin M → Finset (ZMod N)} (hP : IsPartition P Finset.univ) (hL : L ≤ N) :
    IsPartition (fun i => (P i).image ZMod.val ∩ Finset.range L) (Finset.range L) := by
  constructor
  · intro x
    constructor
    · intro hx
      have hxN : x < N := (Finset.mem_range.mp hx).trans_le hL
      obtain ⟨i, hi⟩ := (hP.1 (x : ZMod N)).mp (Finset.mem_univ _)
      refine ⟨i, Finset.mem_inter.mpr ⟨?_, hx⟩⟩
      exact Finset.mem_image.mpr ⟨(x : ZMod N), hi, ZMod.val_natCast_of_lt hxN⟩
    · rintro ⟨i, hi⟩
      exact (Finset.mem_inter.mp hi).2
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hxi).1
    obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hxj).1
    have hyz : y = z := ZMod.val_injective N (hyx.trans hzx.symm)
    subst z
    exact Finset.disjoint_left.mp (hP.2 i j hij) hy hz

/-- A small-arc progression clipped to an interval partitions into two
ordinary progression cells, permitting empty cells. -/
theorem ModAP.two_cell_interval_partition {N d L : Nat} [NeZero N]
    (P : ModAP N) (hP : P.IsProper) (hdiam : diameterAtMost P.carrier d)
    (hshort : 2 * (d + 1) < N) :
    ∃ R : Fin 2 → NatAP, (∀ j, (R j).IsProper) ∧
      IsNatAPPartition R ((P.carrier.image ZMod.val) ∩ Finset.range L) := by
  obtain ⟨Q, R, hQ, hR, hdis, hc⟩ := P.exists_two_natAPs_inter_interval (L := L) hP hdiam hshort
  refine ⟨![Q, R], ?_, ?_⟩
  · intro j
    fin_cases j
    · exact hQ
    · exact hR
  · constructor
    · intro x
      rw [← hc, Finset.mem_union]
      simp only [Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [Disjoint.symm hdis]

/-- The exact restriction of a small-diameter partition to an interval.
The output consists of ordinary progressions and has exactly twice as many
indexed cells (some may be empty). -/
theorem small_diameter_partition_interval_unwrap {N M L d : Nat} [NeZero N]
    (P : Fin M → ModAP N) (hP : IsPartition (fun i => (P i).carrier) Finset.univ)
    (hproper : ∀ i, (P i).IsProper) (hL : L ≤ N)
    (hdiam : ∀ i, diameterAtMost (P i).carrier d) (hshort : 2 * (d + 1) < N) :
    ∃ J : Nat, ∃ R : Fin J → NatAP,
      J = 2 * M ∧ IsNatAPPartition R (Finset.range L) ∧
      (∀ j, (R j).IsProper) ∧
      ∀ f : ZMod N → Complex,
        (∀ x, L ≤ x.val → f x = 0) →
        (∑ i, ‖∑ x ∈ (P i).carrier, f x‖) ≤
          ∑ j, ‖∑ t ∈ (R j).carrier, f (t : ZMod N)‖ := by
  choose S hSproper hS using fun i =>
    (P i).two_cell_interval_partition (L := L) (hproper i) (hdiam i) hshort
  let sizes : Fin M → Nat := fun _ => 2
  refine ⟨∑ i, sizes i, section5NatFlatten sizes S, by simp [sizes, mul_comm],
    finsetPartition_flatten sizes _ _ (fun i j => (S i j).carrier)
      (hP.representatives_inter_range hL) hS,
    section5NatFlatten_isProper sizes S hSproper, fun f hsupp => ?_⟩
  have hsum (i : Fin M) : (∑ x ∈ (P i).carrier, f x) =
      ∑ t ∈ ((P i).carrier.image ZMod.val) ∩ Finset.range L, f (t : ZMod N) := by
    rw [Finset.sum_subset Finset.inter_subset_left, Finset.sum_image (ZMod.val_injective N).injOn]
    · simp only [ZMod.natCast_zmod_val]
    · intro t ht hout
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp ht
      rw [ZMod.natCast_zmod_val]
      exact hsupp x (not_lt.mp fun h => hout (Finset.mem_inter.mpr ⟨ht, Finset.mem_range.mpr h⟩))
  refine le_of_le_of_eq (Finset.sum_le_sum fun i _ => ?_)
    (((section5NatFlattenEquiv sizes).symm.sum_comp
      (fun z => ‖∑ t ∈ (S z.1 z.2).carrier, f (t : ZMod N)‖)).trans (Fintype.sum_sigma _)).symm
  rw [hsum, ← (hS i).sum_weights (fun t => f (t : ZMod N))]
  exact norm_sum_le _ _

end LeanProofs.GowersSzemeredi
