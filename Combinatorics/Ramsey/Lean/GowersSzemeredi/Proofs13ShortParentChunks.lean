import GowersSzemeredi.Proofs05ResiduePartition

/-! Partitions into lengths between m and 2m-1 only require m points,
not m squared. This avoids an unnecessary scale loss in short-parent
localization for the Section 13 square construction. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Consecutive blocks of length m, with the remainder added to the last. -/
def shortParentChunk (L m : Nat) (j : Fin (L / m)) : NatAP where
  start := j.val * m
  step := 1
  length := if j.val + 1 = L / m then m + L % m else m

theorem shortParentChunk_mem (L m : Nat) (j : Fin (L / m)) (x : Nat) :
    x ∈ (shortParentChunk L m j).carrier ↔
      ∃ i : Nat, i < (shortParentChunk L m j).length ∧ x = j.val * m + i := by
  classical
  simp only [NatAP.carrier, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.val, i.isLt, by simp [shortParentChunk]⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, by simp [shortParentChunk]⟩

theorem shortParentChunk_isProper (L m : Nat) (j : Fin (L / m)) :
    (shortParentChunk L m j).IsProper := by
  classical
  refine ⟨by simp [shortParentChunk], ?_⟩
  unfold NatAP.carrier
  rw [Finset.card_image_of_injective]
  · simp
  · intro i k hik
    apply Fin.ext
    simpa only [shortParentChunk, mul_one, Nat.add_left_cancel_iff] using hik

theorem shortParentChunk_bounds {L m : Nat} (hm : 0 < m) (j : Fin (L / m)) :
    m ≤ (shortParentChunk L m j).length ∧ (shortParentChunk L m j).length < 2 * m := by
  have hr := Nat.mod_lt L hm
  dsimp [shortParentChunk]
  split_ifs <;> omega

theorem shortParentChunk_subset (L m : Nat) (j : Fin (L / m)) :
    (shortParentChunk L m j).carrier ⊆ Finset.range L := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := (shortParentChunk_mem L m j x).mp hx
  have hdiv : L / m * m + L % m = L := by simpa only [Nat.mul_comm] using Nat.div_add_mod L m
  have hj : j.val + 1 ≤ L / m := j.isLt
  have hjmul := Nat.mul_le_mul_right m hj
  apply Finset.mem_range.mpr
  dsimp [shortParentChunk] at hi
  split_ifs at hi with hlast
  · nlinarith only [hi, hdiv, hlast]
  · nlinarith only [hi, hdiv, hjmul, Nat.zero_le (L % m)]

/-- These blocks partition the interval for every positive m at most L. -/
theorem shortParentChunk_partition {L m : Nat} (hm : 0 < m) (hmL : m ≤ L) :
    IsNatAPPartition (shortParentChunk L m) (Finset.range L) := by
  classical
  have hn : 0 < L / m := Nat.div_pos hmL hm
  have hdiv : L / m * m + L % m = L := by simpa only [Nat.mul_comm] using Nat.div_add_mod L m
  constructor
  · intro x
    constructor
    · intro hx
      have hxL := Finset.mem_range.mp hx
      by_cases hxmain : x < L / m * m
      · have hj : x / m < L / m := (Nat.div_lt_iff_lt_mul hm).mpr hxmain
        let j : Fin (L / m) := ⟨x / m, hj⟩
        refine ⟨j, (shortParentChunk_mem L m j x).mpr ⟨x % m, ?_, ?_⟩⟩
        · exact (Nat.mod_lt x hm).trans_le (shortParentChunk_bounds hm j).1
        · simpa only [j, Nat.mul_comm] using (Nat.div_add_mod x m).symm
      · let j : Fin (L / m) := ⟨L / m - 1, by omega⟩
        have hjlast : j.val + 1 = L / m := by dsimp [j]; omega
        have hjmul : j.val * m + m = L / m * m := by nlinarith only [hjlast]
        have hxstart : j.val * m ≤ x := by omega
        refine ⟨j, (shortParentChunk_mem L m j x).mpr ⟨x - j.val * m, ?_, ?_⟩⟩
        · dsimp [shortParentChunk]
          rw [if_pos hjlast]
          omega
        · omega
    · rintro ⟨j, hx⟩
      exact shortParentChunk_subset L m j hx
  · intro j k hne
    have hsep (j k : Fin (L / m)) (hjk : j.val < k.val) :
        Disjoint (shortParentChunk L m j).carrier (shortParentChunk L m k).carrier := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      obtain ⟨i, hi, hxi⟩ := (shortParentChunk_mem L m j x).mp hx
      obtain ⟨l, _, hxl⟩ := (shortParentChunk_mem L m k x).mp hy
      have hjnot : j.val + 1 ≠ L / m := by have := k.isLt; omega
      have hbound := Nat.mul_le_mul_right m (show j.val + 1 ≤ k.val by omega)
      dsimp [shortParentChunk] at hi
      rw [if_neg hjnot] at hi
      nlinarith only [hi, hxi, hxl, hbound]
    have hjk : j.val ≠ k.val := fun h => bne_iff_ne.mp hne (Fin.ext h)
    rcases lt_or_gt_of_ne hjk with h | h
    · exact hsep j k h
    · exact (hsep k j h).symm

/-- Prescribed-step partitioning into lengths in [m,2m) with the linear
budget p*m<=r. -/
theorem section13_residue_short_partition (r p m : Nat)
    (hp : 0 < p) (hm : 0 < m) (hsize : p * m ≤ r) :
    ∃ M : Nat, ∃ Q : Fin M → NatAP,
      0 < M ∧ IsNatAPPartition Q (Finset.range r) ∧
      ∀ j, (Q j).IsProper ∧ m ≤ (Q j).length ∧ (Q j).length < 2 * m ∧ (Q j).step = p := by
  classical
  have hpr : p ≤ r := by nlinarith
  let P := residueNatAP r p
  have hlong (a : Fin p) : m ≤ (P a).length := by
    have hprod : p * (m - 1) + p ≤ r := by
      rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hm]
      exact hsize
    have hi : (a : Nat) + (m - 1) * p < r := by nlinarith [a.isLt]
    have h := (residueNatAP_index_lt hp hpr a (m - 1)).mpr hi
    change m ≤ (residueNatAP r p a).length
    omega
  let L := fun a : Fin p => (P a).length / m
  let R := fun a : Fin p => shortParentChunk (P a).length m
  let T := fun (a : Fin p) (i : Fin (L a)) => section5NatTransport (P a) (R a i)
  have hPproper (a : Fin p) : (P a).IsProper := residueNatAP_proper hp a
  have hRpart (a : Fin p) : IsNatAPPartition (R a) (Finset.range (P a).length) :=
    shortParentChunk_partition hm (hlong a)
  have hTpart (a : Fin p) : IsNatAPPartition (T a) (P a).carrier :=
    section5NatTransport_partition (P a) (R a) (hPproper a) (hRpart a)
  have hsum : 0 < ∑ a, L a := by
    let a : Fin p := ⟨0, hp⟩
    exact (Nat.div_pos (hlong a) hm).trans_le
      (Finset.single_le_sum (f := L) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a))
  refine ⟨∑ a, L a, section5NatFlatten L T, hsum,
    section5NatFlatten_partition P _ L T (residueNatAP_partition hp hpr) hTpart, ?_⟩
  intro j
  let z := (section5NatFlattenEquiv L).symm j
  refine ⟨section5NatTransport_isProper (P z.1) (R z.1 z.2)
    (hPproper z.1) (shortParentChunk_isProper _ _ z.2),
    (shortParentChunk_bounds hm z.2).1, (shortParentChunk_bounds hm z.2).2, ?_⟩
  change (R z.1 z.2).step * (P z.1).step = p
  simp [R, P, shortParentChunk, residueNatAP]

end LeanProofs.GowersSzemeredi
