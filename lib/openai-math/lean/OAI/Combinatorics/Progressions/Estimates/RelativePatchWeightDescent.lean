import OAI.Combinatorics.Progressions.Linear.VaryingRankFixedPatchFunction
import OAI.Combinatorics.Progressions.Polynomial.LowestPolynomialLayer

namespace OAI

section

namespace Erdos3

theorem exists_monotone_lowest_weight_prefix {d : ℕ} (w : Fin d → ℕ)
    (hmono : Monotone w) (hd : 0 < d) :
    ∃ D : ℕ, 0 < D ∧ D ≤ d ∧
      (∀ i : Fin d, i.val < D → w i = w ⟨0, hd⟩) ∧
      (∀ i : Fin d, D ≤ i.val → w ⟨0, hd⟩ < w i) := by
  classical
  let above := fun D : ℕ => D ≤ d ∧ ∀ i : Fin d, D ≤ i.val → w ⟨0, hd⟩ < w i
  have hex : ∃ D, above D := ⟨d, le_rfl, fun i hi => False.elim (by omega)⟩
  let D := Nat.find hex
  have hD : above D := Nat.find_spec hex
  have hpos : 0 < D := by
    by_contra hn
    have hzero : D = 0 := by omega
    have hh := hD.2 ⟨0, hd⟩ (by omega)
    exact (lt_irrefl _) hh
  refine ⟨D, hpos, hD.1, ?_, hD.2⟩
  intro i hi
  apply le_antisymm
  · by_contra hn
    have hstrict : w ⟨0, hd⟩ < w i := by omega
    have hcut : above i.val := ⟨i.isLt.le, fun k hk =>
      hstrict.trans_le (hmono (show i ≤ k from hk))⟩
    have hminimal : D ≤ i.val := Nat.find_min' hex hcut
    omega
  · exact hmono (show (⟨0, hd⟩ : Fin d) ≤ i from Nat.zero_le _)

namespace PolynomialPatch

theorem castRank_weight_apply {X : Type*} {s d e : ℕ}
    (A : PolynomialPatch X s d) (h : d = e) (i : Fin e) :
    (A.castRank h).weight i = A.weight (i.cast h.symm) := by
  subst e
  rfl

theorem exists_lowestLayer_prefix {X : Type*} {s d : ℕ}
    (A : PolynomialPatch X s d) (hd : 0 < d) :
    ∃ (D j : ℕ) (hD : D ≤ d), 0 < D ∧ 1 ≤ j ∧ j ≤ s ∧
      (∀ i : Fin D,
        (A.castRank (Nat.add_sub_of_le hD).symm).weight (i.castAdd (d - D)) = j) ∧
      (∀ i : Fin (d - D),
        j < (A.castRank (Nat.add_sub_of_le hD).symm).weight (i.natAdd D)) ∧
      Nonempty ((A.castRank (Nat.add_sub_of_le hD).symm).LowestLayerModel (D := D) (E := d - D) j) := by
  obtain ⟨D, hDpos, hD, hfirst, hrest⟩ :=
    exists_monotone_lowest_weight_prefix A.weight A.weight_mono hd
  have hprefix (i : Fin D) :
      (A.castRank (Nat.add_sub_of_le hD).symm).weight (i.castAdd (d - D)) = A.weight ⟨0, hd⟩ := by
    rw [castRank_weight_apply]
    exact hfirst _ i.isLt
  refine ⟨D, A.weight ⟨0, hd⟩, hD, hDpos, A.weight_pos _, A.weight_le _, hprefix, ?_, ?_⟩
  · intro i
    rw [castRank_weight_apply]
    exact hrest _ (Nat.le_add_right D i.val)
  · exact nonempty_lowestLayerModel _ (Nat.zero_lt_of_lt (A.weight_pos _)) hprefix

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3
open scoped Classical

theorem relativePatchDistinctWeights_tail {X Y : Type*} {s D E j : ℕ}
    (A : PolynomialPatch X s (D + E)) (B : PolynomialPatch Y s E)
    (hD : 0 < D)
    (hfirst : ∀ i : Fin D, A.weight (i.castAdd E) = j)
    (hrest : ∀ i : Fin E, j < A.weight (i.natAdd D))
    (hB : ∀ i, B.weight i = A.weight (i.natAdd D)) :
    relativePatchDistinctWeights B + 1 = relativePatchDistinctWeights A := by
  have hnot : j ∉ Finset.univ.image B.weight := by
    rintro hj
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hj
    have h := hrest i
    rw [← hB i, hi] at h
    exact (lt_irrefl j) h
  have himage : Finset.univ.image A.weight = insert j (Finset.univ.image B.weight) := by
    ext k
    constructor
    · intro hk
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hk
      cases i using Fin.addCases with
      | left i => exact Finset.mem_insert.mpr (Or.inl (hfirst i))
      | right i =>
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr
          ⟨i, Finset.mem_univ _, hB i⟩))
    · intro hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact Finset.mem_image.mpr ⟨(⟨0,hD⟩ : Fin D).castAdd E, Finset.mem_univ _, hfirst _⟩
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hk
        exact Finset.mem_image.mpr ⟨i.natAdd D, Finset.mem_univ _, (hB i).symm⟩
  unfold relativePatchDistinctWeights
  rw [himage, Finset.card_insert_of_notMem hnot]

@[simp] theorem relativePatchDistinctWeights_castRank {X : Type*} {s d e : ℕ}
    (A : PolynomialPatch X s d) (h : d = e) :
    relativePatchDistinctWeights (A.castRank h) = relativePatchDistinctWeights A := by
  subst e
  rfl

@[simp] theorem relativePatchDistinctWeights_coordinateFiber {X : Type*}
    [Fintype X] [DecidableEq X] {s d : ℕ} (A : PolynomialPatch X s d)
    (keep : X → Prop) (fixed : {i // ¬keep i} → ℤ) :
    relativePatchDistinctWeights (A.coordinateFiber keep fixed) = relativePatchDistinctWeights A := rfl

@[simp] theorem relativePatchComplexity_coordinateFiber {X : Type*}
    [Fintype X] [DecidableEq X] {s d : ℕ} (A : PolynomialPatch X s d)
    (keep : X → Prop) (fixed : {i // ¬keep i} → ℤ) :
    relativePatchComplexity (A.coordinateFiber keep fixed) = relativePatchComplexity A := rfl

theorem relativePatchDistinctWeights_tail_le {X Y : Type*} {s D E j stage : ℕ}
    (A : PolynomialPatch X s (D + E)) (B : PolynomialPatch Y s E)
    (hD : 0 < D)
    (hfirst : ∀ i : Fin D, A.weight (i.castAdd E) = j)
    (hrest : ∀ i : Fin E, j < A.weight (i.natAdd D))
    (hB : ∀ i, B.weight i = A.weight (i.natAdd D))
    (hstage : relativePatchDistinctWeights A ≤ stage + 1) :
    relativePatchDistinctWeights B ≤ stage := by
  have h := relativePatchDistinctWeights_tail A B hD hfirst hrest hB
  omega

end Erdos3

end

end OAI
