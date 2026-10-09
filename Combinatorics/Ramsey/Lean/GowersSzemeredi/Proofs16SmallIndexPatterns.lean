import GowersSzemeredi.Proofs16SmallCoverIndices

/-! Count index sets of size at most ell without padding them by indices
whose maps may be undefined on the relevant row. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def smallIndexSets (m ell : Nat) : Finset (Finset (Fin m)) :=
  Finset.univ.powerset.filter fun J => J.card ≤ ell

@[simp] theorem mem_smallIndexSets {m ell : Nat} {J : Finset (Fin m)} :
    J ∈ smallIndexSets m ell ↔ J.card ≤ ell := by
  simp [smallIndexSets]

/-- Variable-size index patterns have at most (m+1)^ell possibilities. -/
theorem smallIndexSets_card_le (m ell : Nat) :
    (smallIndexSets m ell).card ≤ (m + 1)^ell := by
  classical
  induction ell with
  | zero =>
    have hz : smallIndexSets m 0 = {∅} := by ext J; simp
    simp [hz]
  | succ ell ih =>
    let expand : Option (Fin m) × Finset (Fin m) → Finset (Fin m) :=
      fun p => p.1.elim p.2 (fun i => insert i p.2)
    have hsub : smallIndexSets m (ell + 1) ⊆
        (Finset.univ ×ˢ smallIndexSets m ell).image expand := by
      intro J hJ
      have hcard := mem_smallIndexSets.mp hJ
      by_cases hne : J.Nonempty
      · obtain ⟨i, hi⟩ := hne
        refine Finset.mem_image.mpr ⟨(some i, J.erase i), ?_, ?_⟩
        · apply Finset.mem_product.mpr
          refine ⟨Finset.mem_univ _, mem_smallIndexSets.mpr ?_⟩
          rw [Finset.card_erase_of_mem hi]
          omega
        · simpa [expand] using Finset.insert_erase hi
      · have hzero : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        subst J
        exact Finset.mem_image.mpr ⟨(none, ∅),
          Finset.mem_product.mpr ⟨Finset.mem_univ _, by simp⟩, rfl⟩
    calc (smallIndexSets m (ell + 1)).card
        ≤ ((Finset.univ ×ˢ smallIndexSets m ell).image expand).card := Finset.card_le_card hsub
      _ ≤ (Finset.univ ×ˢ smallIndexSets m ell).card := Finset.card_image_le
      _ = (m + 1) * (smallIndexSets m ell).card := by simp
      _ ≤ (m + 1) * (m + 1)^ell := Nat.mul_le_mul_left _ ih
      _ = (m + 1)^(ell + 1) := by rw [pow_succ, Nat.mul_comm]

end LeanProofs.GowersSzemeredi
