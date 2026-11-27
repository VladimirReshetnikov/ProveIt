import Lib.Base

/-!
# The index of a product of subgroups is the product of the indices

One lemma of group theory, `New.Seesaw.index_pi_univ`: in a finite product of groups, the index of a
product of subgroups is the product of their indices (an infinite index is read as `0`).

## Relation to the literature

Known result: the index of a product of subgroups in a finite product of groups is the product of
the indices. Mathlib's `Subgroup.index_pi` is the case where all the factors are the same group.
-/

/-- In a finite product of groups `G i`, the index of the product `∏ i, H i` of subgroups
`H i ≤ G i` is the product of the indices of the `H i`. An infinite index is read as `0`. -/
lemma New.Seesaw.index_pi_univ {I : Type*} {G : I → Type*} [Fintype I] [∀ i : I, Group (G i)]
    (H : ∀ i : I, Subgroup (G i)) :
    (Subgroup.pi Set.univ H).index = ∏ i : I, (H i).index := by
  -- The cosets of a product subgroup are the tuples of cosets.
  have cosets : (∀ i : I, G i ⧸ H i) ≃ (∀ i : I, G i) ⧸ Subgroup.pi Set.univ H :=
    (Setoid.piQuotientEquiv fun i : I ↦ QuotientGroup.leftRel (H i)).trans
      (Quotient.congrRight fun x y ↦ by rw [QuotientGroup.leftRel_pi H])
  simp only [Subgroup.index_eq_card]
  rw [← Nat.card_congr cosets, Nat.card_pi]
