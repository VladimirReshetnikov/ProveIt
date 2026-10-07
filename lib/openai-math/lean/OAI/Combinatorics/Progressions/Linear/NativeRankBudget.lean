import OAI.Combinatorics.Progressions.Estimates.RationalPowerHeight

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

abbrev RankAlphabet := Σ i : Fin (s + 1), Fin (finrank ℚ (D.filtration.layer (i.val + 1)))

def rankAlphabetWeight (a : D.RankAlphabet) : ℕ := a.1.val + 1

noncomputable def rankAlphabetVector (a : D.RankAlphabet) : L := D.layerBasis a.1 a.2

theorem rankAlphabetWeight_pos (a : D.RankAlphabet) : 0 < D.rankAlphabetWeight a := Nat.succ_pos _

theorem rankAlphabetVector_mem (a : D.RankAlphabet) :
    D.rankAlphabetVector a ∈ D.filtration.layer (D.rankAlphabetWeight a) :=
  (D.layerBasis a.1 a.2).property

theorem rankAlphabet_card_le : Fintype.card D.RankAlphabet ≤ (s + 1) * d := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  simp only [RankAlphabet, Fintype.card_sigma, Fintype.card_fin]
  calc
    _ ≤ ∑ _i : Fin (s + 1), d := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using
        (D.filtration.layer (i.val + 1)).finrank_le
    _ = _ := by simp

theorem rankAlphabet_spans_layer (i : ℕ) (hi : 0 < i) :
    D.filtration.layer i ≤ Submodule.span ℚ
      (D.rankAlphabetVector '' {a | D.rankAlphabetWeight a = i}) := by
  by_cases his : i ≤ s + 1
  · let j : Fin (s + 1) := ⟨i - 1, by omega⟩
    have hj : j.val + 1 = i := by dsimp [j]; omega
    have heq : D.filtration.layer i = Submodule.span ℚ
        (Set.range (fun k => ((D.layerBasis j k : D.filtration.layer (j.val + 1)) : L))) := by
      rw [span_submodule_basis, hj]
    rw [heq]
    apply Submodule.span_mono
    rintro x ⟨k, rfl⟩
    exact ⟨⟨j, k⟩, hj, rfl⟩
  · have hbot : D.filtration.layer i = ⊥ := by
      apply bot_unique
      exact (D.filtration.antitone (show s + 1 ≤ i by omega)).trans D.filtration.terminal.le
    rw [hbot]
    exact bot_le

theorem rankAlphabet_span_layer (i : ℕ) (hi : 0 < i) :
    Submodule.span ℚ (D.rankAlphabetVector '' {a | D.rankAlphabetWeight a = i}) =
      D.filtration.layer i := by
  apply le_antisymm _ (D.rankAlphabet_spans_layer i hi)
  apply Submodule.span_le.mpr
  rintro x ⟨a, ha, rfl⟩
  exact ha ▸ D.rankAlphabetVector_mem a

noncomputable def finiteRankGenerators (i r : ℕ) : Finset L := by
  classical
  exact ((Finset.univ.filter (fun a : D.RankAlphabet => D.rankAlphabetWeight a = i + 1)).image
    D.rankAlphabetVector) ∪ finiteWeightedLieValues D.rankAlphabetVector D.rankAlphabetWeight i r

theorem finiteRankGenerators_span (i r : ℕ) :
    Submodule.span ℚ (D.finiteRankGenerators i r : Set L) = D.filtration.rankLayer i r := by
  classical
  rw [D.filtration.rankLayer_eq_weighted_tree_span D.rankAlphabetVector D.rankAlphabetWeight
    D.rankAlphabetWeight_pos D.rankAlphabetVector_mem D.rankAlphabet_spans_layer]
  rw [weightedLieTreeSpan_eq_finite_span _ _ D.rankAlphabetWeight_pos]
  have hleaf : Submodule.span ℚ
      (((Finset.univ.filter (fun a : D.RankAlphabet => D.rankAlphabetWeight a = i + 1)).image
        D.rankAlphabetVector : Finset L) : Set L) = D.filtration.layer (i + 1) := by
    simpa only [Finset.coe_image, Finset.coe_filter, Finset.mem_univ,
      true_and] using D.rankAlphabet_span_layer (i + 1) (Nat.succ_pos i)
  change Submodule.span ℚ ((_ ∪ _ : Finset L) : Set L) = _
  rw [Finset.coe_union, Submodule.span_union, hleaf]

theorem finiteRankGenerators_card_le (i r : ℕ) (hi : i ≤ s) :
    (D.finiteRankGenerators i r).card ≤
      (s + 1) * d + ((s + 1) * d + 2) ^ (3 ^ s) := by
  classical
  have hleaf : ((Finset.univ.filter
      (fun a : D.RankAlphabet => D.rankAlphabetWeight a = i + 1)).image D.rankAlphabetVector).card ≤
      Fintype.card D.RankAlphabet := by
    exact Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans_eq (Finset.card_univ))
  have htree := finiteWeightedLieValues_card_le D.rankAlphabetVector D.rankAlphabetWeight i r
  have htree' : (finiteWeightedLieValues D.rankAlphabetVector D.rankAlphabetWeight i r).card ≤
      ((s + 1) * d + 2) ^ (3 ^ s) := by
    apply htree.trans
    apply (Nat.pow_le_pow_left (Nat.add_le_add_right D.rankAlphabet_card_le 2) _).trans
    exact Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) hi)
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add (hleaf.trans D.rankAlphabet_card_le) htree')

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

theorem finiteRankGenerators_height {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H)
    (hb : ∀ i j k, RationalHeightLE (D.basis.repr (D.layerBasis i j) k) H)
    (i r : ℕ) (hi : i ≤ s) (x : L) (hx : x ∈ D.finiteRankGenerators i r) (k : Fin d) :
    RationalHeightLE (D.basis.repr x k) (lieTreeHeight d H s) := by
  classical
  rcases Finset.mem_union.mp hx with h | h
  · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp h
    exact (hb a.1 a.2 k).mono (lieTreeHeight_ge_input d H s)
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
    have h := finiteLieTrees_coordinate_height D.basis D.rankAlphabetVector hc
      (fun a j => hb a.1 a.2 j) i a (Finset.mem_filter.mp ha).1 k
    simp only [Fintype.card_fin] at h
    exact h.mono (lieTreeHeight_mono d H hi)

theorem exists_rankLayer_basis_height {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H)
    (hb : ∀ i j k, RationalHeightLE (D.basis.repr (D.layerBasis i j) k) H)
    (i r : ℕ) (hi : i ≤ s) :
    ∃ b : Basis (Fin (finrank ℚ (D.filtration.rankLayer i r))) ℚ (D.filtration.rankLayer i r),
      ∀ j k, RationalHeightLE (D.basis.repr (b j : L) k) (lieTreeHeight d H s) := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ (D.finiteRankGenerators i r : Set L)
  rw [D.finiteRankGenerators_span] at hex
  obtain ⟨v, hv, hvspan, hli⟩ := hex
  refine ⟨(Basis.span hli).map (LinearEquiv.ofEq _ _ hvspan), ?_⟩
  intro j k
  simp only [Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.coe_span_apply]
  exact D.finiteRankGenerators_height hc hb i r hi (v j) (hv j) k

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem exists_canonical_rank_basis_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → ∀ i r : ℕ, i ≤ s →
      ∃ b : Basis (Fin (finrank ℚ (D.filtration.rankLayer i r))) ℚ (D.filtration.rankLayer i r),
        (finrank ℚ (D.filtration.rankLayer i r) : ℝ) ≤ p ∧
        ∀ j k, rationalLogHeight (D.basis.repr (b j : L) k) ≤ (p + C) ^ C := by
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + 3 : Polynomial ℕ) ^ (6 * s + 2))
  refine ⟨C, hC, ?_⟩
  intro L _ _ d D p hp hD i r hi
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  have hcost : (p + 3) ^ (6 * s + 2) ≤ (p + C) ^ C := by
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  have htree : (lieTreeHeight d ⌈Real.exp p⌉₊ s : ℝ) ≤ Real.exp ((p + 3) ^ (6 * s + 2)) := by
    simpa only [add_assoc, show (1 : ℝ) + 2 = 3 by norm_num] using
      lieTreeHeight_le_exp d ⌈Real.exp p⌉₊ s (p := p + 1) (by linarith)
        (hD.1.trans (by linarith)) (ceil_exp_le_exp_add_one hp)
  obtain ⟨b, hb⟩ := D.exists_rankLayer_basis_height
    (fun a b c => rationalHeightLE_ceil_exp (hD.2.2.1 a b c))
    (fun a b c => rationalHeightLE_ceil_exp (hD.2.2.2 a b c)) i r hi
  refine ⟨b, ?_, fun j k => rationalLogHeight_le_of_height (hb j k)
    (htree.trans (Real.exp_le_exp.mpr hcost))⟩
  have hdim : finrank ℚ (D.filtration.rankLayer i r) ≤ d := by
    simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using
      (D.filtration.rankLayer i r).finrank_le
  exact (Nat.cast_le.mpr hdim).trans hD.1

end Erdos3.RationalFilteredNilmanifold

end

end OAI
