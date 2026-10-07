import OAI.Combinatorics.Progressions.Estimates.FreeWeightedModelBounds

namespace OAI

section

namespace Erdos3.FreeWeightedNilpotentLieAlgebra

open Module

variable (X : Type*) [Fintype X] (s : ℕ) (w : X → ℕ)

abbrev RankAlphabet := Σ i : Fin (s + 1), layerGenerators X s w (i.val + 1)

def rankAlphabetWeight (a : RankAlphabet X s w) : ℕ := a.1.val + 1

noncomputable def rankAlphabetVector (a : RankAlphabet X s w) : FreeWeightedNilpotentLieAlgebra X s w := a.2.val

theorem rankAlphabetWeight_pos (a : RankAlphabet X s w) : 0 < rankAlphabetWeight X s w a := Nat.succ_pos _

theorem rankAlphabetVector_mem (hw : ∀ x, 0 < w x) (a : RankAlphabet X s w) :
    rankAlphabetVector X s w a ∈ (filtration X s w hw).layer (rankAlphabetWeight X s w a) :=
  layerGenerators_mem X s w hw _ a.2.val a.2.property

theorem rankAlphabet_card_le : Fintype.card (RankAlphabet X s w) ≤
    (s + 1) * (Fintype.card X + 2) ^ (3 ^ s) := by
  classical
  simp only [RankAlphabet, Fintype.card_sigma, Fintype.card_coe]
  calc
    _ ≤ ∑ _i : Fin (s + 1), (Fintype.card X + 2) ^ (3 ^ s) :=
      Finset.sum_le_sum (fun i _ => layerGenerators_card_le X s w (i.val + 1))
    _ = _ := by simp

theorem rankAlphabet_spans_layer (hw : ∀ x, 0 < w x) (d : ℕ) (hd : 0 < d) :
    (filtration X s w hw).layer d ≤ Submodule.span ℚ
      (rankAlphabetVector X s w '' {a | rankAlphabetWeight X s w a = d}) := by
  by_cases hds : d ≤ s + 1
  · let j : Fin (s + 1) := ⟨d - 1, by omega⟩
    have hj : j.val + 1 = d := by dsimp only [j]; omega
    rw [layer_eq_span]
    apply Submodule.span_mono
    intro x hx
    have hx' : x ∈ layerGenerators X s w (j.val + 1) := by simpa only [hj, Finset.mem_coe] using hx
    exact ⟨⟨j, ⟨x, hx'⟩⟩, hj, rfl⟩
  · have hbot : (filtration X s w hw).layer d = ⊥ := by
      apply bot_unique
      exact ((filtration X s w hw).antitone (by omega : s + 1 ≤ d)).trans
        (filtration X s w hw).terminal.le
    rw [hbot]
    exact bot_le

noncomputable def topRankGenerators (k : ℕ) : Finset (FreeWeightedNilpotentLieAlgebra X s w) :=
  finiteWeightedLieValues (rankAlphabetVector X s w) (rankAlphabetWeight X s w) s k

theorem topRankGenerators_span (hw : ∀ x, 0 < w x) (k : ℕ) :
    Submodule.span ℚ (topRankGenerators X s w k : Set _) = (filtration X s w hw).rankLayer s k := by
  rw [(filtration X s w hw).rankLayer_eq_weighted_tree_span
    (rankAlphabetVector X s w) (rankAlphabetWeight X s w) (rankAlphabetWeight_pos X s w)
    (rankAlphabetVector_mem X s w hw) (rankAlphabet_spans_layer X s w hw)]
  rw [(filtration X s w hw).terminal, bot_sup_eq,
    weightedLieTreeSpan_eq_finite_span _ _ (rankAlphabetWeight_pos X s w)]
  rfl

theorem topRankGenerators_card_le (k : ℕ) :
    (topRankGenerators X s w k).card ≤
      ((s + 1) * (Fintype.card X + 2) ^ (3 ^ s) + 2) ^ (3 ^ s) :=
  (finiteWeightedLieValues_card_le (rankAlphabetVector X s w) (rankAlphabetWeight X s w) s k).trans
    (Nat.pow_le_pow_left (Nat.add_le_add_right (rankAlphabet_card_le X s w) 2) _)

theorem topRankGenerators_logHeight {ι : Type*} [Fintype ι]
    (e : Basis ι ℚ (FreeWeightedNilpotentLieAlgebra X s w)) {p : ℝ}
    (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hc : ∀ i j k, rationalLogHeight (lieStructureConstants e i j k) ≤ p)
    (hgen : ∀ x ∈ FreeNilpotentLieAlgebra.treeGenerators X s, ∀ i,
      rationalLogHeight (e.repr (mk X s w x) i) ≤ p)
    (k : ℕ) (x : FreeWeightedNilpotentLieAlgebra X s w) (hx : x ∈ topRankGenerators X s w k) (i : ι) :
    rationalLogHeight (e.repr x i) ≤ (p + 3) ^ (6 * s + 2) := by
  classical
  have hv (a : RankAlphabet X s w) (j : ι) :
      rationalLogHeight (e.repr (rankAlphabetVector X s w a) j) ≤ p := by
    obtain ⟨y, hy, hya⟩ := Finset.mem_image.mp a.2.property
    change rationalLogHeight (e.repr a.2.val j) ≤ p
    rw [← hya]
    exact hgen y (FreeNilpotentLieAlgebra.weightedLayerGenerators_subset X s w _ hy) j
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  have hraw := finiteLieTrees_coordinate_height e (rankAlphabetVector X s w)
    (fun i j k => rationalHeightLE_ceil_exp (hc i j k))
    (fun a j => rationalHeightLE_ceil_exp (hv a j)) s a (Finset.mem_filter.mp ha).1 i
  apply rationalLogHeight_le_of_height hraw
  simpa only [show p + 1 + 2 = p + 3 by ring] using
    lieTreeHeight_le_exp (Fintype.card ι) ⌈Real.exp p⌉₊ s
      (hp.trans (le_add_of_nonneg_right zero_le_one))
      (hd.trans (le_add_of_nonneg_right zero_le_one)) (ceil_exp_le_exp_add_one hp)

end Erdos3.FreeWeightedNilpotentLieAlgebra

end

end OAI
