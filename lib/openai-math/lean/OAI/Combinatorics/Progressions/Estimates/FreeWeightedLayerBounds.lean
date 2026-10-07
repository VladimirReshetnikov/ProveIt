import OAI.Combinatorics.Progressions.Linear.WeightedLieUpperSpan
import OAI.Combinatorics.Progressions.Nilpotent.FreeNilpotentSourceBounds

namespace OAI

section

namespace Erdos3.FreeNilpotentLieAlgebra

variable (X : Type*) (s : ℕ)

theorem mk_lieTreeEval (a : FreeMagma X) :
    mk X s (lieTreeEval (FreeLieAlgebra.of ℚ) a) = lieTreeEval (of X s) a :=
  map_lieTreeEval (mk X s) (FreeLieAlgebra.of ℚ) a

noncomputable def weightedLayer (w : X → ℕ) (d : ℕ) : Submodule ℚ (FreeNilpotentLieAlgebra X s) :=
  weightedLieUpperSpan (of X s) w d

theorem weightedLayer_antitone (w : X → ℕ) : Antitone (weightedLayer X s w) :=
  weightedLieUpperSpan_antitone (of X s) w

theorem weightedLayer_lie_mem (w : X → ℕ) {d e : ℕ} {x y : FreeNilpotentLieAlgebra X s}
    (hx : x ∈ weightedLayer X s w d) (hy : y ∈ weightedLayer X s w e) :
    ⁅x, y⁆ ∈ weightedLayer X s w (d + e) :=
  weightedLieUpperSpan_lie_mem (of X s) w hx hy

theorem weightedLayer_eq_top (w : X → ℕ) (d : ℕ) (hd : ∀ a : FreeMagma X, d ≤ lieTreeWeight w a) :
    weightedLayer X s w d = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨p, rfl⟩ := mk_surjective X s x
  apply freeLie_linear_induction (fun p => mk X s p ∈ weightedLayer X s w d)
  · simpa only [map_zero] using (weightedLayer X s w d).zero_mem
  · intro p q hp hq
    rw [map_add]
    exact (weightedLayer X s w d).add_mem hp hq
  · intro c p hp
    rw [map_smul]
    exact (weightedLayer X s w d).smul_mem c hp
  · intro a
    rw [mk_lieTreeEval]
    exact Submodule.subset_span ⟨a, hd a, rfl⟩

theorem weightedLayer_zero (w : X → ℕ) : weightedLayer X s w 0 = ⊤ :=
  weightedLayer_eq_top X s w 0 (fun _ => Nat.zero_le _)

theorem weightedLayer_one (w : X → ℕ) (hw : ∀ i, 0 < w i) : weightedLayer X s w 1 = ⊤ :=
  weightedLayer_eq_top X s w 1 (fun a => a.length_pos.trans_le (lieTree_length_le_weight w hw a))

noncomputable def weightedLayerIdeal (w : X → ℕ) (d : ℕ) : LieIdeal ℚ (FreeNilpotentLieAlgebra X s) :=
  { weightedLayer X s w d with
    lie_mem := by
      intro x y hy
      have hx : x ∈ weightedLayer X s w 0 := by rw [weightedLayer_zero]; exact Submodule.mem_top
      change ⁅x, y⁆ ∈ weightedLayer X s w d
      simpa only [Nat.zero_add] using weightedLayer_lie_mem X s w hx hy }

variable [Fintype X]

noncomputable def weightedLayerGenerators (w : X → ℕ) (d : ℕ) : Finset (FreeNilpotentLieAlgebra X s) := by
  classical
  exact ((finiteLieTrees X s).filter (fun a => a.length ≤ s ∧ d ≤ lieTreeWeight w a)).image
    (fun a => mk X s (lieTreeEval (FreeLieAlgebra.of ℚ) a))

theorem weightedLayer_eq_span (w : X → ℕ) (d : ℕ) :
    weightedLayer X s w d = Submodule.span ℚ (weightedLayerGenerators X s w d : Set _) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨a, ha, rfl⟩
    by_cases hlen : a.length ≤ s
    · apply Submodule.subset_span
      exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr
        ⟨mem_finiteLieTrees_of_length_le X a hlen, hlen, ha⟩, mk_lieTreeEval X s a⟩
    · rw [← mk_lieTreeEval, mk_tree_eq_zero_of_length_gt X s a (Nat.lt_of_not_ge hlen)]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact Submodule.subset_span ⟨a, (Finset.mem_filter.mp ha).2.2, (mk_lieTreeEval X s a).symm⟩

theorem weightedLayerGenerators_subset (w : X → ℕ) (d : ℕ) :
    weightedLayerGenerators X s w d ⊆ treeGenerators X s := by
  classical
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2.1⟩, rfl⟩

theorem weightedLayerGenerators_card_le (w : X → ℕ) (d : ℕ) :
    (weightedLayerGenerators X s w d).card ≤ (Fintype.card X + 2) ^ (3 ^ s) :=
  (Finset.card_le_card (weightedLayerGenerators_subset X s w d)).trans (treeGenerators_card_le X s)

end Erdos3.FreeNilpotentLieAlgebra

end

section

namespace Erdos3.FreeNilpotentLieAlgebra

open Module
attribute [local instance] LieRing.ofAssociativeRing

variable (X : Type*) [Fintype X] (s : ℕ) (w : X → ℕ) (d : ℕ)

theorem weightedLayerGenerators_coordinate_height (x : FreeNilpotentLieAlgebra X s)
    (hx : x ∈ weightedLayerGenerators X s w d) (i : BoundedFreeWord X s) :
    RationalHeightLE (coordinates X s x i) ((2 * (s + 1)) ^ s) :=
  treeGenerators_coordinate_height X s x (weightedLayerGenerators_subset X s w d hx) i

theorem weightedLayerGenerators_basis_height
    (b : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ (FreeNilpotentLieAlgebra X s))
    (hb : ∀ j i, RationalHeightLE (coordinates X s (b j) i) ((2 * (s + 1)) ^ s))
    (x : FreeNilpotentLieAlgebra X s) (hx : x ∈ weightedLayerGenerators X s w d) (j) :
    let n := Fintype.card (BoundedFreeWord X s)
    let H := (2 * (s + 1)) ^ s
    RationalHeightLE (b.repr x j)
      ((n + 1) * (rationalSolveHeight (finrank ℚ (FreeNilpotentLieAlgebra X s)) H * H) ^ n) := by
  have h := embedding_basis_coordinate_height b (Pi.basisFun ℚ (BoundedFreeWord X s))
    (coordinates X s) (coordinates_injective X s)
    (show 1 ≤ (2 * (s + 1)) ^ s from one_le_pow₀ (by omega))
    (fun i j => by simpa only [Pi.basisFun_repr] using hb j i)
    x (fun i => by simpa only [Pi.basisFun_repr] using
      weightedLayerGenerators_coordinate_height X s w d x hx i) j
  simpa only [Fintype.card_fin] using h

end Erdos3.FreeNilpotentLieAlgebra

end

end OAI
