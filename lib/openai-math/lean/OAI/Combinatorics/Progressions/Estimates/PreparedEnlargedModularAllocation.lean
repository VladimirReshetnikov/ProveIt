import OAI.Combinatorics.Progressions.Linear.AllocatedModularRankPreparedBlocks
import OAI.Combinatorics.Progressions.Linear.AllocatedModularRankSmoothWidthBudget
import OAI.Combinatorics.Progressions.Linear.PreparedDeckRankCardinality
import OAI.Combinatorics.Progressions.Linear.PreparedSpatialKernelBlocks

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {X₀ J₀ : Type} {m : ℕ} (prep : RankPreparationFamily X₀ J₀ m)

def preparedInitialRankSpatialEmbedding (nX M : ℕ) :
    Fin (modularInitialBlockCount m (nX + m * M)) ↪
      EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)) :=
  enlargedPreparedRankSpatialEmbedding m _ _ le_rfl

def preparedInitialRankKernelEmbedding (nX M : ℕ) (j : Fin m) :
    Fin (modularInitialBlockCount m (nX + m * M)) × Fin (j.val + 1) ↪
      EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)) :=
  enlargedPreparedRankKernelEmbedding m _ _ le_rfl j

noncomputable def preparedInitialRankPrincipalEmbedding (nX M : ℕ)
    (inactive : LayerSamplerAxis (PreparedSamplerContinuous prep)
      (preparedSamplerTransverse prep) → Prop)
    (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j) :
    Fin (modularInitialBlockCount m (nX + m * M)) ↪
      EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))
        ⟨j, a.val⟩ :=
  enlargedPreparedRankPrincipalEmbedding prep _ _ le_rfl ⟨j, a.val⟩

section Dimension

variable {J E : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

include U o bW

theorem preparedInitialRank_layer_card (j : Fin m) :
    Fintype.card (E j) + preparedSamplerTransverse prep j = Fintype.card (prep j).Coord := by
  rw [preparedDeckBasis_card_eq (U j) (o j) (bW j)]
  exact preparedSampler_axis_card prep j

theorem preparedInitialRank_dimension_le (nX M : ℕ)
    (hM : ∀ j, Fintype.card (prep j).Coord ≤ M) :
    Fintype.card (Fin nX) +
        ∑ j : Fin m, (Fintype.card (E j) + preparedSamplerTransverse prep j) ≤ nX + m * M := by
  simp only [Fintype.card_fin]
  apply Nat.add_le_add_left
  calc
    _ = ∑ j : Fin m, Fintype.card (prep j).Coord :=
      Finset.sum_congr rfl (fun j _ => preparedInitialRank_layer_card prep U o bW j)
    _ ≤ ∑ _j : Fin m, M := Finset.sum_le_sum (fun j _ => hM j)
    _ = m * M := by simp

theorem preparedInitialRank_output_dimension_le (nX M : ℕ)
    (hM : ∀ j, Fintype.card (prep j).Coord ≤ M) (hm : 0 < m)
    (inactive : LayerSamplerAxis (PreparedSamplerContinuous prep)
      (preparedSamplerTransverse prep) → Prop) :
    (∑ j : Fin m, Fintype.card (AllocatedCongruenceRankOutput (Fin nX) E inactive j)) ≤
      nX + m * M :=
  (allocatedCongruenceRankOutput_sum_card_le hm inactive).trans
    (preparedInitialRank_dimension_le prep U o bW nX M hM)

theorem preparedInitialRank_parameters (nX M : ℕ)
    (hM : ∀ j, Fintype.card (prep j).Coord ≤ M) (hm : 0 < m) :
    0 ≤ (modularInitialRankStrength m (nX + m * M) : ℝ) ∧
    (Fintype.card (Fin nX) +
      ∑ j : Fin m, (Fintype.card (E j) + preparedSamplerTransverse prep j) ≤ nX + m * M) ∧
    ⌈2 * ((modularInitialRankStrength m (nX + m * M) : ℝ) + (nX + m * M : ℕ) + 10) /
      modularRankSmallBallExponent m⌉₊ ≤ modularInitialBlockCount m (nX + m * M) :=
  ⟨Nat.cast_nonneg _, preparedInitialRank_dimension_le prep U o bW nX M hM,
    modularInitialBlockCount_threshold hm _⟩

end Dimension

theorem preparedInitialRank_smooth_card_le (nX M : ℕ)
    (hM : ∀ j, Fintype.card (prep j).Coord ≤ M) (hm : 0 < m)
    (inactive : LayerSamplerAxis (PreparedSamplerContinuous prep)
      (preparedSamplerTransverse prep) → Prop) :
    Fintype.card (AllocatedSmoothRankCoefficientIndex (Fin nX) inactive
      (modularInitialBlockCount m (nX + m * M))) ≤
        modularInitialBlockCount m (nX + m * M) * (nX + m * M) := by
  apply (allocatedSmoothRankCoefficientIndex_card_le hm inactive).trans
  apply Nat.mul_le_mul_left
  simp only [Fintype.card_fin]
  apply Nat.add_le_add_left
  calc
    ∑ j : Fin m, preparedSamplerTransverse prep j ≤ ∑ _j : Fin m, M := by
      apply Finset.sum_le_sum
      intro j _
      have h := preparedSampler_axis_card prep j
      have := hM j
      omega
    _ = m * M := by simp

end Erdos3.VectorPolynomial

end

end OAI
