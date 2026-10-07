import OAI.Combinatorics.Progressions.Linear.AllocatedModularRankCongruenceOutput

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

def enlargedPreparedRankSpatialEmbedding (m Jalloc J : ℕ) (hJ : J ≤ Jalloc) :
    Fin J ↪ EnlargedPreparedCommonKernel m Jalloc :=
  (Fin.castLEEmb (hJ.trans (by nlinarith : Jalloc ≤ (m + 1) * Jalloc))).trans
    (Fin.natAddEmb ((m + 1) * (m + 3)))

def enlargedPreparedRankKernelEmbedding (m Jalloc J : ℕ) (hJ : J ≤ Jalloc) (j : Fin m) :
    Fin J × Fin (j.val + 1) ↪ EnlargedPreparedCommonKernel m Jalloc :=
  (finProdFinEquiv.toEmbedding.trans (Fin.castLEEmb (by
    calc
      J * (j.val + 1) ≤ Jalloc * (m + 1) := Nat.mul_le_mul hJ (by omega)
      _ = (m + 1) * Jalloc := Nat.mul_comm _ _))).trans
    (Fin.natAddEmb ((m + 1) * (m + 3)))

theorem enlargedPreparedRankSpatialEmbedding_reserved (m Jalloc J : ℕ)
    (hJ : J ≤ Jalloc) (l : Fin J) :
    (m + 1) * (m + 3) ≤ (enlargedPreparedRankSpatialEmbedding m Jalloc J hJ l).val := by
  change (m + 1) * (m + 3) ≤ (m + 1) * (m + 3) + l.val
  exact Nat.le_add_right _ _

theorem enlargedPreparedRankKernelEmbedding_reserved (m Jalloc J : ℕ)
    (hJ : J ≤ Jalloc) (j : Fin m) (l : Fin J × Fin (j.val + 1)) :
    (m + 1) * (m + 3) ≤ (enlargedPreparedRankKernelEmbedding m Jalloc J hJ j l).val := by
  change (m + 1) * (m + 3) ≤ (m + 1) * (m + 3) + (finProdFinEquiv l).val
  exact Nat.le_add_right _ _

variable {X₀ J₀ : Type} {m : ℕ} (L : RankPreparationFamily X₀ J₀ m)

noncomputable def enlargedPreparedRankPrincipalEmbedding (Jalloc J : ℕ) (hJ : J ≤ Jalloc)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :
    Fin J ↪ EnlargedPreparedCommonSamplerBlock L Jalloc a :=
  (Fin.castLEEmb hJ).trans (Fin.natAddEmb (preparedCommonBlockCount m a.1))

theorem enlargedPreparedRankPrincipalEmbedding_reserved (Jalloc J : ℕ) (hJ : J ≤ Jalloc)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) (l : Fin J) :
    preparedCommonBlockCount m a.1 ≤ (enlargedPreparedRankPrincipalEmbedding L Jalloc J hJ a l).val := by
  change preparedCommonBlockCount m a.1 ≤ preparedCommonBlockCount m a.1 + l.val
  exact Nat.le_add_right _ _

theorem enlargedPreparedRank_embeddings (Jalloc J : ℕ) (hJ : J ≤ Jalloc)
    (inactive : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L) → Prop)
    (j : Fin m) :
    ∃ _spatial : Fin J ↪ EnlargedPreparedCommonKernel m Jalloc,
      ∃ _kernel : Fin J × Fin (j.val + 1) ↪ EnlargedPreparedCommonKernel m Jalloc,
        Nonempty (∀ a : AllocatedDegreeActiveAxis inactive j,
          Fin J ↪ EnlargedPreparedCommonSamplerBlock L Jalloc ⟨j, a.val⟩) :=
  ⟨enlargedPreparedRankSpatialEmbedding m Jalloc J hJ,
    enlargedPreparedRankKernelEmbedding m Jalloc J hJ j,
    ⟨fun a => enlargedPreparedRankPrincipalEmbedding L Jalloc J hJ ⟨j, a.val⟩⟩⟩

variable {E : Fin m → Type*}

noncomputable def enlargedPreparedTaggedRankBlock (Jalloc J : ℕ) (hJ : J ≤ Jalloc)
    (inactive : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L) → Prop)
    (j : Fin m) :
    AllocatedTaggedRankOutput X₀ E inactive j → Fin J →
      Finset (LayerSamplerLongVariables inactive (EnlargedPreparedCommonKernel m Jalloc)
        (EnlargedPreparedCommonSamplerBlock L Jalloc)) :=
  allocatedTaggedRankBlock inactive j
    (enlargedPreparedRankSpatialEmbedding m Jalloc J hJ)
    (enlargedPreparedRankKernelEmbedding m Jalloc J hJ j)
    (fun a => enlargedPreparedRankPrincipalEmbedding L Jalloc J hJ ⟨j, a.val⟩)

theorem enlargedPreparedTaggedRankBlock_card (Jalloc J : ℕ) (hJ : J ≤ Jalloc)
    (inactive : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L) → Prop)
    (j : Fin m) (o : AllocatedTaggedRankOutput X₀ E inactive j) (l : Fin J) :
    (enlargedPreparedTaggedRankBlock L Jalloc J hJ inactive j o l).card = j.val + 1 :=
  allocatedTaggedRankBlock_card _ _ _ _ _ _ _

theorem enlargedPreparedTaggedRankBlock_disjoint (Jalloc J : ℕ) (hJ : J ≤ Jalloc)
    (inactive : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L) → Prop)
    (j : Fin m) (o : AllocatedTaggedRankOutput X₀ E inactive j) :
    Pairwise (fun l q => Disjoint (enlargedPreparedTaggedRankBlock L Jalloc J hJ inactive j o l)
      (enlargedPreparedTaggedRankBlock L Jalloc J hJ inactive j o q)) :=
  allocatedTaggedRankBlock_disjoint _ _ _ _ _ _

noncomputable def enlargedPreparedTaggedRankSelected (Jalloc J : ℕ) (hJ : J ≤ Jalloc)
    (inactive : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L) → Prop)
    (j : Fin m) :
    AllocatedTaggedRankOutput X₀ E inactive j → Fin J →
      LayerSamplerLongVariables inactive (EnlargedPreparedCommonKernel m Jalloc)
        (EnlargedPreparedCommonSamplerBlock L Jalloc) :=
  allocatedTaggedRankSelected inactive j
    (enlargedPreparedRankSpatialEmbedding m Jalloc J hJ)
    (enlargedPreparedRankKernelEmbedding m Jalloc J hJ j)
    (fun a => enlargedPreparedRankPrincipalEmbedding L Jalloc J hJ ⟨j, a.val⟩)

theorem enlargedPreparedTaggedRankSelected_mem (Jalloc J : ℕ) (hJ : J ≤ Jalloc)
    (inactive : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L) → Prop)
    (j : Fin m) (o : AllocatedTaggedRankOutput X₀ E inactive j) (l : Fin J) :
    enlargedPreparedTaggedRankSelected L Jalloc J hJ inactive j o l ∈
      enlargedPreparedTaggedRankBlock L Jalloc J hJ inactive j o l :=
  allocatedTaggedRankSelected_mem _ _ _ _ _ _ _

end Erdos3.VectorPolynomial

end

end OAI
