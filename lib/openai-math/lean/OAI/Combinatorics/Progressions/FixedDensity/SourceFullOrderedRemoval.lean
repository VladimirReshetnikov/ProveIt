import OAI.Combinatorics.Progressions.FixedDensity.OrderedFullBoundary

namespace OAI

section

namespace Erdos3.FixedDensity

def topPositiveOrderedFace
    {k n : ℕ} (e : OrderedFace k (n + 1)) :
    PositiveOrderedFace k (n + 1) where
  lowerRank := Fin.last n
  face := e

@[simp]
theorem topPositiveOrderedFace_rank
    {k n : ℕ} (e : OrderedFace k (n + 1)) :
    (topPositiveOrderedFace e).rank = n + 1 := by
  rfl

@[simp]
theorem topPositiveOrderedFace_lowerRank_succ
    {k n : ℕ} (e : OrderedFace k (n + 1)) :
    (topPositiveOrderedFace e).lowerRank.succ =
      Fin.last (n + 1) := by
  apply Fin.ext
  rfl

theorem partialConfigurationWeight_univ_eq_zero_of_not_occurrence
    {G : Type*} [Fintype G] [DecidableEq G]
    {k n : ℕ}
    (H : OrderedPattern G k (n + 1))
    {C : OrderedPartitionComplex G k (n + 1)}
    (hC : OrderedFacePartitionRefines C.topLayer
      (orderedPatternTopPartition H))
    (A : ClosedOrderedAtomConfiguration G k (n + 1) C)
    (hA : H.IsOccurrence A.witness)
    {x : Fin k → G} (hx : ¬H.IsOccurrence x) :
    partialConfigurationWeight A Finset.univ x = 0 := by
  have hmissing :
      ∃ e : OrderedFace k (n + 1),
        orderedFaceTuple e x ∉
          (A.atom (Fin.last (n + 1)) e).1 := by
    by_contra h
    push Not at h
    exact hx
      (A.isOccurrence_of_mem_topAtoms
        H hC hA x h)
  obtain ⟨e, he⟩ := hmissing
  unfold partialConfigurationWeight
  apply Finset.prod_eq_zero
    (Finset.mem_univ (topPositiveOrderedFace e))
  unfold configurationFaceWeight
  change
    partitionAtomIndicator
        (C.partition (Fin.last (n + 1)) e)
        (A.atom (Fin.last (n + 1)) e)
        (orderedFaceTuple e x) =
      0
  exact
    partitionAtomIndicator_of_not_mem
      (C.partition (Fin.last (n + 1)) e)
      (A.atom (Fin.last (n + 1)) e) he

theorem partialConfigurationWeight_univ_le_patternWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k n : ℕ}
    (H : OrderedPattern G k (n + 1))
    {C : OrderedPartitionComplex G k (n + 1)}
    (hC : OrderedFacePartitionRefines C.topLayer
      (orderedPatternTopPartition H))
    (A : ClosedOrderedAtomConfiguration G k (n + 1) C)
    (hA : H.IsOccurrence A.witness)
    (x : Fin k → G) :
    partialConfigurationWeight A Finset.univ x ≤
      H.toWeighted.patternWeight x := by
  by_cases hx : H.IsOccurrence x
  · rw [H.toWeighted_patternWeight_of_occurrence hx]
    exact partialConfigurationWeight_le_one
      A Finset.univ x
  · rw [H.toWeighted_patternWeight_of_not_occurrence hx,
      partialConfigurationWeight_univ_eq_zero_of_not_occurrence
        H hC A hA hx]

theorem fullConfigurationCount_le_patternCount
    {G : Type*} [Fintype G] [DecidableEq G]
    {k n : ℕ}
    (H : OrderedPattern G k (n + 1))
    {C : OrderedPartitionComplex G k (n + 1)}
    (hC : OrderedFacePartitionRefines C.topLayer
      (orderedPatternTopPartition H))
    (A : ClosedOrderedAtomConfiguration G k (n + 1) C)
    (hA : H.IsOccurrence A.witness) :
    fullConfigurationCount A ≤
      H.toWeighted.patternCount := by
  unfold fullConfigurationCount partialConfigurationCount
    WeightedOrderedPattern.patternCount
  exact mean_mono
    (partialConfigurationWeight_univ_le_patternWeight
      H hC A hA)

theorem orderedBadBaseDeletionFamily_isCover_of_good_count
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k n : ℕ} (hrk : n + 1 ≤ k)
    (H : OrderedPattern G k (n + 1))
    (P : OrderedCoarseFineComplex G k (n + 1))
    (hinitial :
      P.fine.Refines (orderedPatternInitialComplex H))
    (α β : ℕ → ℝ) (c : ℝ)
    (hcount : H.toWeighted.patternCount < c)
    (hgoodCount :
      ∀ A : ClosedOrderedAtomConfiguration
          G k (n + 1) P.fine,
        A.IsGood P.fine P.coarse α β →
          c ≤ fullConfigurationCount A) :
    H.IsCover
      (orderedBadBaseDeletionFamily
        P.fine P.coarse α β) := by
  intro x hx
  by_contra hsurvives
  push Not at hsurvives
  let A :
      ClosedOrderedAtomConfiguration
        G k (n + 1) P.fine :=
    ClosedOrderedAtomConfiguration.ofTuple P.fine x
  have hgood :
      A.IsGood P.fine P.coarse α β := by
    exact
      ClosedOrderedAtomConfiguration.isGood_of_avoids_topBadBaseDeletion
        hrk P.fine P.coarse x α β hsurvives
  have hcA : c ≤ fullConfigurationCount A :=
    hgoodCount A hgood
  have htop :
      OrderedFacePartitionRefines P.fine.topLayer
        (orderedPatternTopPartition H) :=
    orderedPatternTopPartition_refines_of_complex_refines_initial
      H hinitial
  have hAH :
      fullConfigurationCount A ≤
        H.toWeighted.patternCount := by
    exact fullConfigurationCount_le_patternCount
      H htop A ((H.mem_occurrenceFinset x).1 hx)
  linarith

theorem orderedBadBaseDeletionFamily_isCover
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k n : ℕ} (hrk : n + 1 ≤ k)
    (H : OrderedPattern G k (n + 1))
    (P : OrderedCoarseFineComplex G k (n + 1))
    (hinitial :
      P.fine.Refines (orderedPatternInitialComplex H))
    (α β : ℕ → ℝ)
    (ε : OrderedRegularityTolerance (n + 1))
    (hregular :
      IsFullyPreliminaryOrderedRegular P.fine ε)
    {ρ η δ : ℝ}
    (hρ : 0 ≤ ρ) (hη : 0 ≤ η) (hδ : 0 ≤ δ)
    (hα : ∀ m, ρ ≤ α m)
    (hε : ∀ j, ε j ≤ η)
    (hβ0 : ∀ m, 0 ≤ β m)
    (hβδ : ∀ m, β m ≤ δ ^ 2)
    (hcount :
      H.toWeighted.patternCount <
        ρ ^ Fintype.card
            (PositiveOrderedFace k (n + 1)) -
          (Fintype.card
              (PositiveOrderedFace k (n + 1)) : ℝ) *
            (η + δ)) :
    H.IsCover
      (orderedBadBaseDeletionFamily
        P.fine P.coarse α β) := by
  apply orderedBadBaseDeletionFamily_isCover_of_good_count
    hrk H P hinitial α β
    (ρ ^ Fintype.card
        (PositiveOrderedFace k (n + 1)) -
      (Fintype.card
          (PositiveOrderedFace k (n + 1)) : ℝ) *
        (η + δ))
    hcount
  intro A hgood
  exact fullConfigurationCount_lower_bound
    P A α β hgood ε hregular
    hρ hη hδ hα hε hβ0 hβδ

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace OrderedCoarseFineComplex

noncomputable def sourceFullAtomDefectSq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts)
    (x : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  atomBoundaryDefectSq
    (orderedBoundaryPartition
      (positiveFaceLowerLayer P.fine e) e.face)
    (orderedBoundaryPartition
      (positiveFaceLowerLayer P.coarse e) e.face)
    upper a x

theorem sourceFullAtomDefectSq_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts)
    (x : Fin (e.lowerRank.1 + 1) → G) :
    0 ≤ P.sourceFullAtomDefectSq e upper a x := by
  exact atomBoundaryDefectSq_nonneg _ _ upper a x

noncomputable def sourceFullLargeDefectBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts) (β : ℝ) :
    Finset (Fin (e.lowerRank.1 + 1) → G) :=
  largeAverageBaseSupport
    (orderedFullLowerBoundaryPartition P.coarse e)
    (P.sourceFullAtomDefectSq e upper a) β

@[simp]
theorem mem_sourceFullLargeDefectBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts) (β : ℝ)
    (x : Fin (e.lowerRank.1 + 1) → G) :
    x ∈ P.sourceFullLargeDefectBaseSupport e upper a β ↔
      β <
        conditionalMean
          (orderedFullLowerBoundaryPartition P.coarse e)
          (P.sourceFullAtomDefectSq e upper a) x := by
  exact
    mem_largeAverageBaseSupport
      (orderedFullLowerBoundaryPartition P.coarse e)
      (P.sourceFullAtomDefectSq e upper a) β x

theorem mul_mean_indicator_sourceFullLargeDefectBaseSupport_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts)
    {β : ℝ} (hβ : 0 ≤ β) :
    β * mean (finsetIndicator
        (P.sourceFullLargeDefectBaseSupport e upper a β)) ≤
      mean (P.sourceFullAtomDefectSq e upper a) := by
  exact
    mul_mean_indicator_largeAverageBaseSupport_le
      (orderedFullLowerBoundaryPartition P.coarse e)
      (P.sourceFullAtomDefectSq e upper a)
      (P.sourceFullAtomDefectSq_nonneg e upper a)
      hβ

theorem mul_mean_indicator_sourceFullLargeDefectBaseSupport_le_atomEnergy_sub
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts)
    {β : ℝ} (hβ : 0 ≤ β) :
    β * mean (finsetIndicator
        (P.sourceFullLargeDefectBaseSupport e upper a β)) ≤
      orderedAtomEnergy
          (positiveFaceLowerLayer P.fine e) e.face upper -
        orderedAtomEnergy
          (positiveFaceLowerLayer P.coarse e) e.face upper := by
  refine
    (P.mul_mean_indicator_sourceFullLargeDefectBaseSupport_le
      e upper a hβ).trans ?_
  change
    mean
        (atomBoundaryDefectSq
          (orderedBoundaryPartition
            (positiveFaceLowerLayer P.fine e) e.face)
          (orderedBoundaryPartition
            (positiveFaceLowerLayer P.coarse e) e.face)
          upper a) ≤
      partitionAtomEnergy
          (orderedBoundaryPartition
            (positiveFaceLowerLayer P.fine e) e.face) upper -
        partitionAtomEnergy
          (orderedBoundaryPartition
            (positiveFaceLowerLayer P.coarse e) e.face) upper
  exact
    mean_atomBoundaryDefectSq_le_atomEnergy_sub
      (orderedBoundaryPartition_mono
        (fun f => P.refines e.lowerRank.castSucc f) e.face)
      upper a

theorem mean_indicator_sourceFullLargeDefectBaseSupport_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts)
    {β : ℝ} (hβ : 0 < β) :
    mean (finsetIndicator
        (P.sourceFullLargeDefectBaseSupport e upper a β)) ≤
      mean (P.sourceFullAtomDefectSq e upper a) / β := by
  apply (le_div_iff₀ hβ).2
  simpa [mul_comm] using
    P.mul_mean_indicator_sourceFullLargeDefectBaseSupport_le
      e upper a hβ.le

theorem orderedAtomEnergy_sub_eq_sum_mean_sourceFullAtomDefectSq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G)) :
    orderedAtomEnergy
          (positiveFaceLowerLayer P.fine e) e.face upper -
        orderedAtomEnergy
          (positiveFaceLowerLayer P.coarse e) e.face upper =
      ∑ a : upper.parts,
        mean (P.sourceFullAtomDefectSq e upper a) := by
  rw [orderedAtomEnergy_sub_eq_sum_mean_sq
    (fine := positiveFaceLowerLayer P.fine e)
    (coarse := positiveFaceLowerLayer P.coarse e)
    (fun f => P.refines e.lowerRank.castSucc f)
    e.face upper]
  rfl

noncomputable def sourceFullAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts) (α β : ℝ) :
    Finset (Fin (e.lowerRank.1 + 1) → G) :=
  smallAverageBaseSupport
      (orderedBoundaryPartition
        (positiveFaceLowerLayer P.coarse e) e.face)
      (partitionAtomIndicator upper a) α ∪
    P.sourceFullLargeDefectBaseSupport e upper a β

@[simp]
theorem mem_sourceFullAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts) (α β : ℝ)
    (x : Fin (e.lowerRank.1 + 1) → G) :
    x ∈ P.sourceFullAtomBadBaseSupport e upper a α β ↔
      conditionalMean
          (orderedBoundaryPartition
            (positiveFaceLowerLayer P.coarse e) e.face)
          (partitionAtomIndicator upper a) x < α ∨
        β <
          conditionalMean
            (orderedFullLowerBoundaryPartition P.coarse e)
            (P.sourceFullAtomDefectSq e upper a) x := by
  rw [sourceFullAtomBadBaseSupport, Finset.mem_union,
    mem_smallAverageBaseSupport,
    P.mem_sourceFullLargeDefectBaseSupport]

theorem mean_indicator_atom_inter_sourceFullAtomBadBaseSupport_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β) :
    mean (finsetIndicator
        (a.1 ∩ P.sourceFullAtomBadBaseSupport
          e upper a α β)) ≤
      α + mean (P.sourceFullAtomDefectSq e upper a) / β := by
  calc
    mean (finsetIndicator
        (a.1 ∩ P.sourceFullAtomBadBaseSupport
          e upper a α β)) ≤
        mean (finsetIndicator
          (a.1 ∩
            smallAverageBaseSupport
              (orderedBoundaryPartition
                (positiveFaceLowerLayer P.coarse e) e.face)
              (partitionAtomIndicator upper a) α)) +
          mean (finsetIndicator
            (P.sourceFullLargeDefectBaseSupport
              e upper a β)) := by
      exact
        mean_indicator_inter_union_le_add
          a.1
          (smallAverageBaseSupport
            (orderedBoundaryPartition
              (positiveFaceLowerLayer P.coarse e) e.face)
            (partitionAtomIndicator upper a) α)
          (P.sourceFullLargeDefectBaseSupport e upper a β)
    _ ≤
        α + mean (P.sourceFullAtomDefectSq e upper a) / β :=
      add_le_add
        (mean_indicator_inter_smallAverageBaseSupport_le
          (orderedBoundaryPartition
            (positiveFaceLowerLayer P.coarse e) e.face)
          a.1 hα)
        (P.mean_indicator_sourceFullLargeDefectBaseSupport_le
          e upper a hβ)

noncomputable def sourceFullOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (α β : ℝ) :
    Finset (Fin (e.lowerRank.1 + 1) → G) := by
  classical
  exact
    (Finset.univ : Finset upper.parts).biUnion fun a =>
      a.1 ∩ P.sourceFullAtomBadBaseSupport e upper a α β

@[simp]
theorem mem_sourceFullOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (α β : ℝ) (x : Fin (e.lowerRank.1 + 1) → G) :
    x ∈ P.sourceFullOwnAtomBadBaseSupport e upper α β ↔
      x ∈ P.sourceFullAtomBadBaseSupport e upper
        (partitionAtomAt upper x) α β := by
  classical
  constructor
  · intro hx
    rw [sourceFullOwnAtomBadBaseSupport] at hx
    obtain ⟨a, _ha, hxpart⟩ :=
      Finset.mem_biUnion.mp hx
    have hxa : x ∈ a.1 :=
      (Finset.mem_inter.mp hxpart).1
    have hbad :
        x ∈ P.sourceFullAtomBadBaseSupport
          e upper a α β :=
      (Finset.mem_inter.mp hxpart).2
    have hcanonical : partitionAtomAt upper x = a :=
      (partitionAtomAt_eq_iff_mem upper x a).2 hxa
    simpa [hcanonical] using hbad
  · intro hbad
    rw [sourceFullOwnAtomBadBaseSupport]
    apply Finset.mem_biUnion.mpr
    refine ⟨partitionAtomAt upper x, Finset.mem_univ _, ?_⟩
    exact Finset.mem_inter.mpr
      ⟨upper.mem_part (Finset.mem_univ x), hbad⟩

theorem mean_indicator_sourceFullOwnAtomBadBaseSupport_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β) :
    mean (finsetIndicator
        (P.sourceFullOwnAtomBadBaseSupport
          e upper α β)) ≤
      (FacePartition.complexity upper : ℝ) * α +
        (orderedAtomEnergy
            (positiveFaceLowerLayer P.fine e) e.face upper -
          orderedAtomEnergy
            (positiveFaceLowerLayer P.coarse e) e.face upper) / β := by
  calc
    mean (finsetIndicator
        (P.sourceFullOwnAtomBadBaseSupport
          e upper α β)) ≤
        ∑ a : upper.parts,
          mean (finsetIndicator
            (a.1 ∩ P.sourceFullAtomBadBaseSupport
              e upper a α β)) := by
      exact
        mean_finsetIndicator_biUnion_le_sum
          (Finset.univ : Finset upper.parts)
          (fun a =>
            a.1 ∩ P.sourceFullAtomBadBaseSupport
              e upper a α β)
    _ ≤
        ∑ a : upper.parts,
          (α + mean
            (P.sourceFullAtomDefectSq e upper a) / β) := by
      apply Finset.sum_le_sum
      intro a _ha
      exact
        P.mean_indicator_atom_inter_sourceFullAtomBadBaseSupport_le
          e upper a hα hβ
    _ =
        (FacePartition.complexity upper : ℝ) * α +
          (orderedAtomEnergy
              (positiveFaceLowerLayer P.fine e) e.face upper -
            orderedAtomEnergy
              (positiveFaceLowerLayer P.coarse e) e.face upper) / β := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div]
      simp only [Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      rw [Fintype.card_coe]
      rw [← P.orderedAtomEnergy_sub_eq_sum_mean_sourceFullAtomDefectSq
        e upper]
      rfl

noncomputable def sourceFullCoarseOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (α β : ℝ) :
    Finset (Fin (e.lowerRank.1 + 1) → G) :=
  P.sourceFullOwnAtomBadBaseSupport e
    (P.coarse.partition e.lowerRank.succ e.face) α β

@[simp]
theorem mem_sourceFullCoarseOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (α β : ℝ) (x : Fin (e.lowerRank.1 + 1) → G) :
    x ∈ P.sourceFullCoarseOwnAtomBadBaseSupport e α β ↔
      x ∈ P.sourceFullAtomBadBaseSupport e
        (P.coarse.partition e.lowerRank.succ e.face)
        (partitionAtomAt
          (P.coarse.partition e.lowerRank.succ e.face) x)
        α β := by
  exact
    P.mem_sourceFullOwnAtomBadBaseSupport e
      (P.coarse.partition e.lowerRank.succ e.face) α β x

theorem mean_indicator_sourceFullCoarseOwnAtomBadBaseSupport_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β) :
    mean (finsetIndicator
        (P.sourceFullCoarseOwnAtomBadBaseSupport e α β)) ≤
      (FacePartition.complexity
          (P.coarse.partition e.lowerRank.succ e.face) : ℝ) * α +
        P.coarseUpperFaceAtomEnergyGap
          e.lowerRank e.face / β := by
  unfold sourceFullCoarseOwnAtomBadBaseSupport
    coarseUpperFaceAtomEnergyGap
  exact
    P.mean_indicator_sourceFullOwnAtomBadBaseSupport_le
      e (P.coarse.partition e.lowerRank.succ e.face) hα hβ

end OrderedCoarseFineComplex

theorem sourceFullMixedDefect_eq_orderedAtomBoundaryDefect_of_mem
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G)
    (hy :
      y ∈
        (orderedFullLowerBoundaryPartition P.coarse e).part
          (orderedFaceTuple e.face A.witness)) :
    sourceFullMixedDefect P A e y =
      orderedAtomBoundaryDefect
        (positiveFaceLowerLayer P.fine e)
        (positiveFaceLowerLayer P.coarse e)
        e.face
        (P.coarse.partition e.lowerRank.succ e.face)
        (A.atom e.lowerRank.succ e.face) y := by
  have himmediate :
      y ∈
        (orderedBoundaryPartition
          (positiveFaceLowerLayer P.coarse e) e.face).part
          (orderedFaceTuple e.face A.witness) :=
    FacePartition.part_subset_of_le
      (orderedFullLowerBoundaryPartition_le_immediate
        P.coarse e)
      (orderedFaceTuple e.face A.witness) hy
  have hindicator :
      mixedConfigurationBoundaryIndicator P A e y = 1 := by
    unfold mixedConfigurationBoundaryIndicator
    exact partitionAtomIndicator_of_mem _ _ himmediate
  have h :=
    mixedConfigurationDefect_mul_boundaryIndicator P A e y
  rw [hindicator, mul_one, mul_one] at h
  simpa [sourceFullMixedDefect] using h

theorem conditionalMean_sourceFullMixedDefect_sq_eq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r) :
    conditionalMean
        (orderedFullLowerBoundaryPartition P.coarse e)
        (fun y => sourceFullMixedDefect P A e y ^ 2)
        (orderedFaceTuple e.face A.witness) =
      conditionalMean
        (orderedFullLowerBoundaryPartition P.coarse e)
        (P.sourceFullAtomDefectSq e
          (P.coarse.partition e.lowerRank.succ e.face)
          (A.atom e.lowerRank.succ e.face))
        (orderedFaceTuple e.face A.witness) := by
  unfold conditionalMean
  apply Finset.expect_congr rfl
  intro y hy
  rw [sourceFullMixedDefect_eq_orderedAtomBoundaryDefect_of_mem
    P A e y hy]
  rfl

namespace ClosedOrderedAtomConfiguration

def AvoidsSourceFullBadBases
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ) : Prop :=
  ∀ e : PositiveOrderedFace k r,
    orderedFaceTuple e.face A.witness ∉
      P.sourceFullCoarseOwnAtomBadBaseSupport e
        (α e.rank) (β e.rank)

theorem sourceFullMixedGoodAtFace_of_not_mem_badBase
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (α β : ℝ)
    (havoid :
      orderedFaceTuple e.face A.witness ∉
        P.sourceFullCoarseOwnAtomBadBaseSupport e α β) :
    SourceFullMixedGoodAtFace P A e α β := by
  let upper :=
    P.coarse.partition e.lowerRank.succ e.face
  let a : upper.parts :=
    A.atom e.lowerRank.succ e.face
  let x : Fin (e.lowerRank.1 + 1) → G :=
    orderedFaceTuple e.face A.witness
  have hcanonical :
      partitionAtomAt upper x = a := by
    exact (A.atom_eq_partitionAtomAt
      e.lowerRank.succ e.face).symm
  have hlocal :
      x ∉ P.sourceFullAtomBadBaseSupport
        e upper a α β := by
    intro hbad
    apply havoid
    apply
      (P.mem_sourceFullCoarseOwnAtomBadBaseSupport
        e α β x).2
    change
      x ∈ P.sourceFullAtomBadBaseSupport
        e upper (partitionAtomAt upper x) α β
    rw [hcanonical]
    exact hbad
  have hlow :
      x ∉
        smallAverageBaseSupport
          (orderedBoundaryPartition
            (positiveFaceLowerLayer P.coarse e) e.face)
          (partitionAtomIndicator upper a) α := by
    intro h
    exact hlocal (Finset.mem_union_left _ h)
  have hlarge :
      x ∉
        P.sourceFullLargeDefectBaseSupport
          e upper a β := by
    intro h
    exact hlocal (Finset.mem_union_right _ h)
  constructor
  · have hdensity :
        α ≤
          conditionalMean
            (orderedBoundaryPartition
              (positiveFaceLowerLayer P.coarse e) e.face)
            (partitionAtomIndicator upper a) x :=
      not_lt.mp fun h =>
        hlow
          ((mem_smallAverageBaseSupport
            (orderedBoundaryPartition
              (positiveFaceLowerLayer P.coarse e) e.face)
            (partitionAtomIndicator upper a) α x).2 h)
    simpa [sourceFullMixedCoarseDensity,
      mixedConfigurationCoarseDensity, upper, a, x,
      orderedBoundaryStructured] using hdensity
  · rw [conditionalMean_sourceFullMixedDefect_sq_eq P A e]
    have hdefect :
        conditionalMean
            (orderedFullLowerBoundaryPartition P.coarse e)
            (P.sourceFullAtomDefectSq e upper a) x ≤
          β :=
      not_lt.mp fun h =>
        hlarge
          ((P.mem_sourceFullLargeDefectBaseSupport
            e upper a β x).2 h)
    simpa [upper, a, x] using hdefect

theorem isSourceFullMixedGood_of_avoids_badBases
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (havoid : A.AvoidsSourceFullBadBases P α β) :
    A.IsSourceFullMixedGood P α β := by
  intro e
  exact
    A.sourceFullMixedGoodAtFace_of_not_mem_badBase
      P e (α e.rank) (β e.rank) (havoid e)

end ClosedOrderedAtomConfiguration

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace OrderedCoarseFineComplex

noncomputable def sourceFullTopBadBaseDeletion
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : OrderedFace k r)
    (α β : ℕ → ℝ) :
    Finset (Fin r → G) := by
  classical
  exact
    (Finset.univ :
      Finset (OrderedPositiveSubface r)).biUnion fun q =>
      orderedFacePullbackFinset q.2
        (P.sourceFullCoarseOwnAtomBadBaseSupport
          ({ lowerRank := q.1
             face := q.2.trans e } : PositiveOrderedFace k r)
          (α (q.1.1 + 1))
          (β (q.1.1 + 1)))

noncomputable def sourceFullBadBaseDeletionFamily
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (α β : ℕ → ℝ) :
    OrderedPattern.DeletionFamily (G := G) k r :=
  fun e => P.sourceFullTopBadBaseDeletion e α β

theorem mean_indicator_sourceFullTopBadBaseDeletion_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : OrderedFace k r)
    (α β : ℕ → ℝ)
    (hα : ∀ j, 0 ≤ α (j + 1))
    (hβ : ∀ j, 0 < β (j + 1)) :
    mean (finsetIndicator
        (P.sourceFullTopBadBaseDeletion e α β)) ≤
      ∑ q : OrderedPositiveSubface r,
        ((FacePartition.complexity
            (P.coarse.partition q.1.succ
              (q.2.trans e)) : ℝ) *
            α (q.1.1 + 1) +
          P.coarseUpperFaceAtomEnergyGap
              q.1 (q.2.trans e) /
            β (q.1.1 + 1)) := by
  calc
    mean (finsetIndicator
        (P.sourceFullTopBadBaseDeletion e α β)) ≤
        ∑ q : OrderedPositiveSubface r,
          mean (finsetIndicator
            (orderedFacePullbackFinset q.2
              (P.sourceFullCoarseOwnAtomBadBaseSupport
                ({ lowerRank := q.1
                   face := q.2.trans e } :
                  PositiveOrderedFace k r)
                (α (q.1.1 + 1))
                (β (q.1.1 + 1))))) := by
      exact
        mean_finsetIndicator_biUnion_le_sum
          (Finset.univ : Finset (OrderedPositiveSubface r))
          (fun q =>
            orderedFacePullbackFinset q.2
              (P.sourceFullCoarseOwnAtomBadBaseSupport
                ({ lowerRank := q.1
                   face := q.2.trans e } :
                  PositiveOrderedFace k r)
                (α (q.1.1 + 1))
                (β (q.1.1 + 1))))
    _ ≤
        ∑ q : OrderedPositiveSubface r,
          ((FacePartition.complexity
              (P.coarse.partition q.1.succ
                (q.2.trans e)) : ℝ) *
              α (q.1.1 + 1) +
            P.coarseUpperFaceAtomEnergyGap
                q.1 (q.2.trans e) /
              β (q.1.1 + 1)) := by
      apply Finset.sum_le_sum
      intro q _hq
      rw [mean_indicator_orderedFacePullbackFinset]
      exact
        P.mean_indicator_sourceFullCoarseOwnAtomBadBaseSupport_le
          ({ lowerRank := q.1
             face := q.2.trans e } : PositiveOrderedFace k r)
          (hα q.1.1) (hβ q.1.1)

theorem faceDeletionDensity_sourceFullBadBaseDeletionFamily_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (α β : ℕ → ℝ)
    (hα : ∀ j, 0 ≤ α (j + 1))
    (hβ : ∀ j, 0 < β (j + 1))
    (e : OrderedFace k r) :
    OrderedPattern.faceDeletionDensity
        (P.sourceFullBadBaseDeletionFamily α β) e ≤
      ∑ q : OrderedPositiveSubface r,
        ((FacePartition.complexity
            (P.coarse.partition q.1.succ
              (q.2.trans e)) : ℝ) *
            α (q.1.1 + 1) +
          P.coarseUpperFaceAtomEnergyGap
              q.1 (q.2.trans e) /
            β (q.1.1 + 1)) := by
  rw [show
      OrderedPattern.faceDeletionDensity
          (P.sourceFullBadBaseDeletionFamily α β) e =
        mean (finsetIndicator
          (P.sourceFullTopBadBaseDeletion e α β)) by
    unfold OrderedPattern.faceDeletionDensity
      sourceFullBadBaseDeletionFamily
    rw [mean_finsetIndicator]]
  exact
    P.mean_indicator_sourceFullTopBadBaseDeletion_le
      e α β hα hβ

theorem faceDeletionDensity_sourceFullBadBaseDeletionFamily_le_fineGap
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (α β : ℕ → ℝ)
    (hα : ∀ j, 0 ≤ α (j + 1))
    (hβ : ∀ j, 0 < β (j + 1))
    (e : OrderedFace k r) :
    OrderedPattern.faceDeletionDensity
        (P.sourceFullBadBaseDeletionFamily α β) e ≤
      ∑ q : OrderedPositiveSubface r,
        ((FacePartition.complexity
            (P.coarse.partition q.1.succ
              (q.2.trans e)) : ℝ) *
            α (q.1.1 + 1) +
          ((FacePartition.complexity
              (P.fine.partition q.1.succ
                (q.2.trans e)) : ℝ) *
            P.faceAtomEnergyGap q.1 (q.2.trans e)) /
            β (q.1.1 + 1)) := by
  calc
    OrderedPattern.faceDeletionDensity
        (P.sourceFullBadBaseDeletionFamily α β) e ≤
        ∑ q : OrderedPositiveSubface r,
          ((FacePartition.complexity
              (P.coarse.partition q.1.succ
                (q.2.trans e)) : ℝ) *
              α (q.1.1 + 1) +
            P.coarseUpperFaceAtomEnergyGap
                q.1 (q.2.trans e) /
              β (q.1.1 + 1)) :=
      P.faceDeletionDensity_sourceFullBadBaseDeletionFamily_le
        α β hα hβ e
    _ ≤
        ∑ q : OrderedPositiveSubface r,
          ((FacePartition.complexity
              (P.coarse.partition q.1.succ
                (q.2.trans e)) : ℝ) *
              α (q.1.1 + 1) +
            ((FacePartition.complexity
                (P.fine.partition q.1.succ
                  (q.2.trans e)) : ℝ) *
              P.faceAtomEnergyGap q.1 (q.2.trans e)) /
              β (q.1.1 + 1)) := by
      apply Finset.sum_le_sum
      intro q _hq
      exact add_le_add
        (le_refl _)
        (div_le_div_of_nonneg_right
          (P.coarseUpperFaceAtomEnergyGap_le
            q.1 (q.2.trans e))
          (hβ q.1.1).le)

theorem faceDeletionDensity_sourceFullBadBaseDeletionFamily_constant_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r coarseBound fineBound : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (hcoarse :
      ∀ (j : Fin (r + 1)) (e : OrderedFace k j.1),
        FacePartition.complexity
          (P.coarse.partition j e) ≤ coarseBound)
    (hfine :
      ∀ (j : Fin (r + 1)) (e : OrderedFace k j.1),
        FacePartition.complexity
          (P.fine.partition j e) ≤ fineBound)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β)
    (e : OrderedFace k r) :
    OrderedPattern.faceDeletionDensity
        (P.sourceFullBadBaseDeletionFamily
          (fun _ => α) (fun _ => β)) e ≤
      (Fintype.card (OrderedPositiveSubface r) : ℝ) *
        ((coarseBound : ℝ) * α +
          (fineBound : ℝ) * P.totalAtomEnergyGap / β) := by
  calc
    OrderedPattern.faceDeletionDensity
        (P.sourceFullBadBaseDeletionFamily
          (fun _ => α) (fun _ => β)) e ≤
        ∑ q : OrderedPositiveSubface r,
          ((FacePartition.complexity
              (P.coarse.partition q.1.succ
                (q.2.trans e)) : ℝ) * α +
            ((FacePartition.complexity
                (P.fine.partition q.1.succ
                  (q.2.trans e)) : ℝ) *
              P.faceAtomEnergyGap q.1 (q.2.trans e)) / β) := by
      exact
        P.faceDeletionDensity_sourceFullBadBaseDeletionFamily_le_fineGap
          (fun _ => α) (fun _ => β)
          (fun _ => hα) (fun _ => hβ) e
    _ ≤
        ∑ _q : OrderedPositiveSubface r,
          ((coarseBound : ℝ) * α +
            (fineBound : ℝ) * P.totalAtomEnergyGap / β) := by
      apply Finset.sum_le_sum
      intro q _hq
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right
          (Nat.cast_le.mpr
            (hcoarse q.1.succ (q.2.trans e)))
          hα
      · apply div_le_div_of_nonneg_right _ hβ.le
        calc
          (FacePartition.complexity
                (P.fine.partition q.1.succ
                  (q.2.trans e)) : ℝ) *
              P.faceAtomEnergyGap q.1 (q.2.trans e) ≤
              (fineBound : ℝ) *
                P.faceAtomEnergyGap q.1 (q.2.trans e) :=
            mul_le_mul_of_nonneg_right
              (Nat.cast_le.mpr
                (hfine q.1.succ (q.2.trans e)))
              (P.faceAtomEnergyGap_nonneg
                q.1 (q.2.trans e))
          _ ≤
              (fineBound : ℝ) * P.totalAtomEnergyGap :=
            mul_le_mul_of_nonneg_left
              (P.faceAtomEnergyGap_le_total
                q.1 (q.2.trans e))
              (Nat.cast_nonneg fineBound)
    _ =
        (Fintype.card (OrderedPositiveSubface r) : ℝ) *
          ((coarseBound : ℝ) * α +
            (fineBound : ℝ) * P.totalAtomEnergyGap / β) := by
      simp only [Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]

end OrderedCoarseFineComplex

namespace ClosedOrderedAtomConfiguration

theorem isSourceFullMixedGood_of_avoids_sourceFullTopBadBaseDeletion
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (hrk : r ≤ k)
    (P : OrderedCoarseFineComplex G k r)
    (x : Fin k → G) (α β : ℕ → ℝ)
    (havoid :
      ∀ e : OrderedFace k r,
        orderedFaceTuple e x ∉
          P.sourceFullTopBadBaseDeletion e α β) :
    (ClosedOrderedAtomConfiguration.ofTuple
      P.coarse x).IsSourceFullMixedGood P α β := by
  apply
    (ClosedOrderedAtomConfiguration.ofTuple
      P.coarse x).isSourceFullMixedGood_of_avoids_badBases
      P α β
  intro f hbad
  obtain ⟨e, d, hde⟩ :=
    exists_orderedFace_factor_through
      (Nat.succ_le_iff.mpr f.lowerRank.2) hrk f.face
  apply havoid e
  rw [OrderedCoarseFineComplex.sourceFullTopBadBaseDeletion]
  apply Finset.mem_biUnion.mpr
  refine ⟨⟨f.lowerRank, d⟩, Finset.mem_univ _, ?_⟩
  rw [mem_orderedFacePullbackFinset]
  change
    orderedFaceTuple (d.trans e) x ∈
      P.sourceFullCoarseOwnAtomBadBaseSupport
        ({ lowerRank := f.lowerRank
           face := d.trans e } : PositiveOrderedFace k r)
        (α (f.lowerRank.1 + 1))
        (β (f.lowerRank.1 + 1))
  rw [hde]
  exact hbad

end ClosedOrderedAtomConfiguration

theorem sourceFullBadBaseDeletionFamily_isCover_of_sourceFullMixedGood_count
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k n : ℕ} (hrk : n + 1 ≤ k)
    (H : OrderedPattern G k (n + 1))
    (P : OrderedCoarseFineComplex G k (n + 1))
    (hinitial :
      P.coarse.Refines (orderedPatternInitialComplex H))
    (α β : ℕ → ℝ) (c : ℝ)
    (hcount : H.toWeighted.patternCount < c)
    (hgoodCount :
      ∀ A : ClosedOrderedAtomConfiguration
          G k (n + 1) P.coarse,
        A.IsSourceFullMixedGood P α β →
          c ≤ fullConfigurationCount A) :
    H.IsCover
      (P.sourceFullBadBaseDeletionFamily α β) := by
  intro x hx
  by_contra hsurvives
  push Not at hsurvives
  let A :
      ClosedOrderedAtomConfiguration
        G k (n + 1) P.coarse :=
    ClosedOrderedAtomConfiguration.ofTuple P.coarse x
  have hgood : A.IsSourceFullMixedGood P α β := by
    exact
      ClosedOrderedAtomConfiguration.isSourceFullMixedGood_of_avoids_sourceFullTopBadBaseDeletion
        hrk P x α β hsurvives
  have hcA : c ≤ fullConfigurationCount A :=
    hgoodCount A hgood
  have htop :
      OrderedFacePartitionRefines P.coarse.topLayer
        (orderedPatternTopPartition H) :=
    orderedPatternTopPartition_refines_of_complex_refines_initial
      H hinitial
  have hAH :
      fullConfigurationCount A ≤
        H.toWeighted.patternCount :=
    fullConfigurationCount_le_patternCount
      H htop A ((H.mem_occurrenceFinset x).1 hx)
  linarith

end Erdos3.FixedDensity

end

end OAI
