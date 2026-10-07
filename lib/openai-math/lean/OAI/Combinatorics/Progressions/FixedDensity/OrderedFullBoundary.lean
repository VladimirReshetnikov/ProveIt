-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import OAI.Combinatorics.Progressions.FixedDensity.ConfigurationWeightedDefect
import OAI.Compat.BigOperators

namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

abbrev ProperPositiveOrderedSubface (n : ℕ) :=
  PositiveOrderedFace (n + 1) n

@[simp]
theorem properPositiveOrderedSubface_rank_lt_upper {n : ℕ}
    (d : ProperPositiveOrderedSubface n) :
    d.rank < n + 1 := by
  simp only [PositiveOrderedFace.rank]
  exact Nat.succ_lt_succ d.lowerRank.2

abbrev orderedFullLowerComplexRank
    {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    Fin (r + 1) :=
  ⟨d.lowerRank.1 + 1, by
    have hd : d.rank < e.rank := by
      exact properPositiveOrderedSubface_rank_lt_upper d
    have he : e.rank ≤ r := by
      simp only [PositiveOrderedFace.rank]
      exact e.lowerRank.2
    omega⟩

@[simp]
theorem orderedFullLowerComplexRank_val
    {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    (orderedFullLowerComplexRank e d).1 =
      d.lowerRank.1 + 1 :=
  rfl

abbrev orderedFullLowerAmbientFace
    {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    OrderedFace k (d.lowerRank.1 + 1) :=
  d.face.trans e.face

@[simp]
theorem orderedFaceTuple_orderedFullLowerAmbientFace
    {G : Type*} {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1)
    (x : Fin k → G) :
    orderedFaceTuple (orderedFullLowerAmbientFace e d) x =
      orderedFaceTuple d.face (orderedFaceTuple e.face x) :=
  rfl

noncomputable def orderedFullLowerConstituentPartition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    FacePartition (Fin (e.lowerRank.1 + 1) → G) :=
  FacePartition.pullback
    (orderedFaceTuple d.face)
    (C.partition
      (orderedFullLowerComplexRank e d)
      (orderedFullLowerAmbientFace e d))

noncomputable def orderedFullLowerPositivePartition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r) :
    FacePartition (Fin (e.lowerRank.1 + 1) → G) :=
  FacePartition.joinFinset
    (Finset.univ :
      Finset (ProperPositiveOrderedSubface e.lowerRank.1))
    (orderedFullLowerConstituentPartition C e)

theorem orderedFullLowerPositivePartition_le_constituent
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    orderedFullLowerPositivePartition C e ≤
      orderedFullLowerConstituentPartition C e d := by
  exact FacePartition.joinFinset_le_of_mem
    (orderedFullLowerConstituentPartition C e)
    (Finset.mem_univ d)

theorem orderedFullLowerPositivePartition_mono
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {fine coarse : OrderedPartitionComplex G k r}
    (hfc : fine.Refines coarse)
    (e : PositiveOrderedFace k r) :
    orderedFullLowerPositivePartition fine e ≤
      orderedFullLowerPositivePartition coarse e := by
  apply FacePartition.le_joinFinset_iff.mpr
  intro d _hd
  exact le_trans
    (orderedFullLowerPositivePartition_le_constituent fine e d)
    (FacePartition.pullback_mono
      (orderedFaceTuple d.face)
      (hfc
        (orderedFullLowerComplexRank e d)
        (orderedFullLowerAmbientFace e d)))

noncomputable def orderedFullLowerBoundaryPartition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r) :
    FacePartition (Fin (e.lowerRank.1 + 1) → G) :=
  FacePartition.join
    (orderedBoundaryPartition
      (positiveFaceLowerLayer C e) e.face)
    (orderedFullLowerPositivePartition C e)

theorem orderedFullLowerBoundaryPartition_le_immediate
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r) :
    orderedFullLowerBoundaryPartition C e ≤
      orderedBoundaryPartition
        (positiveFaceLowerLayer C e) e.face := by
  exact FacePartition.join_le_left _ _

theorem orderedFullLowerBoundaryPartition_le_constituent
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    orderedFullLowerBoundaryPartition C e ≤
      orderedFullLowerConstituentPartition C e d := by
  exact le_trans
    (FacePartition.join_le_right _ _)
    (orderedFullLowerPositivePartition_le_constituent C e d)

theorem orderedFullLowerBoundaryPartition_mono
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {fine coarse : OrderedPartitionComplex G k r}
    (hfc : fine.Refines coarse)
    (e : PositiveOrderedFace k r) :
    orderedFullLowerBoundaryPartition fine e ≤
      orderedFullLowerBoundaryPartition coarse e := by
  apply FacePartition.le_join_iff.mpr
  constructor
  · exact le_trans
      (orderedFullLowerBoundaryPartition_le_immediate fine e)
      (orderedBoundaryPartition_mono
        (fun f =>
          hfc e.lowerRank.castSucc f)
        e.face)
  · exact le_trans
      (FacePartition.join_le_right _ _)
      (orderedFullLowerPositivePartition_mono hfc e)

theorem mem_orderedFullLowerBoundaryPartition_part_iff
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x y : Fin (e.lowerRank.1 + 1) → G) :
    y ∈ (orderedFullLowerBoundaryPartition C e).part x ↔
      y ∈
          (orderedBoundaryPartition
            (positiveFaceLowerLayer C e) e.face).part x ∧
        ∀ d : ProperPositiveOrderedSubface e.lowerRank.1,
          orderedFaceTuple d.face y ∈
            (C.partition
              (orderedFullLowerComplexRank e d)
              (orderedFullLowerAmbientFace e d)).part
              (orderedFaceTuple d.face x) := by
  rw [orderedFullLowerBoundaryPartition, FacePartition.part_join,
    Finset.mem_inter, orderedFullLowerPositivePartition,
    FacePartition.mem_part_joinFinset_iff]
  simp only [Finset.mem_univ, forall_const,
    orderedFullLowerConstituentPartition,
    FacePartition.mem_part_pullback_iff_image_mem]

theorem orderedFaceTuple_mem_orderedFullLowerBoundaryPartition_part_iff
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x y : Fin k → G) :
    orderedFaceTuple e.face y ∈
        (orderedFullLowerBoundaryPartition C e).part
          (orderedFaceTuple e.face x) ↔
      orderedFaceTuple e.face y ∈
          (orderedBoundaryPartition
            (positiveFaceLowerLayer C e) e.face).part
            (orderedFaceTuple e.face x) ∧
        ∀ d : ProperPositiveOrderedSubface e.lowerRank.1,
          orderedFaceTuple (orderedFullLowerAmbientFace e d) y ∈
            (C.partition
              (orderedFullLowerComplexRank e d)
              (orderedFullLowerAmbientFace e d)).part
              (orderedFaceTuple
                (orderedFullLowerAmbientFace e d) x) := by
  rw [mem_orderedFullLowerBoundaryPartition_part_iff]
  constructor
  · rintro ⟨hboundary, hsubfaces⟩
    refine ⟨hboundary, ?_⟩
    intro d
    rw [orderedFaceTuple_orderedFullLowerAmbientFace e d y,
      orderedFaceTuple_orderedFullLowerAmbientFace e d x]
    exact hsubfaces d
  · rintro ⟨hboundary, hsubfaces⟩
    refine ⟨hboundary, ?_⟩
    intro d
    have hd := hsubfaces d
    rw [orderedFaceTuple_orderedFullLowerAmbientFace e d y,
      orderedFaceTuple_orderedFullLowerAmbientFace e d x] at hd
    exact hd

theorem complexity_orderedFullLowerBoundaryPartition_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r) :
    FacePartition.complexity
        (orderedFullLowerBoundaryPartition C e) ≤
      FacePartition.complexity
          (orderedBoundaryPartition
            (positiveFaceLowerLayer C e) e.face) *
        ∏ d : ProperPositiveOrderedSubface e.lowerRank.1,
          FacePartition.complexity
            (C.partition
              (orderedFullLowerComplexRank e d)
              (orderedFullLowerAmbientFace e d)) := by
  calc
    FacePartition.complexity
        (orderedFullLowerBoundaryPartition C e) ≤
        FacePartition.complexity
            (orderedBoundaryPartition
              (positiveFaceLowerLayer C e) e.face) *
          FacePartition.complexity
            (orderedFullLowerPositivePartition C e) := by
      exact FacePartition.complexity_join_le _ _
    _ ≤
        FacePartition.complexity
            (orderedBoundaryPartition
              (positiveFaceLowerLayer C e) e.face) *
          ∏ d : ProperPositiveOrderedSubface e.lowerRank.1,
            FacePartition.complexity
              (orderedFullLowerConstituentPartition C e d) := by
      exact Nat.mul_le_mul_left _
        (FacePartition.complexity_joinFinset_le
          (Finset.univ :
            Finset (ProperPositiveOrderedSubface e.lowerRank.1))
          (orderedFullLowerConstituentPartition C e))
    _ ≤
        FacePartition.complexity
            (orderedBoundaryPartition
              (positiveFaceLowerLayer C e) e.face) *
          ∏ d : ProperPositiveOrderedSubface e.lowerRank.1,
            FacePartition.complexity
              (C.partition
                (orderedFullLowerComplexRank e d)
                (orderedFullLowerAmbientFace e d)) := by
      apply Nat.mul_le_mul_left
      apply Finset.prod_le_prod₀
      · intro d _hd
        exact Nat.zero_le _
      · intro d _hd
        exact FacePartition.complexity_pullback_le
          (orderedFaceTuple d.face)
          (C.partition
            (orderedFullLowerComplexRank e d)
            (orderedFullLowerAmbientFace e d))

noncomputable def orderedFullLowerBoundaryAtomAt
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x : Fin (e.lowerRank.1 + 1) → G) :
    (orderedFullLowerBoundaryPartition C e).parts :=
  partitionAtomAt (orderedFullLowerBoundaryPartition C e) x

@[simp]
theorem orderedFullLowerBoundaryAtomAt_val
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x : Fin (e.lowerRank.1 + 1) → G) :
    (orderedFullLowerBoundaryAtomAt C e x).1 =
      (orderedFullLowerBoundaryPartition C e).part x :=
  rfl

noncomputable def orderedFullLowerBoundaryWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  partitionAtomIndicator
    (orderedFullLowerBoundaryPartition C e)
    (orderedFullLowerBoundaryAtomAt C e x)
    y

theorem orderedFullLowerBoundaryWeight_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x y : Fin (e.lowerRank.1 + 1) → G) :
    0 ≤ orderedFullLowerBoundaryWeight C e x y :=
  partitionAtomIndicator_nonneg _ _ _

theorem orderedFullLowerBoundaryWeight_le_one
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x y : Fin (e.lowerRank.1 + 1) → G) :
    orderedFullLowerBoundaryWeight C e x y ≤ 1 :=
  partitionAtomIndicator_le_one _ _ _

theorem orderedFullLowerBoundaryWeight_le_immediateWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x y : Fin (e.lowerRank.1 + 1) → G) :
    orderedFullLowerBoundaryWeight C e x y ≤
      partitionAtomIndicator
        (orderedBoundaryPartition
          (positiveFaceLowerLayer C e) e.face)
        (orderedBoundaryAtomAt
          (positiveFaceLowerLayer C e) e.face x)
        y := by
  by_cases hy :
      y ∈ (orderedFullLowerBoundaryPartition C e).part x
  · have himmediate :
        y ∈
          (orderedBoundaryPartition
            (positiveFaceLowerLayer C e) e.face).part x :=
      FacePartition.part_subset_of_le
        (orderedFullLowerBoundaryPartition_le_immediate C e)
        x hy
    rw [show orderedFullLowerBoundaryWeight C e x y = 1 by
          exact partitionAtomIndicator_of_mem _ _ hy,
      partitionAtomIndicator_of_mem _ _ himmediate]
  · rw [show orderedFullLowerBoundaryWeight C e x y = 0 by
          exact partitionAtomIndicator_of_not_mem _ _ hy]
    exact partitionAtomIndicator_nonneg _ _ _

@[simp]
theorem orderedFullLowerBoundaryWeight_sq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x y : Fin (e.lowerRank.1 + 1) → G) :
    orderedFullLowerBoundaryWeight C e x y ^ 2 =
      orderedFullLowerBoundaryWeight C e x y :=
  partitionAtomIndicator_sq _ _ _

@[simp]
theorem orderedFullLowerBoundaryWeight_self
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x : Fin (e.lowerRank.1 + 1) → G) :
    orderedFullLowerBoundaryWeight C e x x = 1 := by
  apply partitionAtomIndicator_of_mem
  exact
    (orderedFullLowerBoundaryPartition C e).mem_part
      (Finset.mem_univ x)

theorem orderedFullLowerBoundaryWeight_eq_one_iff
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x y : Fin (e.lowerRank.1 + 1) → G) :
    orderedFullLowerBoundaryWeight C e x y = 1 ↔
      y ∈ (orderedFullLowerBoundaryPartition C e).part x := by
  constructor
  · intro h
    by_contra hy
    have hz :
        orderedFullLowerBoundaryWeight C e x y = 0 :=
      partitionAtomIndicator_of_not_mem _ _ hy
    linarith
  · intro hy
    exact partitionAtomIndicator_of_mem _ _ hy

theorem orderedFullLowerBoundaryWeight_eq_one_iff_all_subfaces
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x y : Fin (e.lowerRank.1 + 1) → G) :
    orderedFullLowerBoundaryWeight C e x y = 1 ↔
      y ∈
          (orderedBoundaryPartition
            (positiveFaceLowerLayer C e) e.face).part x ∧
        ∀ d : ProperPositiveOrderedSubface e.lowerRank.1,
          orderedFaceTuple d.face y ∈
            (C.partition
              (orderedFullLowerComplexRank e d)
              (orderedFullLowerAmbientFace e d)).part
              (orderedFaceTuple d.face x) := by
  rw [orderedFullLowerBoundaryWeight_eq_one_iff,
    mem_orderedFullLowerBoundaryPartition_part_iff]

noncomputable def orderedFullLowerStructured
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (f : (Fin (e.lowerRank.1 + 1) → G) → ℝ) :
    (Fin (e.lowerRank.1 + 1) → G) → ℝ :=
  conditionalMean (orderedFullLowerBoundaryPartition C e) f

noncomputable def sourceFullMixedCoarseDensity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r) : ℝ :=
  mixedConfigurationCoarseDensity P A e

noncomputable def sourceFullMixedDefect
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  mixedConfigurationDefect P A e y

noncomputable def sourceFullMixedBoundaryWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  orderedFullLowerBoundaryWeight P.coarse e
    (orderedFaceTuple e.face A.witness) y

@[simp]
theorem sourceFullMixedBoundaryWeight_sq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    sourceFullMixedBoundaryWeight P A e y ^ 2 =
      sourceFullMixedBoundaryWeight P A e y :=
  orderedFullLowerBoundaryWeight_sq _ _ _ _

theorem sourceFullMixedBoundaryWeight_le_mixedConfigurationBoundaryIndicator
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    sourceFullMixedBoundaryWeight P A e y ≤
      mixedConfigurationBoundaryIndicator P A e y := by
  exact orderedFullLowerBoundaryWeight_le_immediateWeight
    P.coarse e (orderedFaceTuple e.face A.witness) y

def SourceFullMixedGoodAtFace
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (α β : ℝ) : Prop :=
  α ≤ sourceFullMixedCoarseDensity P A e ∧
    conditionalMean
        (orderedFullLowerBoundaryPartition P.coarse e)
        (fun y => sourceFullMixedDefect P A e y ^ 2)
        (orderedFaceTuple e.face A.witness) ≤
      β

def ClosedOrderedAtomConfiguration.IsSourceFullMixedGood
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ) : Prop :=
  ∀ e : PositiveOrderedFace k r,
    SourceFullMixedGoodAtFace P A e
      (α e.rank) (β e.rank)

noncomputable def sourceFullMixedLocalizedDefectSq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r) : ℝ :=
  mean fun y =>
    sourceFullMixedDefect P A e y ^ 2 *
      sourceFullMixedBoundaryWeight P A e y

theorem SourceFullMixedGoodAtFace.localized_defect
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (α β : ℝ)
    (hgood : SourceFullMixedGoodAtFace P A e α β) :
    sourceFullMixedLocalizedDefectSq P A e ≤
      β * mean (sourceFullMixedBoundaryWeight P A e) := by
  unfold sourceFullMixedLocalizedDefectSq
  apply mean_mul_partitionAtomIndicator_le
    (orderedFullLowerBoundaryPartition P.coarse e)
    (fun y => sourceFullMixedDefect P A e y ^ 2)
    (orderedFullLowerBoundaryAtomAt P.coarse e
      (orderedFaceTuple e.face A.witness))
  have hrep :
      (orderedFullLowerBoundaryPartition P.coarse e).representative
          (orderedFullLowerBoundaryAtomAt P.coarse e
            (orderedFaceTuple e.face A.witness)) ∈
        (orderedFullLowerBoundaryPartition P.coarse e).part
          (orderedFaceTuple e.face A.witness) := by
    exact
      (orderedFullLowerBoundaryPartition P.coarse e).representative_mem
        (orderedFullLowerBoundaryAtomAt P.coarse e
          (orderedFaceTuple e.face A.witness))
  have heq :=
    conditionalMean_eq_of_mem_part
      (orderedFullLowerBoundaryPartition P.coarse e)
      (fun y => sourceFullMixedDefect P A e y ^ 2)
      hrep
  rw [heq]
  exact hgood.2

theorem ClosedOrderedAtomConfiguration.IsSourceFullMixedGood.localized_defect
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (hgood : A.IsSourceFullMixedGood P α β)
    (e : PositiveOrderedFace k r) :
    sourceFullMixedLocalizedDefectSq P A e ≤
      β e.rank *
        mean (sourceFullMixedBoundaryWeight P A e) :=
  (hgood e).localized_defect P A e
    (α e.rank) (β e.rank)

end Erdos3.FixedDensity

end

end OAI
