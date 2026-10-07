import OAI.Combinatorics.Progressions.FixedDensity.SourceFullOrderedRemoval
import OAI.Combinatorics.Progressions.FixedDensity.StrongOrderedComplexRegularity

namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

noncomputable def orderedRemovalConfigurationFaceCount (k r : ℕ) : ℕ :=
  Fintype.card (PositiveOrderedFace k r)

noncomputable def orderedRemovalTopSubfaceCount (r : ℕ) : ℕ :=
  Fintype.card (OrderedPositiveSubface r)

noncomputable def orderedRemovalComplexityCoefficient (r M : ℕ) : ℕ :=
  orderedRemovalTopSubfaceCount r * M

noncomputable def orderedRemovalDensityFloor
    (r M : ℕ) (ξ : ℝ) : ℝ :=
  min (1 / 2)
    (ξ /
      (4 *
        ((orderedRemovalComplexityCoefficient r M : ℝ) + 1)))

noncomputable def orderedRemovalCountingError
    (k r M : ℕ) (ξ : ℝ) : ℝ :=
  orderedRemovalDensityFloor r M ξ ^
      orderedRemovalConfigurationFaceCount k r /
    (4 *
      ((orderedRemovalConfigurationFaceCount k r : ℝ) + 1))

noncomputable def orderedRemovalDefectThreshold
    (k r M : ℕ) (ξ : ℝ) : ℝ :=
  orderedRemovalCountingError k r M ξ ^ 2

noncomputable def orderedRemovalEnergyGapTarget
    (k r M : ℕ) (ξ : ℝ) : ℝ :=
  ξ * orderedRemovalDefectThreshold k r M ξ / 4

noncomputable def orderedRemovalAlpha
    (r M : ℕ) (ξ : ℝ) : ℕ → ℝ :=
  fun _ => orderedRemovalDensityFloor r M ξ

noncomputable def orderedRemovalBeta
    (k r M : ℕ) (ξ : ℝ) : ℕ → ℝ :=
  fun _ => orderedRemovalDefectThreshold k r M ξ

noncomputable def orderedRemovalTolerance
    (k r M : ℕ) (ξ : ℝ) :
    OrderedRegularityTolerance r :=
  fun _ => orderedRemovalCountingError k r M ξ

noncomputable def orderedRemovalDeletionError
    (r M : ℕ) (α gap β : ℝ) : ℝ :=
  (orderedRemovalComplexityCoefficient r M : ℝ) * α +
    gap / β

noncomputable def orderedRemovalConfigurationLowerBound
    (k r : ℕ) (ρ η δ : ℝ) : ℝ :=
  ρ ^ orderedRemovalConfigurationFaceCount k r -
    (orderedRemovalConfigurationFaceCount k r : ℝ) *
      (η + δ)

theorem orderedRemovalDensityFloor_pos
    {r M : ℕ} {ξ : ℝ} (hξ : 0 < ξ) :
    0 < orderedRemovalDensityFloor r M ξ := by
  unfold orderedRemovalDensityFloor
  apply lt_min
  · norm_num
  · exact div_pos hξ
      (mul_pos (by norm_num)
        (by positivity))

theorem orderedRemovalDensityFloor_nonneg
    {r M : ℕ} {ξ : ℝ} (hξ : 0 < ξ) :
    0 ≤ orderedRemovalDensityFloor r M ξ :=
  (orderedRemovalDensityFloor_pos hξ).le

theorem orderedRemovalDensityFloor_le_half
    (r M : ℕ) (ξ : ℝ) :
    orderedRemovalDensityFloor r M ξ ≤ 1 / 2 := by
  unfold orderedRemovalDensityFloor
  exact min_le_left _ _

theorem orderedRemovalDensityFloor_le_fraction
    (r M : ℕ) (ξ : ℝ) :
    orderedRemovalDensityFloor r M ξ ≤
      ξ /
        (4 *
          ((orderedRemovalComplexityCoefficient r M : ℝ) + 1)) := by
  unfold orderedRemovalDensityFloor
  exact min_le_right _ _

theorem orderedRemovalCountingError_pos
    {k r M : ℕ} {ξ : ℝ} (hξ : 0 < ξ) :
    0 < orderedRemovalCountingError k r M ξ := by
  unfold orderedRemovalCountingError
  exact div_pos
    (pow_pos (orderedRemovalDensityFloor_pos hξ) _)
    (mul_pos (by norm_num) (by positivity))

theorem orderedRemovalCountingError_nonneg
    {k r M : ℕ} {ξ : ℝ} (hξ : 0 < ξ) :
    0 ≤ orderedRemovalCountingError k r M ξ :=
  (orderedRemovalCountingError_pos hξ).le

theorem orderedRemovalDefectThreshold_pos
    {k r M : ℕ} {ξ : ℝ} (hξ : 0 < ξ) :
    0 < orderedRemovalDefectThreshold k r M ξ := by
  unfold orderedRemovalDefectThreshold
  exact sq_pos_of_pos
    (orderedRemovalCountingError_pos hξ)

theorem orderedRemovalDefectThreshold_nonneg
    {k r M : ℕ} {ξ : ℝ} (hξ : 0 < ξ) :
    0 ≤ orderedRemovalDefectThreshold k r M ξ :=
  (orderedRemovalDefectThreshold_pos hξ).le

theorem orderedRemovalEnergyGapTarget_pos
    {k r M : ℕ} {ξ : ℝ} (hξ : 0 < ξ) :
    0 < orderedRemovalEnergyGapTarget k r M ξ := by
  unfold orderedRemovalEnergyGapTarget
  exact div_pos
    (mul_pos hξ (orderedRemovalDefectThreshold_pos hξ))
    (by norm_num)

theorem orderedRemoval_complexity_mul_densityFloor_le_quarter
    {r M : ℕ} {ξ : ℝ} (hξ : 0 < ξ) :
    (orderedRemovalComplexityCoefficient r M : ℝ) *
        orderedRemovalDensityFloor r M ξ ≤
      ξ / 4 := by
  let C : ℝ :=
    (orderedRemovalComplexityCoefficient r M : ℝ)
  have hC : 0 ≤ C := by
    exact Nat.cast_nonneg _
  have hden : 0 < C + 1 := by positivity
  have hfloor :
      orderedRemovalDensityFloor r M ξ ≤
        ξ / (4 * (C + 1)) := by
    exact orderedRemovalDensityFloor_le_fraction r M ξ
  calc
    C * orderedRemovalDensityFloor r M ξ ≤
        C * (ξ / (4 * (C + 1))) :=
      mul_le_mul_of_nonneg_left hfloor hC
    _ = (C / (C + 1)) * (ξ / 4) := by
      field_simp
    _ ≤ 1 * (ξ / 4) := by
      apply mul_le_mul_of_nonneg_right
      · exact (div_le_one hden).2 (by linarith)
      · positivity
    _ = ξ / 4 := one_mul _

theorem orderedRemovalEnergyGapTarget_div_defectThreshold
    {k r M : ℕ} {ξ : ℝ} (hξ : 0 < ξ) :
    orderedRemovalEnergyGapTarget k r M ξ /
        orderedRemovalDefectThreshold k r M ξ =
      ξ / 4 := by
  unfold orderedRemovalEnergyGapTarget
  have hβ :
      orderedRemovalDefectThreshold k r M ξ ≠ 0 :=
    (orderedRemovalDefectThreshold_pos hξ).ne'
  field_simp

theorem orderedRemovalDeletionError_le
    {k r M : ℕ} {ξ gap : ℝ}
    (hξ : 0 < ξ)
    (hgap :
      gap ≤ orderedRemovalEnergyGapTarget k r M ξ) :
    orderedRemovalDeletionError r M
        (orderedRemovalDensityFloor r M ξ)
        gap
        (orderedRemovalDefectThreshold k r M ξ) ≤
      ξ := by
  unfold orderedRemovalDeletionError
  have hβ :
      0 < orderedRemovalDefectThreshold k r M ξ :=
    orderedRemovalDefectThreshold_pos hξ
  calc
    (orderedRemovalComplexityCoefficient r M : ℝ) *
          orderedRemovalDensityFloor r M ξ +
        gap / orderedRemovalDefectThreshold k r M ξ ≤
        ξ / 4 +
          orderedRemovalEnergyGapTarget k r M ξ /
            orderedRemovalDefectThreshold k r M ξ := by
      exact add_le_add
        (orderedRemoval_complexity_mul_densityFloor_le_quarter hξ)
        (div_le_div_of_nonneg_right hgap hβ.le)
    _ = ξ / 2 := by
      rw [orderedRemovalEnergyGapTarget_div_defectThreshold hξ]
      ring
    _ ≤ ξ := by linarith

theorem orderedRemoval_counting_margin
    {k r M : ℕ} {ξ : ℝ} (hξ : 0 < ξ) :
    (orderedRemovalConfigurationFaceCount k r : ℝ) *
        (orderedRemovalCountingError k r M ξ +
          orderedRemovalCountingError k r M ξ) <
      orderedRemovalDensityFloor r M ξ ^
        orderedRemovalConfigurationFaceCount k r := by
  let N : ℝ :=
    (orderedRemovalConfigurationFaceCount k r : ℝ)
  let p : ℝ :=
    orderedRemovalDensityFloor r M ξ ^
      orderedRemovalConfigurationFaceCount k r
  have hN : 0 ≤ N := by
    exact Nat.cast_nonneg _
  have hp : 0 < p := by
    exact pow_pos (orderedRemovalDensityFloor_pos hξ) _
  have hden : 0 < 4 * (N + 1) := by positivity
  have hcoeff :
      (2 * N) / (4 * (N + 1)) < 1 := by
    apply (div_lt_one hden).2
    linarith
  calc
    N *
        (orderedRemovalCountingError k r M ξ +
          orderedRemovalCountingError k r M ξ) =
        ((2 * N) / (4 * (N + 1))) * p := by
      unfold orderedRemovalCountingError
      dsimp only [N, p]
      ring
    _ < 1 * p :=
      mul_lt_mul_of_pos_right hcoeff hp
    _ = p := one_mul _

theorem orderedRemovalConfigurationLowerBound_pos
    {k r M : ℕ} {ξ : ℝ} (hξ : 0 < ξ) :
    0 <
      orderedRemovalConfigurationLowerBound k r
        (orderedRemovalDensityFloor r M ξ)
        (orderedRemovalCountingError k r M ξ)
        (orderedRemovalCountingError k r M ξ) := by
  unfold orderedRemovalConfigurationLowerBound
  have hmargin :=
    orderedRemoval_counting_margin
      (k := k) (r := r) (M := M) hξ
  linarith

noncomputable def orderedRemovalRegularityBudget
    (k j : ℕ) (τ : ℝ) : ℕ :=
  Nat.ceil
      ((Fintype.card (OrderedFace k (j + 1)) : ℝ) /
        τ ^ 2) +
    1

noncomputable def orderedRemovalRegularityBudgetSchedule
    (k r : ℕ)
    (τ : (j : Fin r) → ℕ → ℝ) :
    (j : Fin r) → ℕ → ℕ :=
  fun j n => orderedRemovalRegularityBudget k j.1 (τ j n)

theorem orderedRemovalRegularityBudget_pos
    (k j : ℕ) (τ : ℝ) :
    0 < orderedRemovalRegularityBudget k j τ := by
  unfold orderedRemovalRegularityBudget
  omega

theorem orderedRemovalRegularityBudget_spec
    {k j : ℕ} {τ : ℝ} (hτ : 0 < τ) :
    (Fintype.card (OrderedFace k (j + 1)) : ℝ) <
      (orderedRemovalRegularityBudget k j τ : ℝ) * τ ^ 2 := by
  have hsq : 0 < τ ^ 2 := sq_pos_of_pos hτ
  have hquot :
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) /
          τ ^ 2 <
        (orderedRemovalRegularityBudget k j τ : ℝ) := by
    unfold orderedRemovalRegularityBudget
    calc
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) /
            τ ^ 2 ≤
          (Nat.ceil
            ((Fintype.card
              (OrderedFace k (j + 1)) : ℝ) /
                τ ^ 2) : ℝ) :=
        Nat.le_ceil _
      _ <
          (Nat.ceil
            ((Fintype.card
              (OrderedFace k (j + 1)) : ℝ) /
                τ ^ 2) : ℝ) + 1 := by
        linarith
      _ =
          ((Nat.ceil
              ((Fintype.card
                (OrderedFace k (j + 1)) : ℝ) /
                  τ ^ 2) + 1 : ℕ) : ℝ) := by
        norm_num
  exact (div_lt_iff₀ hsq).1 hquot

theorem orderedRemovalRegularityBudgetSchedule_spec
    {k r : ℕ}
    {τ : (j : Fin r) → ℕ → ℝ}
    (hτ : ∀ j n, 0 < τ j n) :
    ∀ j n,
      (Fintype.card
        (OrderedFace k (j.1 + 1)) : ℝ) <
        (orderedRemovalRegularityBudgetSchedule
          k r τ j n : ℝ) * (τ j n) ^ 2 := by
  intro j n
  exact orderedRemovalRegularityBudget_spec (hτ j n)

noncomputable def orderedRemovalEnergyTimescale
    (k r : ℕ) (γ : ℝ) : ℕ :=
  Nat.ceil (orderedAllRankAtomEnergyBudget k r / γ) + 1

noncomputable def orderedRemovalEnergyLength
    (k r : ℕ) (γ : ℝ) : Fin r → ℕ :=
  fun _ => orderedRemovalEnergyTimescale k r γ

theorem orderedRemovalEnergyTimescale_pos
    (k r : ℕ) (γ : ℝ) :
    0 < orderedRemovalEnergyTimescale k r γ := by
  unfold orderedRemovalEnergyTimescale
  omega

theorem orderedRemovalEnergyLength_pos
    (k r : ℕ) (γ : ℝ) :
    ∀ j, 0 < orderedRemovalEnergyLength k r γ j := by
  intro j
  exact orderedRemovalEnergyTimescale_pos k r γ

theorem orderedRemovalEnergyLength_sum_div_lt
    {k r : ℕ} {γ : ℝ} (hγ : 0 < γ) :
    (∑ j : Fin r,
      (Fintype.card
        (OrderedFace k (j.1 + 1)) : ℝ) /
          (orderedRemovalEnergyLength k r γ j : ℝ)) <
      γ := by
  let B : ℝ := orderedAllRankAtomEnergyBudget k r
  let L : ℕ := orderedRemovalEnergyTimescale k r γ
  have hLNat : 0 < L :=
    orderedRemovalEnergyTimescale_pos k r γ
  have hLCast : (0 : ℝ) < (L : ℝ) := by
    exact_mod_cast hLNat
  have hquot : B / γ < (L : ℝ) := by
    dsimp only [B, L]
    unfold orderedRemovalEnergyTimescale
    calc
      orderedAllRankAtomEnergyBudget k r / γ ≤
          (Nat.ceil
            (orderedAllRankAtomEnergyBudget k r / γ) : ℝ) :=
        Nat.le_ceil _
      _ <
          (Nat.ceil
            (orderedAllRankAtomEnergyBudget k r / γ) : ℝ) + 1 := by
        linarith
      _ =
          ((Nat.ceil
              (orderedAllRankAtomEnergyBudget k r / γ) + 1 : ℕ) : ℝ) := by
        norm_num
  have hbudget : B < (L : ℝ) * γ :=
    (div_lt_iff₀ hγ).1 hquot
  unfold orderedRemovalEnergyLength
  change
    (∑ j : Fin r,
      (Fintype.card
        (OrderedFace k (j.1 + 1)) : ℝ) / (L : ℝ)) < γ
  rw [← Finset.sum_div]
  change B / (L : ℝ) < γ
  apply (div_lt_iff₀ hLCast).2
  simpa [mul_comm] using hbudget

theorem fixedUpperLayerComplexityFactor_monotone
    (j : ℕ) (budget : ℕ → ℕ) :
    Monotone (fixedUpperLayerComplexityFactor j budget) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [fixedUpperLayerComplexityFactor]
  exact Nat.le_mul_of_pos_left _
    (pow_pos (by positivity) _)

def orderedRemovalFinePartitionComplexityBound
    (r initialBound : ℕ)
    (budget : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ) : ℕ :=
  initialBound *
    (1 +
      ∑ j : Fin r,
        fixedUpperLayerComplexityFactor
          j.1 (budget j) (length j))

theorem fixedUpperLayerComplexityFactor_le_removalBoundFactor
    {r : ℕ}
    (budget : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ)
    (j : Fin r) :
    fixedUpperLayerComplexityFactor
        j.1 (budget j) (length j) ≤
      1 +
        ∑ i : Fin r,
          fixedUpperLayerComplexityFactor
            i.1 (budget i) (length i) := by
  have hsum :
      fixedUpperLayerComplexityFactor
          j.1 (budget j) (length j) ≤
        ∑ i : Fin r,
          fixedUpperLayerComplexityFactor
            i.1 (budget i) (length i) := by
    exact Finset.single_le_sum
      (fun i _ => Nat.zero_le
        (fixedUpperLayerComplexityFactor
          i.1 (budget i) (length i)))
      (Finset.mem_univ j)
  omega

namespace StrongOrderedComplexRegularityCertificate

theorem fine_complexity_le_removalBound
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r initialBound : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : StrongOrderedComplexRegularityCertificate
      G k r initial ε budget length)
    (hinitial :
      ∀ (j : Fin (r + 1)) (e : OrderedFace k j.1),
        FacePartition.complexity
          (initial.partition j e) ≤ initialBound) :
    ∀ (j : Fin (r + 1)) (e : OrderedFace k j.1),
      FacePartition.complexity
          (R.fine.partition j e) ≤
        orderedRemovalFinePartitionComplexityBound
          r initialBound budget length := by
  intro j
  cases j using Fin.lastCases with
  | last =>
      intro e
      have htop := congrFun R.fine_topLayer_eq e
      simp only [OrderedPartitionComplex.topLayer] at htop
      rw [htop]
      apply (hinitial (Fin.last r) e).trans
      unfold orderedRemovalFinePartitionComplexityBound
      exact Nat.le_mul_of_pos_right initialBound
        (by positivity)
  | cast i =>
      intro e
      have hcertificate := R.fine_complexity i e
      have hindex :
          R.index i + 1 ≤ length i :=
        R.index_lt i
      have hfactor :
          fixedUpperLayerComplexityFactor
              i.1 (budget i) (R.index i + 1) ≤
            fixedUpperLayerComplexityFactor
              i.1 (budget i) (length i) :=
        fixedUpperLayerComplexityFactor_monotone
          i.1 (budget i) hindex
      have hfactorBound :
          fixedUpperLayerComplexityFactor
              i.1 (budget i) (length i) ≤
            1 +
              ∑ q : Fin r,
                fixedUpperLayerComplexityFactor
                  q.1 (budget q) (length q) :=
        fixedUpperLayerComplexityFactor_le_removalBoundFactor
          budget length i
      calc
        FacePartition.complexity
            (R.fine.partition i.castSucc e) ≤
            fixedUpperLayerComplexityFactor
                i.1 (budget i) (R.index i + 1) *
              FacePartition.complexity
                (initial.partition i.castSucc e) :=
          hcertificate
        _ ≤
            fixedUpperLayerComplexityFactor
                i.1 (budget i) (R.index i + 1) *
              initialBound :=
          Nat.mul_le_mul_left _
            (hinitial i.castSucc e)
        _ ≤
            fixedUpperLayerComplexityFactor
                i.1 (budget i) (length i) *
              initialBound :=
          Nat.mul_le_mul_right initialBound hfactor
        _ ≤
            orderedRemovalFinePartitionComplexityBound
              r initialBound budget length := by
          unfold orderedRemovalFinePartitionComplexityBound
          simpa [Nat.mul_comm] using
            Nat.mul_le_mul_left initialBound hfactorBound

end StrongOrderedComplexRegularityCertificate

noncomputable def orderedRemovalRankCleaningError
    (r : ℕ)
    (complexity : Fin r → ℕ)
    (α : ℕ → ℝ)
    (gap : Fin r → ℝ)
    (β : ℕ → ℝ) : ℝ :=
  ∑ j : Fin r,
    ((Fintype.card
        (OrderedFace r (j.1 + 1)) : ℝ) *
        (complexity j : ℝ) * α (j.1 + 1) +
      gap j / β (j.1 + 1))

noncomputable def orderedRemovalRankDensityProduct
    (k r : ℕ) (α : ℕ → ℝ) : ℝ :=
  ∏ e : PositiveOrderedFace k r, α e.rank

noncomputable def orderedRemovalRankCountingError
    (k r : ℕ)
    (η : Fin r → ℝ)
    (δ : ℕ → ℝ) : ℝ :=
  ∑ e : PositiveOrderedFace k r,
    (η e.lowerRank + δ e.rank)

def IsRankSensitiveOrderedRemovalChoice
    (k r : ℕ) (ξ : ℝ)
    (complexity : Fin r → ℕ)
    (α β : ℕ → ℝ)
    (gap : Fin r → ℝ)
    (η : Fin r → ℝ)
    (δ : ℕ → ℝ) : Prop :=
  orderedRemovalRankCleaningError
      r complexity α gap β ≤ ξ ∧
    orderedRemovalRankCountingError k r η δ <
      orderedRemovalRankDensityProduct k r α

structure IsStrongOrderedRemovalCompatible
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r initialBound : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : StrongOrderedComplexRegularityCertificate
      G k r initial ε budget length)
    (ξ : ℝ) : Prop where
  tolerance_le :
    ∀ j : Fin r,
      selectedOrderedComplexTolerance ε R.index j ≤
        orderedRemovalCountingError k r
          (orderedRemovalFinePartitionComplexityBound
            r initialBound budget length) ξ
  reciprocal_gap_le :
    (∑ j : Fin r,
      (Fintype.card
        (OrderedFace k (j.1 + 1)) : ℝ) /
          (length j : ℝ)) ≤
      orderedRemovalEnergyGapTarget k r
        (orderedRemovalFinePartitionComplexityBound
          r initialBound budget length) ξ

namespace StrongOrderedComplexRegularityCertificate

theorem faceDeletionDensity_badBase_le_removalAllowance
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r initialBound : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : StrongOrderedComplexRegularityCertificate
      G k r initial ε budget length)
    (hinitial :
      ∀ (j : Fin (r + 1)) (e : OrderedFace k j.1),
        FacePartition.complexity
          (initial.partition j e) ≤ initialBound)
    {ξ : ℝ} (hξ : 0 < ξ)
    (hcompatible :
      IsStrongOrderedRemovalCompatible
        (initialBound := initialBound) R ξ)
    (e : OrderedFace k r) :
    OrderedPattern.faceDeletionDensity
        (orderedBadBaseDeletionFamily
          R.fine R.coarse
          (orderedRemovalAlpha r
            (orderedRemovalFinePartitionComplexityBound
              r initialBound budget length) ξ)
          (orderedRemovalBeta k r
            (orderedRemovalFinePartitionComplexityBound
              r initialBound budget length) ξ)) e ≤
      ξ := by
  let M :=
    orderedRemovalFinePartitionComplexityBound
      r initialBound budget length
  let gap : ℝ :=
    ∑ j : Fin r,
      (Fintype.card
        (OrderedFace k (j.1 + 1)) : ℝ) /
          (length j : ℝ)
  change
    OrderedPattern.faceDeletionDensity
        (orderedBadBaseDeletionFamily
          R.fine R.coarse
          (fun _ => orderedRemovalDensityFloor r M ξ)
          (fun _ =>
            orderedRemovalDefectThreshold k r M ξ)) e ≤
      ξ
  have hdeletion :=
    R.faceDeletionDensity_badBase_constant_of_complexity_le_sum_div
      (M := M)
      (α := orderedRemovalDensityFloor r M ξ)
      (β := orderedRemovalDefectThreshold k r M ξ)
      (fun j e =>
        R.fine_complexity_le_removalBound
          hinitial j.succ e)
      (orderedRemovalDensityFloor_nonneg
        (r := r) (M := M) hξ)
      (orderedRemovalDefectThreshold_pos
        (k := k) (r := r) (M := M) hξ)
      e
  calc
    OrderedPattern.faceDeletionDensity
        (orderedBadBaseDeletionFamily
          R.fine R.coarse
          (fun _ => orderedRemovalDensityFloor r M ξ)
          (fun _ =>
            orderedRemovalDefectThreshold k r M ξ)) e ≤
        (Fintype.card (OrderedPositiveSubface r) : ℝ) *
            (M : ℝ) *
            orderedRemovalDensityFloor r M ξ +
          gap /
            orderedRemovalDefectThreshold k r M ξ := by
      simpa [M, gap] using hdeletion
    _ =
        orderedRemovalDeletionError r M
          (orderedRemovalDensityFloor r M ξ)
          gap
          (orderedRemovalDefectThreshold k r M ξ) := by
      unfold orderedRemovalDeletionError
        orderedRemovalComplexityCoefficient
        orderedRemovalTopSubfaceCount
      push_cast
      ring
    _ ≤ ξ :=
      orderedRemovalDeletionError_le hξ
        hcompatible.reciprocal_gap_le

theorem removalConfigurationLowerBound_le_fullConfigurationCount
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r initialBound : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : StrongOrderedComplexRegularityCertificate
      G k r initial ε budget length)
    (A : ClosedOrderedAtomConfiguration G k r R.fine)
    {ξ : ℝ} (hξ : 0 < ξ)
    (hcompatible :
      IsStrongOrderedRemovalCompatible
        (initialBound := initialBound) R ξ)
    (hgood :
      A.IsGood R.fine R.coarse
        (orderedRemovalAlpha r
          (orderedRemovalFinePartitionComplexityBound
            r initialBound budget length) ξ)
        (orderedRemovalBeta k r
          (orderedRemovalFinePartitionComplexityBound
            r initialBound budget length) ξ)) :
    orderedRemovalConfigurationLowerBound k r
        (orderedRemovalDensityFloor r
          (orderedRemovalFinePartitionComplexityBound
            r initialBound budget length) ξ)
        (orderedRemovalCountingError k r
          (orderedRemovalFinePartitionComplexityBound
            r initialBound budget length) ξ)
        (orderedRemovalCountingError k r
          (orderedRemovalFinePartitionComplexityBound
            r initialBound budget length) ξ) ≤
      fullConfigurationCount A := by
  let M :=
    orderedRemovalFinePartitionComplexityBound
      r initialBound budget length
  unfold orderedRemovalConfigurationLowerBound
    orderedRemovalConfigurationFaceCount
  apply
    fullConfigurationCount_lower_bound
      R.toCoarseFine A
      (orderedRemovalAlpha r M ξ)
      (orderedRemovalBeta k r M ξ)
      hgood
      (selectedOrderedComplexTolerance ε R.index)
      R.regular
      (orderedRemovalDensityFloor_nonneg hξ)
      (orderedRemovalCountingError_nonneg hξ)
      (orderedRemovalCountingError_nonneg hξ)
      (fun _ => le_rfl)
      hcompatible.tolerance_le
      (fun _ =>
        orderedRemovalDefectThreshold_nonneg hξ)
      (fun _ => le_rfl)

theorem fullConfigurationCount_pos_of_removalParameters
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r initialBound : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : StrongOrderedComplexRegularityCertificate
      G k r initial ε budget length)
    (A : ClosedOrderedAtomConfiguration G k r R.fine)
    {ξ : ℝ} (hξ : 0 < ξ)
    (hcompatible :
      IsStrongOrderedRemovalCompatible
        (initialBound := initialBound) R ξ)
    (hgood :
      A.IsGood R.fine R.coarse
        (orderedRemovalAlpha r
          (orderedRemovalFinePartitionComplexityBound
            r initialBound budget length) ξ)
        (orderedRemovalBeta k r
          (orderedRemovalFinePartitionComplexityBound
            r initialBound budget length) ξ)) :
    0 < fullConfigurationCount A := by
  exact
    (orderedRemovalConfigurationLowerBound_pos
      (k := k) (r := r)
      (M := orderedRemovalFinePartitionComplexityBound
        r initialBound budget length) hξ).trans_le
      (R.removalConfigurationLowerBound_le_fullConfigurationCount
        A hξ hcompatible hgood)

end StrongOrderedComplexRegularityCertificate

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

structure NatGrowthFunction where
  toFun : ℕ → ℕ
  monotone' : Monotone toFun
  above_diagonal : ∀ n, n + 1 ≤ toFun n

namespace NatGrowthFunction

instance : CoeFun NatGrowthFunction (fun _ => ℕ → ℕ) :=
  ⟨NatGrowthFunction.toFun⟩

theorem monotone (F : NatGrowthFunction) :
    Monotone F :=
  F.monotone'

theorem positive (F : NatGrowthFunction) (n : ℕ) :
    0 < F n := by
  exact lt_of_lt_of_le (Nat.zero_lt_succ n)
    (F.above_diagonal n)

theorem one_le (F : NatGrowthFunction) (n : ℕ) :
    1 ≤ F n :=
  F.positive n

end NatGrowthFunction

noncomputable def growthRegularityStepTolerance
    (F : NatGrowthFunction) (M : ℕ) : ℝ :=
  1 / (F M : ℝ)

noncomputable def growthRegularityStepBudget
    (k j : ℕ) (F : NatGrowthFunction) (M : ℕ) : ℕ :=
  orderedRemovalRegularityBudget
    k j (growthRegularityStepTolerance F M)

noncomputable def growthRegularityComplexity
    (k j initialBound : ℕ) (F : NatGrowthFunction) :
    ℕ → ℕ
  | 0 => initialBound
  | n + 1 =>
      (2 ^ (j + 1)) ^
          growthRegularityStepBudget
            k j F
              (growthRegularityComplexity
                k j initialBound F n) *
        growthRegularityComplexity
          k j initialBound F n

noncomputable def growthRegularityTolerance
    (k j initialBound : ℕ) (F : NatGrowthFunction) :
    ℕ → ℝ :=
  fun n =>
    growthRegularityStepTolerance F
      (growthRegularityComplexity
        k j initialBound F n)

noncomputable def growthRegularityBudget
    (k j initialBound : ℕ) (F : NatGrowthFunction) :
    ℕ → ℕ :=
  fun n =>
    growthRegularityStepBudget k j F
      (growthRegularityComplexity
        k j initialBound F n)

@[simp]
theorem growthRegularityComplexity_zero
    (k j initialBound : ℕ) (F : NatGrowthFunction) :
    growthRegularityComplexity
      k j initialBound F 0 = initialBound :=
  rfl

@[simp]
theorem growthRegularityComplexity_succ
    (k j initialBound n : ℕ) (F : NatGrowthFunction) :
    growthRegularityComplexity
        k j initialBound F (n + 1) =
      (2 ^ (j + 1)) ^
          growthRegularityBudget
            k j initialBound F n *
        growthRegularityComplexity
          k j initialBound F n :=
  rfl

@[simp]
theorem growthRegularityTolerance_eq
    (k j initialBound n : ℕ) (F : NatGrowthFunction) :
    growthRegularityTolerance
        k j initialBound F n =
      1 /
        (F (growthRegularityComplexity
          k j initialBound F n) : ℝ) :=
  rfl

@[simp]
theorem growthRegularityBudget_eq
    (k j initialBound n : ℕ) (F : NatGrowthFunction) :
    growthRegularityBudget
        k j initialBound F n =
      Nat.ceil
          ((Fintype.card
              (OrderedFace k (j + 1)) : ℝ) /
            (growthRegularityTolerance
              k j initialBound F n) ^ 2) +
        1 :=
  rfl

theorem growthRegularityStepTolerance_pos
    (F : NatGrowthFunction) (M : ℕ) :
    0 < growthRegularityStepTolerance F M := by
  unfold growthRegularityStepTolerance
  exact one_div_pos.mpr
    (by exact_mod_cast F.positive M)

theorem growthRegularityTolerance_pos
    (k j initialBound : ℕ) (F : NatGrowthFunction) :
    ∀ n,
      0 <
        growthRegularityTolerance
          k j initialBound F n := by
  intro n
  exact growthRegularityStepTolerance_pos F
    (growthRegularityComplexity
      k j initialBound F n)

theorem growthRegularityBudget_pos
    (k j initialBound : ℕ) (F : NatGrowthFunction) :
    ∀ n,
      0 <
        growthRegularityBudget
          k j initialBound F n := by
  intro n
  exact orderedRemovalRegularityBudget_pos _ _ _

theorem growthRegularityBudget_spec
    (k j initialBound : ℕ) (F : NatGrowthFunction) :
    ∀ n,
      (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
        (growthRegularityBudget
            k j initialBound F n : ℝ) *
          (growthRegularityTolerance
            k j initialBound F n) ^ 2 := by
  intro n
  exact orderedRemovalRegularityBudget_spec
    (growthRegularityTolerance_pos
      k j initialBound F n)

theorem growthRegularityComplexity_eq_factor_mul
    (k j initialBound : ℕ) (F : NatGrowthFunction) :
    ∀ n,
      growthRegularityComplexity
          k j initialBound F n =
        fixedUpperLayerComplexityFactor
            j (growthRegularityBudget
              k j initialBound F) n *
          initialBound := by
  intro n
  induction n with
  | zero =>
      simp [fixedUpperLayerComplexityFactor]
  | succ n ih =>
      rw [growthRegularityComplexity_succ, ih]
      simp [fixedUpperLayerComplexityFactor,
        Nat.mul_assoc]

theorem growthRegularityComplexity_pos
    {k j initialBound : ℕ} (F : NatGrowthFunction)
    (hinitial : 0 < initialBound) :
    ∀ n,
      0 <
        growthRegularityComplexity
          k j initialBound F n := by
  intro n
  induction n with
  | zero =>
      simpa using hinitial
  | succ n ih =>
      rw [growthRegularityComplexity_succ]
      exact Nat.mul_pos
        (pow_pos (by positivity) _)
        ih

theorem growthRegularityComplexity_monotone
    (k j initialBound : ℕ) (F : NatGrowthFunction) :
    Monotone
      (growthRegularityComplexity
        k j initialBound F) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [growthRegularityComplexity_succ]
  exact Nat.le_mul_of_pos_left _
    (pow_pos (by positivity) _)

noncomputable def growthRegularityLength
    (k j : ℕ) (γ : ℝ) : ℕ :=
  Nat.ceil
      ((Fintype.card
        (OrderedFace k (j + 1)) : ℝ) / γ) +
    1

theorem growthRegularityLength_pos
    (k j : ℕ) (γ : ℝ) :
    0 < growthRegularityLength k j γ := by
  unfold growthRegularityLength
  omega

theorem orderedFace_card_div_growthRegularityLength_lt
    {k j : ℕ} {γ : ℝ} (hγ : 0 < γ) :
    (Fintype.card
        (OrderedFace k (j + 1)) : ℝ) /
        (growthRegularityLength k j γ : ℝ) <
      γ := by
  let A : ℝ :=
    (Fintype.card
      (OrderedFace k (j + 1)) : ℝ)
  let L : ℕ :=
    growthRegularityLength k j γ
  have hLNat : 0 < L :=
    growthRegularityLength_pos k j γ
  have hLCast : (0 : ℝ) < (L : ℝ) := by
    exact_mod_cast hLNat
  have hquot : A / γ < (L : ℝ) := by
    dsimp only [A, L]
    unfold growthRegularityLength
    calc
      (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) / γ ≤
          (Nat.ceil
            ((Fintype.card
              (OrderedFace k (j + 1)) : ℝ) / γ) : ℝ) :=
        Nat.le_ceil _
      _ <
          (Nat.ceil
            ((Fintype.card
              (OrderedFace k (j + 1)) : ℝ) / γ) : ℝ) + 1 := by
        linarith
      _ =
          ((Nat.ceil
            ((Fintype.card
              (OrderedFace k (j + 1)) : ℝ) / γ) + 1 : ℕ) : ℝ) := by
        norm_num
  have hA : A < (L : ℝ) * γ :=
    (div_lt_iff₀ hγ).1 hquot
  apply (div_lt_iff₀ hLCast).2
  simpa [mul_comm] using hA

structure GrowthFunctionFixedUpperCertificate
    (G : Type*) [Fintype G] [DecidableEq G]
    (k j initialBound : ℕ)
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (F : NatGrowthFunction) (γ : ℝ) where
  index : ℕ
  index_lt :
    index < growthRegularityLength k j γ
  coarse : OrderedFacePartitionSystem G k j
  fine : OrderedFacePartitionSystem G k j
  refines : OrderedFacePartitionRefines fine coarse
  coarse_refines_initial :
    OrderedFacePartitionRefines coarse initial
  fine_regular :
    IsPreliminaryOrderedRegular fine upper
      (1 /
        (F (growthRegularityComplexity
          k j initialBound F index) : ℝ))
  gap_nonneg :
    0 ≤
      orderedLayerAtomEnergy fine upper -
        orderedLayerAtomEnergy coarse upper
  gap_le :
    orderedLayerAtomEnergy fine upper -
        orderedLayerAtomEnergy coarse upper ≤ γ
  coarse_complexity :
    ∀ e,
      FacePartition.complexity (coarse e) ≤
        growthRegularityComplexity
          k j initialBound F index
  fine_complexity :
    ∀ e,
      FacePartition.complexity (fine e) ≤
        growthRegularityComplexity
          k j initialBound F (index + 1)

theorem GrowthFunctionFixedUpperCertificate.nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j initialBound : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (F : NatGrowthFunction) {γ : ℝ} (hγ : 0 < γ)
    (hinitial :
      ∀ e,
        FacePartition.complexity (initial e) ≤
          initialBound) :
    Nonempty
      (GrowthFunctionFixedUpperCertificate
        G k j initialBound initial upper F γ) := by
  let τ : ℕ → ℝ :=
    growthRegularityTolerance k j initialBound F
  let B : ℕ → ℕ :=
    growthRegularityBudget k j initialBound F
  let L : ℕ :=
    growthRegularityLength k j γ
  obtain ⟨R⟩ :=
    FixedUpperLayerCoarseFine.nonempty
      initial upper τ B
      (fun n =>
        (growthRegularityTolerance_pos
          k j initialBound F n).le)
      (growthRegularityBudget_spec
        k j initialBound F)
      (growthRegularityLength_pos k j γ)
  refine ⟨{
    index := R.index
    index_lt := R.index_lt
    coarse := R.coarse
    fine := R.fine
    refines := R.refines
    coarse_refines_initial :=
      R.coarse_refines_initial
    fine_regular := ?_
    gap_nonneg := R.gap_nonneg
    gap_le := ?_
    coarse_complexity := ?_
    fine_complexity := ?_ }⟩
  · simpa [τ, growthRegularityTolerance_eq] using
      R.fine_regular
  · exact R.gap_le.trans
      (orderedFace_card_div_growthRegularityLength_lt
        hγ).le
  · intro e
    calc
      FacePartition.complexity (R.coarse e) ≤
          fixedUpperLayerComplexityFactor
              j B R.index *
            FacePartition.complexity (initial e) :=
        R.coarse_complexity e
      _ ≤
          fixedUpperLayerComplexityFactor
              j B R.index *
            initialBound :=
        Nat.mul_le_mul_left _ (hinitial e)
      _ =
          growthRegularityComplexity
            k j initialBound F R.index := by
        rw [growthRegularityComplexity_eq_factor_mul]
  · intro e
    calc
      FacePartition.complexity (R.fine e) ≤
          fixedUpperLayerComplexityFactor
              j B (R.index + 1) *
            FacePartition.complexity (initial e) :=
        R.fine_complexity e
      _ ≤
          fixedUpperLayerComplexityFactor
              j B (R.index + 1) *
            initialBound :=
        Nat.mul_le_mul_left _ (hinitial e)
      _ =
          growthRegularityComplexity
            k j initialBound F (R.index + 1) := by
        rw [growthRegularityComplexity_eq_factor_mul]

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem complexity_orderedPatternInitialComplex_le_two
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ} (H : OrderedPattern G k r) :
    ∀ (j : Fin (r + 1)) (e : OrderedFace k j.1),
      FacePartition.complexity
          ((orderedPatternInitialComplex H).partition j e) ≤ 2 := by
  intro j
  cases j using Fin.lastCases with
  | last =>
      intro e
      change
        FacePartition.complexity
            ((orderedPatternInitialComplex H).topLayer e) ≤ 2
      rw [orderedPatternInitialComplex_topLayer]
      exact complexity_orderedPatternTopPartition_le_two H e
  | cast i =>
      intro e
      simp [orderedPatternInitialComplex,
        indiscreteOrderedPartitionComplex,
        OrderedPartitionComplex.withTopLayer]

structure OrderedRemovalSchedule
    (k r initialBound : ℕ) (ξ : ℝ) where
  tolerance : (j : Fin r) → ℕ → ℝ
  budget : (j : Fin r) → ℕ → ℕ
  length : Fin r → ℕ
  tolerance_pos : ∀ j n, 0 < tolerance j n
  budget_spec :
    ∀ j n,
      (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) <
        (budget j n : ℝ) * (tolerance j n) ^ 2
  length_pos : ∀ j, 0 < length j
  tolerance_le :
    ∀ j n,
      tolerance j n ≤
        orderedRemovalCountingError k r
          (orderedRemovalFinePartitionComplexityBound
            r initialBound budget length) ξ
  reciprocal_gap_le :
    (∑ j : Fin r,
      (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) /
        (length j : ℝ)) ≤
      orderedRemovalEnergyGapTarget k r
        (orderedRemovalFinePartitionComplexityBound
          r initialBound budget length) ξ

def HasOrderedRemovalSchedules
    (k r initialBound : ℕ) : Prop :=
  ∀ ξ : ℝ, 0 < ξ →
    Nonempty (OrderedRemovalSchedule k r initialBound ξ)

namespace OrderedRemovalSchedule

theorem certificateCompatible
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r initialBound : ℕ} {ξ : ℝ}
    {initial : OrderedPartitionComplex G k r}
    (S : OrderedRemovalSchedule k r initialBound ξ)
    (R : StrongOrderedComplexRegularityCertificate
      G k r initial S.tolerance S.budget S.length) :
    IsStrongOrderedRemovalCompatible
      (initialBound := initialBound) R ξ where
  tolerance_le j :=
    S.tolerance_le j (R.index j)
  reciprocal_gap_le :=
    S.reciprocal_gap_le

theorem certificate_nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r initialBound : ℕ} {ξ : ℝ}
    (S : OrderedRemovalSchedule k r initialBound ξ)
    (initial : OrderedPartitionComplex G k r) :
    Nonempty
      (StrongOrderedComplexRegularityCertificate
        G k r initial S.tolerance S.budget S.length) := by
  exact StrongOrderedComplexRegularityCertificate.nonempty
    initial S.tolerance S.budget S.length
    (fun j n => (S.tolerance_pos j n).le)
    S.budget_spec S.length_pos

end OrderedRemovalSchedule

theorem hasUniformOrderedPatternRemoval_succ_of_schedules
    (k n : ℕ) (hrank : n + 1 ≤ k)
    (hschedules :
      HasOrderedRemovalSchedules k (n + 1) 2) :
    HasUniformOrderedPatternRemoval k (n + 1) := by
  intro ξ hξ
  let S : OrderedRemovalSchedule k (n + 1) 2 ξ :=
    Classical.choice (hschedules ξ hξ)
  let M : ℕ :=
    orderedRemovalFinePartitionComplexityBound
      (n + 1) 2 S.budget S.length
  let c : ℝ :=
    orderedRemovalConfigurationLowerBound k (n + 1)
      (orderedRemovalDensityFloor (n + 1) M ξ)
      (orderedRemovalCountingError k (n + 1) M ξ)
      (orderedRemovalCountingError k (n + 1) M ξ)
  have hc : 0 < c := by
    exact orderedRemovalConfigurationLowerBound_pos
      (k := k) (r := n + 1) (M := M) hξ
  refine ⟨c, hc, ?_⟩
  intro G instFintype instDecidableEq instNonempty H hcount
  let initial : OrderedPartitionComplex G k (n + 1) :=
    orderedPatternInitialComplex H
  obtain ⟨R⟩ := S.certificate_nonempty initial
  let P : OrderedCoarseFineComplex G k (n + 1) :=
    R.toCoarseFine
  let α : ℕ → ℝ :=
    orderedRemovalAlpha (n + 1) M ξ
  let β : ℕ → ℝ :=
    orderedRemovalBeta k (n + 1) M ξ
  let D : OrderedPattern.DeletionFamily
      (G := G) k (n + 1) :=
    orderedBadBaseDeletionFamily R.fine R.coarse α β
  have hinitial :
      R.fine.Refines (orderedPatternInitialComplex H) := by
    exact R.fine_refines_initial
  have hcompatible :
      IsStrongOrderedRemovalCompatible
        (initialBound := 2) R ξ :=
    S.certificateCompatible R
  have hcover : H.IsCover D := by
    apply orderedBadBaseDeletionFamily_isCover
      hrank H P hinitial α β
      (selectedOrderedComplexTolerance S.tolerance R.index)
      R.regular
      (orderedRemovalDensityFloor_nonneg hξ)
      (orderedRemovalCountingError_nonneg hξ)
      (orderedRemovalCountingError_nonneg hξ)
      (fun _ => le_rfl)
      hcompatible.tolerance_le
      (fun _ => orderedRemovalDefectThreshold_nonneg hξ)
      (fun _ => le_rfl)
    simpa [c, M, orderedRemovalConfigurationLowerBound,
      orderedRemovalConfigurationFaceCount] using hcount
  refine ⟨D, hcover, ?_⟩
  intro e
  exact R.faceDeletionDensity_badBase_le_removalAllowance
    (complexity_orderedPatternInitialComplex_le_two H)
    hξ hcompatible e

end Erdos3.FixedDensity

end

end OAI
