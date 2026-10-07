-- Modified for ProveIt: `all_goals first | rfl | simp` after each `convert ... using 1` (convert leaves reflexive side goals open in Lean 4.32.0).
import OAI.Combinatorics.Progressions.FixedDensity.OrderedRemovalAssembly

namespace OAI

section

namespace Erdos3.FixedDensity

structure DescendingGrowthHierarchy
    (F : NatGrowthFunction) (depth : ℕ) where
  level : Fin (depth + 1) → ℕ
  step_eq :
    ∀ i : Fin depth,
      level i.castSucc = F (level i.succ)

namespace DescendingGrowthHierarchy

theorem lower_le_growth
    {F : NatGrowthFunction} {depth : ℕ}
    (H : DescendingGrowthHierarchy F depth)
    (i : Fin depth) :
    H.level i.succ ≤ F (H.level i.succ) := by
  exact (Nat.le_succ _).trans
    (F.above_diagonal (H.level i.succ))

theorem growth_eq_upper
    {F : NatGrowthFunction} {depth : ℕ}
    (H : DescendingGrowthHierarchy F depth)
    (i : Fin depth) :
    F (H.level i.succ) = H.level i.castSucc :=
  (H.step_eq i).symm

theorem lower_le_growth_le_upper
    {F : NatGrowthFunction} {depth : ℕ}
    (H : DescendingGrowthHierarchy F depth)
    (i : Fin depth) :
    H.level i.succ ≤ F (H.level i.succ) ∧
      F (H.level i.succ) ≤ H.level i.castSucc := by
  exact ⟨H.lower_le_growth i,
    (H.growth_eq_upper i).le⟩

theorem antitone
    {F : NatGrowthFunction} {depth : ℕ}
    (H : DescendingGrowthHierarchy F depth) :
    Antitone H.level := by
  rw [Fin.antitone_iff_succ_le]
  intro i
  exact (H.lower_le_growth i).trans_eq
    (H.growth_eq_upper i)

end DescendingGrowthHierarchy

def canonicalDescendingGrowthHierarchy
    (F : NatGrowthFunction) (depth bottom : ℕ) :
    DescendingGrowthHierarchy F depth where
  level q :=
    (F.toFun ^[depth - q.1]) bottom
  step_eq := by
    intro i
    have hexponent :
        depth - i.castSucc.1 =
          (depth - i.succ.1) + 1 := by
      simp only [Fin.val_castSucc, Fin.val_succ]
      omega
    rw [hexponent]
    exact Function.iterate_succ_apply'
      F.toFun (depth - i.succ.1) bottom

@[simp]
theorem canonicalDescendingGrowthHierarchy_last
    (F : NatGrowthFunction) (depth bottom : ℕ) :
    (canonicalDescendingGrowthHierarchy
      F depth bottom).level (Fin.last depth) =
        bottom := by
  simp [canonicalDescendingGrowthHierarchy]

@[simp]
theorem canonicalDescendingGrowthHierarchy_zero
    (F : NatGrowthFunction) (depth bottom : ℕ) :
    (canonicalDescendingGrowthHierarchy
      F depth bottom).level 0 =
        (F.toFun ^[depth]) bottom := by
  simp [canonicalDescendingGrowthHierarchy]

noncomputable def growthComplexRegularityTolerance
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction) :
    (j : Fin r) → ℕ → ℝ :=
  fun j =>
    growthRegularityTolerance
      k j.1 (initialBound j.castSucc) F

noncomputable def growthComplexRegularityBudget
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction) :
    (j : Fin r) → ℕ → ℕ :=
  fun j =>
    growthRegularityBudget
      k j.1 (initialBound j.castSucc) F

noncomputable def growthComplexRegularityLength
    (k r : ℕ) (γ : Fin r → ℝ) :
    Fin r → ℕ :=
  fun j =>
    growthRegularityLength k j.1 (γ j)

noncomputable def selectedGrowthCoarseComplexityBound
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (index : Fin r → ℕ)
    (j : Fin r) : ℕ :=
  growthRegularityComplexity
    k j.1 (initialBound j.castSucc) F (index j)

noncomputable def selectedGrowthFineComplexityBound
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (index : Fin r → ℕ)
    (j : Fin r) : ℕ :=
  growthRegularityComplexity
    k j.1 (initialBound j.castSucc) F (index j + 1)

noncomputable def selectedGrowthCoarseLayerComplexityBound
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (index : Fin r → ℕ) :
    Fin (r + 1) → ℕ :=
  Fin.lastCases
    (initialBound (Fin.last r))
    (fun j =>
      selectedGrowthCoarseComplexityBound
        k r initialBound F index j)

noncomputable def selectedGrowthFineLayerComplexityBound
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (index : Fin r → ℕ) :
    Fin (r + 1) → ℕ :=
  Fin.lastCases
    (initialBound (Fin.last r))
    (fun j =>
      selectedGrowthFineComplexityBound
        k r initialBound F index j)

theorem growthComplexRegularityTolerance_pos
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction) :
    ∀ j n,
      0 <
        growthComplexRegularityTolerance
          k r initialBound F j n := by
  intro j n
  exact growthRegularityTolerance_pos
    k j.1 (initialBound j.castSucc) F n

theorem growthComplexRegularityBudget_spec
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction) :
    ∀ j n,
      (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) <
        (growthComplexRegularityBudget
            k r initialBound F j n : ℝ) *
          (growthComplexRegularityTolerance
            k r initialBound F j n) ^ 2 := by
  intro j n
  exact growthRegularityBudget_spec
    k j.1 (initialBound j.castSucc) F n

theorem growthComplexRegularityLength_pos
    (k r : ℕ) (γ : Fin r → ℝ) :
    ∀ j,
      0 <
        growthComplexRegularityLength k r γ j := by
  intro j
  exact growthRegularityLength_pos k j.1 (γ j)

structure GrowthFunctionOrderedComplexRegularityCertificate
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ)
    (initial : OrderedPartitionComplex G k r)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (γ : Fin r → ℝ) where
  index : Fin r → ℕ
  coarse : OrderedPartitionComplex G k r
  fine : OrderedPartitionComplex G k r
  refines : fine.Refines coarse
  coarse_refines_initial : coarse.Refines initial
  coarse_topLayer_eq :
    coarse.topLayer = initial.topLayer
  fine_topLayer_eq :
    fine.topLayer = initial.topLayer
  index_lt :
    ∀ j : Fin r,
      index j <
        growthRegularityLength k j.1 (γ j)
  regular :
    IsFullyPreliminaryOrderedRegular fine
      (fun j =>
        1 /
          (F (selectedGrowthCoarseComplexityBound
            k r initialBound F index j) : ℝ))
  gap_nonneg :
    ∀ j : Fin r,
      0 ≤
        orderedLayerAtomEnergy
            (fine.partition j.castSucc)
            (fine.partition j.succ) -
          orderedLayerAtomEnergy
            (coarse.partition j.castSucc)
            (fine.partition j.succ)
  gap_le :
    ∀ j : Fin r,
      orderedLayerAtomEnergy
            (fine.partition j.castSucc)
            (fine.partition j.succ) -
          orderedLayerAtomEnergy
            (coarse.partition j.castSucc)
            (fine.partition j.succ) ≤
        γ j
  coarse_complexity :
    ∀ (q : Fin (r + 1)) (e : OrderedFace k q.1),
      FacePartition.complexity
          (coarse.partition q e) ≤
        selectedGrowthCoarseLayerComplexityBound
          k r initialBound F index q
  fine_complexity :
    ∀ (q : Fin (r + 1)) (e : OrderedFace k q.1),
      FacePartition.complexity
          (fine.partition q e) ≤
        selectedGrowthFineLayerComplexityBound
          k r initialBound F index q

namespace GrowthFunctionOrderedComplexRegularityCertificate

def localCertificate
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) :
    GrowthFunctionFixedUpperCertificate
      G k j.1 (initialBound j.castSucc)
      (initial.partition j.castSucc)
      (R.fine.partition j.succ)
      F (γ j) where
  index := R.index j
  index_lt := R.index_lt j
  coarse := R.coarse.partition j.castSucc
  fine := R.fine.partition j.castSucc
  refines := R.refines j.castSucc
  coarse_refines_initial :=
    R.coarse_refines_initial j.castSucc
  fine_regular := by
    simpa [selectedGrowthCoarseComplexityBound] using
      R.regular j
  gap_nonneg := R.gap_nonneg j
  gap_le := R.gap_le j
  coarse_complexity := by
    intro e
    have h := R.coarse_complexity j.castSucc e
    simp only [selectedGrowthCoarseLayerComplexityBound,
      selectedGrowthCoarseComplexityBound,
      Fin.lastCases_castSucc] at h
    convert h using 1
    all_goals first | rfl | simp
  fine_complexity := by
    intro e
    have h := R.fine_complexity j.castSucc e
    simp only [selectedGrowthFineLayerComplexityBound,
      selectedGrowthFineComplexityBound,
      Fin.lastCases_castSucc] at h
    convert h using 1
    all_goals first | rfl | simp

theorem coarse_upper_complexity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) (e : OrderedFace k (j.1 + 1)) :
    FacePartition.complexity
        (R.coarse.partition j.succ e) ≤
      selectedGrowthCoarseLayerComplexityBound
        k r initialBound F R.index j.succ :=
  R.coarse_complexity j.succ e

theorem fine_upper_complexity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) (e : OrderedFace k (j.1 + 1)) :
    FacePartition.complexity
        (R.fine.partition j.succ e) ≤
      selectedGrowthFineLayerComplexityBound
        k r initialBound F R.index j.succ :=
  R.fine_complexity j.succ e

end GrowthFunctionOrderedComplexRegularityCertificate

theorem GrowthFunctionOrderedComplexRegularityCertificate.nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (γ : Fin r → ℝ)
    (hγ : ∀ j, 0 < γ j)
    (hinitial :
      ∀ (q : Fin (r + 1)) (e : OrderedFace k q.1),
        FacePartition.complexity
          (initial.partition q e) ≤ initialBound q) :
    Nonempty
      (GrowthFunctionOrderedComplexRegularityCertificate
        G k r initial initialBound F γ) := by
  let τ : (j : Fin r) → ℕ → ℝ :=
    growthComplexRegularityTolerance
      k r initialBound F
  let B : (j : Fin r) → ℕ → ℕ :=
    growthComplexRegularityBudget
      k r initialBound F
  let L : Fin r → ℕ :=
    growthComplexRegularityLength k r γ
  obtain ⟨R⟩ :=
    StrongOrderedComplexRegularityCertificate.nonempty
      initial τ B L
      (fun j n =>
        (growthComplexRegularityTolerance_pos
          k r initialBound F j n).le)
      (growthComplexRegularityBudget_spec
        k r initialBound F)
      (growthComplexRegularityLength_pos k r γ)
  refine ⟨{
    index := R.index
    coarse := R.coarse
    fine := R.fine
    refines := R.refines
    coarse_refines_initial :=
      R.coarse_refines_initial
    coarse_topLayer_eq := R.coarse_topLayer_eq
    fine_topLayer_eq := R.fine_topLayer_eq
    index_lt := ?_
    regular := ?_
    gap_nonneg := R.gap_nonneg
    gap_le := ?_
    coarse_complexity := ?_
    fine_complexity := ?_ }⟩
  · intro j
    simpa [L, growthComplexRegularityLength] using
      R.index_lt j
  · intro j
    have hregular := R.regular j
    simpa [τ, growthComplexRegularityTolerance,
      selectedOrderedComplexTolerance,
      selectedGrowthCoarseComplexityBound,
      growthRegularityTolerance_eq] using hregular
  · intro j
    exact (R.gap_le j).trans
      (by
        simpa [L, growthComplexRegularityLength] using
          (orderedFace_card_div_growthRegularityLength_lt
            (hγ j)).le)
  · intro q
    cases q using Fin.lastCases with
    | last =>
        intro e
        have htop := congrFun R.coarse_topLayer_eq e
        simp only [OrderedPartitionComplex.topLayer] at htop
        rw [htop]
        simpa [selectedGrowthCoarseLayerComplexityBound] using
          hinitial (Fin.last r) e
    | cast i =>
        intro e
        have hcomplexity := R.coarse_complexity i e
        calc
          FacePartition.complexity
              (R.coarse.partition i.castSucc e) ≤
              fixedUpperLayerComplexityFactor
                  i.1 (B i) (R.index i) *
                FacePartition.complexity
                  (initial.partition i.castSucc e) := by
            simpa [B, growthComplexRegularityBudget] using
              hcomplexity
          _ ≤
              fixedUpperLayerComplexityFactor
                  i.1 (B i) (R.index i) *
                initialBound i.castSucc :=
            Nat.mul_le_mul_left _
              (hinitial i.castSucc e)
          _ =
              selectedGrowthCoarseLayerComplexityBound
                k r initialBound F R.index i.castSucc := by
            simp only [
              selectedGrowthCoarseLayerComplexityBound,
              selectedGrowthCoarseComplexityBound,
              Fin.lastCases_castSucc]
            rw [growthRegularityComplexity_eq_factor_mul]
            rfl
  · intro q
    cases q using Fin.lastCases with
    | last =>
        intro e
        have htop := congrFun R.fine_topLayer_eq e
        simp only [OrderedPartitionComplex.topLayer] at htop
        rw [htop]
        simpa [selectedGrowthFineLayerComplexityBound] using
          hinitial (Fin.last r) e
    | cast i =>
        intro e
        have hcomplexity := R.fine_complexity i e
        calc
          FacePartition.complexity
              (R.fine.partition i.castSucc e) ≤
              fixedUpperLayerComplexityFactor
                  i.1 (B i) (R.index i + 1) *
                FacePartition.complexity
                  (initial.partition i.castSucc e) := by
            simpa [B, growthComplexRegularityBudget] using
              hcomplexity
          _ ≤
              fixedUpperLayerComplexityFactor
                  i.1 (B i) (R.index i + 1) *
                initialBound i.castSucc :=
            Nat.mul_le_mul_left _
              (hinitial i.castSucc e)
          _ =
              selectedGrowthFineLayerComplexityBound
                k r initialBound F R.index i.castSucc := by
            simp only [
              selectedGrowthFineLayerComplexityBound,
              selectedGrowthFineComplexityBound,
              Fin.lastCases_castSucc]
            rw [growthRegularityComplexity_eq_factor_mul]
            rfl

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

noncomputable def growthRegularityOneStep
    (k j : ℕ) (F : NatGrowthFunction) (M : ℕ) : ℕ :=
  (2 ^ (j + 1)) ^
      growthRegularityStepBudget k j F M * M

@[simp]
theorem growthRegularityComplexity_succ_eq_oneStep
    (k j initialBound n : ℕ) (F : NatGrowthFunction) :
    growthRegularityComplexity
        k j initialBound F (n + 1) =
      growthRegularityOneStep k j F
        (growthRegularityComplexity
          k j initialBound F n) :=
  rfl

noncomputable def boundedGrowthRegularityOneStepMaximum
    (k j : ℕ) (F : NatGrowthFunction) : ℕ → ℕ
  | 0 => growthRegularityOneStep k j F 0
  | M + 1 =>
      max
        (boundedGrowthRegularityOneStepMaximum k j F M)
        (growthRegularityOneStep k j F (M + 1))

theorem growthRegularityOneStep_le_boundedMaximum
    (k j : ℕ) (F : NatGrowthFunction)
    {m M : ℕ} (hm : m ≤ M) :
    growthRegularityOneStep k j F m ≤
      boundedGrowthRegularityOneStepMaximum k j F M := by
  induction M generalizing m with
  | zero =>
      have hmzero : m = 0 := Nat.eq_zero_of_le_zero hm
      subst m
      rfl
  | succ M ih =>
      rw [boundedGrowthRegularityOneStepMaximum]
      by_cases hlast : m = M + 1
      · subst m
        exact le_max_right _ _
      · have hmM : m ≤ M := by omega
        exact (ih hmM).trans (le_max_left _ _)

theorem boundedGrowthRegularityOneStepMaximum_monotone
    (k j : ℕ) (F : NatGrowthFunction) :
    Monotone
      (boundedGrowthRegularityOneStepMaximum k j F) := by
  apply monotone_nat_of_le_succ
  intro M
  rw [boundedGrowthRegularityOneStepMaximum]
  exact le_max_left _ _

noncomputable def finiteRankGrowthRegularityOneStepMaximum
    (k : ℕ) (F : NatGrowthFunction) (M : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 =>
      max
        (finiteRankGrowthRegularityOneStepMaximum k F M r)
        (boundedGrowthRegularityOneStepMaximum k r F M)

theorem growthRegularityOneStep_le_finiteRankMaximum
    (k : ℕ) (F : NatGrowthFunction)
    {j r m M : ℕ} (hj : j < r) (hm : m ≤ M) :
    growthRegularityOneStep k j F m ≤
      finiteRankGrowthRegularityOneStepMaximum k F M r := by
  induction r generalizing j with
  | zero =>
      omega
  | succ r ih =>
      rw [finiteRankGrowthRegularityOneStepMaximum]
      by_cases hjlast : j = r
      · subst j
        exact
          (growthRegularityOneStep_le_boundedMaximum
            k r F hm).trans (le_max_right _ _)
      · have hjr : j < r := by omega
        exact (ih hjr).trans (le_max_left _ _)

theorem finiteRankGrowthRegularityOneStepMaximum_monotone
    (k r : ℕ) (F : NatGrowthFunction) :
    Monotone
      (fun M =>
        finiteRankGrowthRegularityOneStepMaximum
          k F M r) := by
  intro a b hab
  induction r with
  | zero =>
      simp [finiteRankGrowthRegularityOneStepMaximum]
  | succ r ih =>
      simp only [finiteRankGrowthRegularityOneStepMaximum]
      exact max_le_max ih
        (boundedGrowthRegularityOneStepMaximum_monotone
          k r F hab)

noncomputable def towerDominatingGrowth
    (k r : ℕ) (F : NatGrowthFunction) :
    NatGrowthFunction where
  toFun M :=
    max (M + 1)
      (max (F M)
        (finiteRankGrowthRegularityOneStepMaximum
          k F M r))
  monotone' := by
    intro a b hab
    exact max_le_max
      (Nat.add_le_add_right hab 1)
      (max_le_max
        (F.monotone hab)
        (finiteRankGrowthRegularityOneStepMaximum_monotone
          k r F hab))
  above_diagonal := by
    intro M
    exact le_max_left _ _

@[simp]
theorem towerDominatingGrowth_apply
    (k r : ℕ) (F : NatGrowthFunction) (M : ℕ) :
    towerDominatingGrowth k r F M =
      max (M + 1)
        (max (F M)
          (finiteRankGrowthRegularityOneStepMaximum
            k F M r)) :=
  rfl

theorem le_towerDominatingGrowth
    (k r : ℕ) (F : NatGrowthFunction) (M : ℕ) :
    F M ≤ towerDominatingGrowth k r F M := by
  rw [towerDominatingGrowth_apply]
  exact (le_max_left _ _).trans (le_max_right _ _)

theorem growthFunction_le_towerDominatingGrowth_of_le
    (k r : ℕ) (F : NatGrowthFunction)
    {m M : ℕ} (hm : m ≤ M) :
    F m ≤ towerDominatingGrowth k r F M := by
  exact (F.monotone hm).trans
    (le_towerDominatingGrowth k r F M)

theorem growthRegularityOneStep_le_towerDominatingGrowth
    (k r : ℕ) (F : NatGrowthFunction)
    (j : Fin r) {m M : ℕ} (hm : m ≤ M) :
    growthRegularityOneStep k j.1 F m ≤
      towerDominatingGrowth k r F M := by
  rw [towerDominatingGrowth_apply]
  exact
    (growthRegularityOneStep_le_finiteRankMaximum
      k F j.isLt hm).trans
      ((le_max_right _ _).trans (le_max_right _ _))

noncomputable def towerDominatingGrowthIteration
    (k r : ℕ) (F : NatGrowthFunction) :
    ℕ → NatGrowthFunction
  | 0 => F
  | stage + 1 =>
      towerDominatingGrowth k r
        (towerDominatingGrowthIteration k r F stage)

@[simp]
theorem towerDominatingGrowthIteration_zero
    (k r : ℕ) (F : NatGrowthFunction) :
    towerDominatingGrowthIteration k r F 0 = F :=
  rfl

@[simp]
theorem towerDominatingGrowthIteration_succ
    (k r : ℕ) (F : NatGrowthFunction) (stage : ℕ) :
    towerDominatingGrowthIteration k r F (stage + 1) =
      towerDominatingGrowth k r
        (towerDominatingGrowthIteration k r F stage) :=
  rfl

theorem le_towerDominatingGrowthIteration
    (k r : ℕ) (F : NatGrowthFunction) :
    ∀ stage M,
      F M ≤ towerDominatingGrowthIteration k r F stage M := by
  intro stage
  induction stage with
  | zero =>
      intro M
      exact le_rfl
  | succ stage ih =>
      intro M
      exact (ih M).trans
        (le_towerDominatingGrowth k r
          (towerDominatingGrowthIteration k r F stage) M)

theorem towerDominatingGrowthIteration_le_succ
    (k r : ℕ) (F : NatGrowthFunction)
    (stage M : ℕ) :
    towerDominatingGrowthIteration k r F stage M ≤
      towerDominatingGrowthIteration k r F (stage + 1) M := by
  exact le_towerDominatingGrowth k r
    (towerDominatingGrowthIteration k r F stage) M

theorem growthRegularityOneStep_le_nextGrowthIteration
    (k r : ℕ) (F : NatGrowthFunction)
    (stage : ℕ) (j : Fin r) {m M : ℕ} (hm : m ≤ M) :
    growthRegularityOneStep k j.1
        (towerDominatingGrowthIteration k r F stage) m ≤
      towerDominatingGrowthIteration k r F (stage + 1) M := by
  exact growthRegularityOneStep_le_towerDominatingGrowth
    k r
    (towerDominatingGrowthIteration k r F stage)
    j hm

theorem growthRegularityComplexity_succ_le_nextGrowthIteration
    (k r initialBound : ℕ) (F : NatGrowthFunction)
    (stage n : ℕ) (j : Fin r) :
    growthRegularityComplexity
        k j.1 initialBound
          (towerDominatingGrowthIteration k r F stage)
          (n + 1) ≤
      towerDominatingGrowthIteration k r F (stage + 1)
        (growthRegularityComplexity
          k j.1 initialBound
            (towerDominatingGrowthIteration k r F stage)
            n) := by
  rw [growthRegularityComplexity_succ_eq_oneStep]
  exact growthRegularityOneStep_le_nextGrowthIteration
    k r F stage j le_rfl

theorem towerDominatingGrowthIteration_reciprocal_le
    (k r : ℕ) (F : NatGrowthFunction)
    (stage M : ℕ) :
    1 /
        (towerDominatingGrowthIteration
          k r F stage M : ℝ) ≤
      1 / (F M : ℝ) := by
  apply one_div_le_one_div_of_le
  · exact_mod_cast F.positive M
  · exact_mod_cast
      le_towerDominatingGrowthIteration
        k r F stage M

def finiteMaximum : (n : ℕ) → (Fin n → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, value =>
      max
        (finiteMaximum n (fun i => value i.castSucc))
        (value (Fin.last n))

theorem le_finiteMaximum :
    ∀ {n : ℕ} (value : Fin n → ℕ) (i : Fin n),
      value i ≤ finiteMaximum n value
  | 0, _, i => Fin.elim0 i
  | n + 1, value, i => by
      cases i using Fin.lastCases with
      | last =>
          rw [finiteMaximum]
          exact le_max_right _ _
      | cast i =>
          rw [finiteMaximum]
          exact
            (le_finiteMaximum
              (fun q => value q.castSucc) i).trans
              (le_max_left _ _)

namespace GrowthFunctionOrderedComplexRegularityCertificate

theorem selectedFineComplexity_le_nextGrowthIteration
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ)
    (j : Fin r) :
    selectedGrowthFineComplexityBound
        k r initialBound
          (towerDominatingGrowthIteration k r F stage)
          R.index j ≤
      towerDominatingGrowthIteration k r F (stage + 1)
        (selectedGrowthCoarseComplexityBound
          k r initialBound
            (towerDominatingGrowthIteration k r F stage)
            R.index j) := by
  exact growthRegularityComplexity_succ_le_nextGrowthIteration
    k r (initialBound j.castSucc) F stage (R.index j) j

theorem regular_with_requestedGrowth
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ) :
    IsFullyPreliminaryOrderedRegular R.fine
      (fun j =>
        1 /
          (F (selectedGrowthCoarseComplexityBound
            k r initialBound
              (towerDominatingGrowthIteration k r F stage)
              R.index j) : ℝ)) := by
  intro j e a b
  exact (R.regular j e a b).trans
    (towerDominatingGrowthIteration_reciprocal_le
      k r F stage
      (selectedGrowthCoarseComplexityBound
        k r initialBound
          (towerDominatingGrowthIteration k r F stage)
          R.index j))

noncomputable def selectedRankTowerHierarchy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ)
    (j : Fin r) :
    DescendingGrowthHierarchy
      (towerDominatingGrowthIteration k r F (stage + 1)) 1 :=
  canonicalDescendingGrowthHierarchy
    (towerDominatingGrowthIteration k r F (stage + 1)) 1
    (selectedGrowthCoarseComplexityBound
      k r initialBound
        (towerDominatingGrowthIteration k r F stage)
        R.index j)

@[simp]
theorem selectedRankTowerHierarchy_last
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ)
    (j : Fin r) :
    (selectedRankTowerHierarchy R j).level (Fin.last 1) =
      selectedGrowthCoarseComplexityBound
        k r initialBound
          (towerDominatingGrowthIteration k r F stage)
          R.index j := by
  exact canonicalDescendingGrowthHierarchy_last
    (towerDominatingGrowthIteration k r F (stage + 1)) 1
    (selectedGrowthCoarseComplexityBound
      k r initialBound
        (towerDominatingGrowthIteration k r F stage)
        R.index j)

@[simp]
theorem selectedRankTowerHierarchy_zero
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ)
    (j : Fin r) :
    (selectedRankTowerHierarchy R j).level 0 =
      towerDominatingGrowthIteration k r F (stage + 1)
        (selectedGrowthCoarseComplexityBound
          k r initialBound
            (towerDominatingGrowthIteration k r F stage)
            R.index j) := by
  simp [selectedRankTowerHierarchy]

theorem selectedFineComplexity_le_selectedRankTowerHierarchy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ)
    (j : Fin r) :
    selectedGrowthFineComplexityBound
        k r initialBound
          (towerDominatingGrowthIteration k r F stage)
          R.index j ≤
      (selectedRankTowerHierarchy R j).level 0 := by
  rw [selectedRankTowerHierarchy_zero]
  exact R.selectedFineComplexity_le_nextGrowthIteration j

theorem finePartitionComplexity_le_selectedRankTowerHierarchy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ)
    (j : Fin r) (e : OrderedFace k j.1) :
    FacePartition.complexity
        (R.fine.partition j.castSucc e) ≤
      (selectedRankTowerHierarchy R j).level 0 := by
  exact
    ((R.localCertificate j).fine_complexity e).trans
      (R.selectedFineComplexity_le_selectedRankTowerHierarchy j)

noncomputable def selectedFineLayerMaximum
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ) : ℕ :=
  finiteMaximum (r + 1)
    (selectedGrowthFineLayerComplexityBound
      k r initialBound
        (towerDominatingGrowthIteration k r F stage)
        R.index)

noncomputable def selectedAllRankTowerHierarchy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ) :
    DescendingGrowthHierarchy
      (towerDominatingGrowthIteration k r F (stage + 1)) r :=
  canonicalDescendingGrowthHierarchy
    (towerDominatingGrowthIteration k r F (stage + 1)) r
    (selectedFineLayerMaximum R)

@[simp]
theorem selectedAllRankTowerHierarchy_last
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ) :
    (selectedAllRankTowerHierarchy R).level (Fin.last r) =
      selectedFineLayerMaximum R := by
  exact canonicalDescendingGrowthHierarchy_last
    (towerDominatingGrowthIteration k r F (stage + 1)) r
    (selectedFineLayerMaximum R)

theorem selectedFineLayerComplexity_le_allRankTowerHierarchy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ)
    (q : Fin (r + 1)) :
    selectedGrowthFineLayerComplexityBound
        k r initialBound
          (towerDominatingGrowthIteration k r F stage)
          R.index q ≤
      (selectedAllRankTowerHierarchy R).level q := by
  calc
    selectedGrowthFineLayerComplexityBound
          k r initialBound
            (towerDominatingGrowthIteration k r F stage)
            R.index q ≤
        selectedFineLayerMaximum R := by
          exact le_finiteMaximum _ q
    _ =
        (selectedAllRankTowerHierarchy R).level
          (Fin.last r) := by
          symm
          exact selectedAllRankTowerHierarchy_last R
    _ ≤
        (selectedAllRankTowerHierarchy R).level q := by
          exact (selectedAllRankTowerHierarchy R).antitone
            (Fin.le_last q)

theorem fineComplexity_le_allRankTowerHierarchy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ)
    (q : Fin (r + 1)) (e : OrderedFace k q.1) :
    FacePartition.complexity
        (R.fine.partition q e) ≤
      (selectedAllRankTowerHierarchy R).level q := by
  exact (R.fine_complexity q e).trans
    (R.selectedFineLayerComplexity_le_allRankTowerHierarchy q)

end GrowthFunctionOrderedComplexRegularityCertificate

end Erdos3.FixedDensity

end

end OAI
