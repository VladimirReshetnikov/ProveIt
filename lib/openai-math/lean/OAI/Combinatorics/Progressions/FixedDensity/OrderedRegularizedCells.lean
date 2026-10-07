-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import OAI.Combinatorics.Progressions.FixedDensity.OrderedCounting
import OAI.Compat.BigOperators

namespace OAI

section

namespace Erdos3.FixedDensity

def indiscreteOrderedRegularitySystem
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ) :
    OrderedRegularitySystem G k r :=
  fun _ => ⟨FacePartition.indiscrete⟩

@[simp]
theorem indiscreteOrderedRegularitySystem_partition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (e : OrderedFace k r) :
    (indiscreteOrderedRegularitySystem G k r e).partition =
      FacePartition.indiscrete :=
  rfl

structure GeneratedOrderedPatternRegularization
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ)
    (H : WeightedOrderedPattern G k r)
    (ε : ℝ) where
  state : OrderedRegularitySystem G k r
  generators :
    (e : OrderedFace k r) →
      Finset (BooleanCutTest (Fin r → G))
  budgetLength : OrderedFace k r → ℕ
  stepIndex : OrderedFace k r → ℕ
  budget_large :
    ∀ e, 1 < (budgetLength e : ℝ) * ε ^ 2
  step_lt_budget :
    ∀ e, stepIndex e < budgetLength e
  partition_eq_generated :
    ∀ e, (state e).partition =
      FacePartition.generatedBy (generators e)
  generators_supported :
    ∀ e, generators e ⊆ booleanFaceCutSupports G r
  generator_card_le :
    ∀ e, (generators e).card ≤ stepIndex e
  regular :
    ∀ e, (state e).IsFaceCutRegular
      (H.edgeWeight e) ε
  count_close :
    |H.patternCount -
        (regularizedOrderedPattern H state).patternCount| ≤
      (Fintype.card (OrderedFace k r) : ℝ) * ε
  complexity_le :
    ∀ e, FacePartition.complexity (state e).partition ≤
      2 ^ stepIndex e

theorem exists_generatedOrderedPatternRegularization
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ} (hr : 0 < r)
    (H : WeightedOrderedPattern G k r)
    (hH : H.EdgeWeightsInUnitInterval)
    {ε : ℝ} (hε : 0 < ε) :
    Nonempty
      (GeneratedOrderedPatternRegularization
        G k r H ε) := by
  classical
  let S₀ :=
    indiscreteOrderedRegularitySystem G k r
  have he (e : OrderedFace k r) :
      ∃ m i : ℕ,
        ∃ T : FaceRegularityState (Fin r → G),
        ∃ F : Finset (BooleanCutTest (Fin r → G)),
          1 < (m : ℝ) * ε ^ 2 ∧
          i < m ∧
          T.partition =
            FacePartition.join (S₀ e).partition
              (FacePartition.generatedBy F) ∧
          F ⊆ booleanFaceCutSupports G r ∧
          F.card ≤ i ∧
          T.IsFaceCutRegular (H.edgeWeight e) ε ∧
          FacePartition.complexity T.partition ≤
            2 ^ i *
              FacePartition.complexity
                (S₀ e).partition := by
    exact
      (S₀ e).exists_faceCutRegular_refinement_with_generators
        hr (H.edgeWeight e)
        (fun y => (hH e y).1)
        (fun y => (hH e y).2) hε
  choose m i S F hdata using he
  have hbudget :
      ∀ e, 1 < (m e : ℝ) * ε ^ 2 :=
    fun e => (hdata e).1
  have hstep :
      ∀ e, i e < m e :=
    fun e => (hdata e).2.1
  have hpartition :
      ∀ e, (S e).partition =
        FacePartition.generatedBy (F e) := by
    intro e
    have h := (hdata e).2.2.1
    simpa [S₀, indiscreteOrderedRegularitySystem,
      FacePartition.join, FacePartition.indiscrete] using h
  have hsupported :
      ∀ e, F e ⊆ booleanFaceCutSupports G r :=
    fun e => (hdata e).2.2.2.1
  have hcard :
      ∀ e, (F e).card ≤ i e :=
    fun e => (hdata e).2.2.2.2.1
  have hregular :
      ∀ e, (S e).IsFaceCutRegular
        (H.edgeWeight e) ε :=
    fun e => (hdata e).2.2.2.2.2.1
  have hcomplexity :
      ∀ e, FacePartition.complexity (S e).partition ≤
        2 ^ i e := by
    intro e
    have h := (hdata e).2.2.2.2.2.2
    simpa [S₀, indiscreteOrderedRegularitySystem] using h
  exact
    ⟨{
      state := S
      generators := F
      budgetLength := m
      stepIndex := i
      budget_large := hbudget
      step_lt_budget := hstep
      partition_eq_generated := hpartition
      generators_supported := hsupported
      generator_card_le := hcard
      regular := hregular
      count_close :=
        patternCount_abs_sub_regularizedOrderedPattern_le
          H hH S hregular
      complexity_le := hcomplexity
    }⟩

theorem exists_generatedOrderedPatternRegularization_before
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ} (hr : 0 < r)
    (H : WeightedOrderedPattern G k r)
    (hH : H.EdgeWeightsInUnitInterval)
    {ε : ℝ} {m : ℕ}
    (hε : 0 ≤ ε)
    (hlong : 1 < (m : ℝ) * ε ^ 2) :
    ∃ R : GeneratedOrderedPatternRegularization
        G k r H ε,
      ∀ e, R.stepIndex e < m := by
  classical
  let S₀ :=
    indiscreteOrderedRegularitySystem G k r
  have he (e : OrderedFace k r) :
      ∃ i : ℕ,
        ∃ T : FaceRegularityState (Fin r → G),
        ∃ F : Finset (BooleanCutTest (Fin r → G)),
          i < m ∧
          T.partition =
            FacePartition.join (S₀ e).partition
              (FacePartition.generatedBy F) ∧
          F ⊆ booleanFaceCutSupports G r ∧
          F.card ≤ i ∧
          T.IsFaceCutRegular (H.edgeWeight e) ε ∧
          FacePartition.complexity T.partition ≤
            2 ^ i *
              FacePartition.complexity
                (S₀ e).partition := by
    exact
      (S₀ e).exists_faceCutRegular_refinement_with_generators_before
        hr (H.edgeWeight e)
        (fun y => (hH e y).1)
        (fun y => (hH e y).2)
        hε hlong
  choose i S F hdata using he
  have hpartition :
      ∀ e, (S e).partition =
        FacePartition.generatedBy (F e) := by
    intro e
    have h := (hdata e).2.1
    simpa [S₀, indiscreteOrderedRegularitySystem,
      FacePartition.join, FacePartition.indiscrete] using h
  have hsupported :
      ∀ e, F e ⊆ booleanFaceCutSupports G r :=
    fun e => (hdata e).2.2.1
  have hcard :
      ∀ e, (F e).card ≤ i e :=
    fun e => (hdata e).2.2.2.1
  have hregular :
      ∀ e, (S e).IsFaceCutRegular
        (H.edgeWeight e) ε :=
    fun e => (hdata e).2.2.2.2.1
  have hcomplexity :
      ∀ e, FacePartition.complexity (S e).partition ≤
        2 ^ i e := by
    intro e
    have h := (hdata e).2.2.2.2.2
    simpa [S₀, indiscreteOrderedRegularitySystem] using h
  let R : GeneratedOrderedPatternRegularization
      G k r H ε := {
    state := S
    generators := F
    budgetLength := fun _ => m
    stepIndex := i
    budget_large := fun _ => hlong
    step_lt_budget := fun e => (hdata e).1
    partition_eq_generated := hpartition
    generators_supported := hsupported
    generator_card_le := hcard
    regular := hregular
    count_close :=
      patternCount_abs_sub_regularizedOrderedPattern_le
        H hH S hregular
    complexity_le := hcomplexity
  }
  exact ⟨R, fun e => (hdata e).1⟩

namespace GeneratedOrderedPatternRegularization

theorem exists_refinement_before
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε η : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε)
    (hr : 0 < r)
    (hH : H.EdgeWeightsInUnitInterval)
    {m : ℕ} (hη : 0 ≤ η)
    (hlong : 1 < (m : ℝ) * η ^ 2) :
    ∃ T : GeneratedOrderedPatternRegularization
        G k r H η,
      (∀ e, (T.state e).partition ≤
        (R.state e).partition) ∧
      (∀ e, R.generators e ⊆ T.generators e) ∧
      ∀ e, T.stepIndex e < R.stepIndex e + m := by
  classical
  have he (e : OrderedFace k r) :
      ∃ i : ℕ,
        ∃ S : FaceRegularityState (Fin r → G),
        ∃ F : Finset (BooleanCutTest (Fin r → G)),
          i < m ∧
          S.partition =
            FacePartition.join (R.state e).partition
              (FacePartition.generatedBy F) ∧
          F ⊆ booleanFaceCutSupports G r ∧
          F.card ≤ i ∧
          S.IsFaceCutRegular (H.edgeWeight e) η ∧
          FacePartition.complexity S.partition ≤
            2 ^ i *
              FacePartition.complexity
                (R.state e).partition := by
    exact
      (R.state e).exists_faceCutRegular_refinement_with_generators_before
        hr (H.edgeWeight e)
        (fun y => (hH e y).1)
        (fun y => (hH e y).2)
        hη hlong
  choose i S F hdata using he
  let U :
      (e : OrderedFace k r) →
        Finset (BooleanCutTest (Fin r → G)) :=
    fun e => R.generators e ∪ F e
  have hbudget :
      ∀ e,
        1 <
          ((R.stepIndex e + m : ℕ) : ℝ) * η ^ 2 := by
    intro e
    have hm :
        (m : ℝ) ≤ ((R.stepIndex e + m : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_left m (R.stepIndex e)
    exact hlong.trans_le
      (mul_le_mul_of_nonneg_right hm (sq_nonneg η))
  have hstep :
      ∀ e,
        R.stepIndex e + i e <
          R.stepIndex e + m :=
    fun e => Nat.add_lt_add_left (hdata e).1 _
  have hpartition :
      ∀ e, (S e).partition =
        FacePartition.generatedBy (U e) := by
    intro e
    calc
      (S e).partition =
          FacePartition.join (R.state e).partition
            (FacePartition.generatedBy (F e)) :=
        (hdata e).2.1
      _ =
          FacePartition.join
            (FacePartition.generatedBy (R.generators e))
            (FacePartition.generatedBy (F e)) := by
        rw [R.partition_eq_generated e]
      _ = FacePartition.generatedBy (U e) := by
        exact
          (FacePartition.generatedBy_union
            (R.generators e) (F e)).symm
  have hsupported :
      ∀ e, U e ⊆ booleanFaceCutSupports G r := by
    intro e
    exact Finset.union_subset
      (R.generators_supported e)
      (hdata e).2.2.1
  have hcard :
      ∀ e, (U e).card ≤ R.stepIndex e + i e := by
    intro e
    calc
      (U e).card ≤
          (R.generators e).card + (F e).card :=
        by
          change
            (R.generators e ∪ F e).card ≤
              (R.generators e).card + (F e).card
          exact Finset.card_union_le
            (R.generators e) (F e)
      _ ≤ R.stepIndex e + i e :=
        Nat.add_le_add
          (R.generator_card_le e)
          (hdata e).2.2.2.1
  have hregular :
      ∀ e, (S e).IsFaceCutRegular
        (H.edgeWeight e) η :=
    fun e => (hdata e).2.2.2.2.1
  have hcomplexity :
      ∀ e, FacePartition.complexity (S e).partition ≤
        2 ^ (R.stepIndex e + i e) := by
    intro e
    calc
      FacePartition.complexity (S e).partition ≤
          2 ^ i e *
            FacePartition.complexity
              (R.state e).partition :=
        (hdata e).2.2.2.2.2
      _ ≤ 2 ^ i e * 2 ^ R.stepIndex e :=
        Nat.mul_le_mul_left _ (R.complexity_le e)
      _ = 2 ^ (R.stepIndex e + i e) := by
        simp [pow_add, Nat.mul_comm]
  let T : GeneratedOrderedPatternRegularization
      G k r H η := {
    state := S
    generators := U
    budgetLength := fun e => R.stepIndex e + m
    stepIndex := fun e => R.stepIndex e + i e
    budget_large := hbudget
    step_lt_budget := hstep
    partition_eq_generated := hpartition
    generators_supported := hsupported
    generator_card_le := hcard
    regular := hregular
    count_close :=
      patternCount_abs_sub_regularizedOrderedPattern_le
        H hH S hregular
    complexity_le := hcomplexity
  }
  refine ⟨T, ?_, ?_, ?_⟩
  · intro e
    change (S e).partition ≤ (R.state e).partition
    rw [(hdata e).2.1]
    exact FacePartition.join_le_left _ _
  · intro e
    change R.generators e ⊆ U e
    exact Finset.subset_union_left
  · intro e
    change R.stepIndex e + i e <
      R.stepIndex e + m
    exact hstep e

abbrev BranchSystem
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε) :=
  (e : OrderedFace k r) →
    GeneratorBranch (R.generators e)

@[simp]
theorem card_branchSystem
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε) :
    Fintype.card R.BranchSystem =
      ∏ e : OrderedFace k r,
        r ^ (R.generators e).card := by
  simp [BranchSystem]

theorem card_branchSystem_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε)
    (hr : 0 < r) :
    Fintype.card R.BranchSystem ≤
      ∏ e : OrderedFace k r,
        r ^ R.stepIndex e := by
  rw [R.card_branchSystem]
  apply Finset.prod_le_prod₀
  · intro e _he
    exact Nat.zero_le _
  · intro e _he
    exact
      Nat.pow_le_pow_right hr
        (R.generator_card_le e)

abbrev TopAtomChoice
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε) :=
  (e : OrderedFace k r) →
    (R.state e).partition.parts

@[simp]
theorem card_topAtomChoice
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε) :
    Fintype.card R.TopAtomChoice =
      ∏ e : OrderedFace k r,
        FacePartition.complexity
          (R.state e).partition := by
  simp [TopAtomChoice, FacePartition.complexity]

theorem card_topAtomChoice_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε) :
    Fintype.card R.TopAtomChoice ≤
      ∏ e : OrderedFace k r,
        2 ^ R.stepIndex e := by
  rw [R.card_topAtomChoice]
  apply Finset.prod_le_prod₀
  · intro e _he
    exact Nat.zero_le _
  · intro e _he
    exact R.complexity_le e

noncomputable def topAtomChoiceOf
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε)
    (x : Fin k → G) :
    R.TopAtomChoice :=
  fun e =>
    ⟨(R.state e).partition.part
        (orderedFaceTuple e x),
      (R.state e).partition.part_mem.2
        (Finset.mem_univ _)⟩

theorem mem_topAtomChoiceOf
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε)
    (x : Fin k → G) (e : OrderedFace k r) :
    orderedFaceTuple e x ∈
      (R.topAtomChoiceOf x e).1 :=
  (R.state e).partition.mem_part
    (Finset.mem_univ _)

def IsInCell
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε)
    (reference : Fin k → G)
    (w : R.BranchSystem)
    (x : Fin k → G) : Prop :=
  ∀ e i,
    eraseCoordinate i (orderedFaceTuple e x) ∈
      lowerGeneratorCell (R.generators e)
        (orderedFaceTuple e reference)
        (w e) i

theorem mem_state_part_iff_exists_lowerGeneratorCells
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε)
    (hr : 0 < r) (e : OrderedFace k r)
    (y x : Fin r → G) :
    x ∈ (R.state e).partition.part y ↔
      ∃ w : GeneratorBranch (R.generators e),
        ∀ i,
          eraseCoordinate i x ∈
            lowerGeneratorCell
              (R.generators e) y w i := by
  rw [R.partition_eq_generated e]
  exact
    mem_generatedBy_part_iff_exists_lowerGeneratorCells
      hr (R.generators e)
        (R.generators_supported e) y x

theorem same_top_atoms_iff_exists_branchSystem
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε)
    (hr : 0 < r)
    (reference x : Fin k → G) :
    (∀ e,
      orderedFaceTuple e x ∈
        (R.state e).partition.part
          (orderedFaceTuple e reference)) ↔
      ∃ w : R.BranchSystem,
        R.IsInCell reference w x := by
  classical
  constructor
  · intro hsame
    have he (e : OrderedFace k r) :
        ∃ w : GeneratorBranch (R.generators e),
          ∀ i,
            eraseCoordinate i
                (orderedFaceTuple e x) ∈
              lowerGeneratorCell (R.generators e)
                (orderedFaceTuple e reference)
                w i :=
      (R.mem_state_part_iff_exists_lowerGeneratorCells
        hr e _ _).1 (hsame e)
    choose w hw using he
    exact ⟨w, fun e i => hw e i⟩
  · rintro ⟨w, hcell⟩
    intro e
    exact
      (R.mem_state_part_iff_exists_lowerGeneratorCells
        hr e _ _).2 ⟨w e, hcell e⟩

theorem regularized_edgeWeight_eq_of_mem_state_part
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε)
    (e : OrderedFace k r)
    (reference x : Fin k → G)
    (hmem :
      orderedFaceTuple e x ∈
        (R.state e).partition.part
          (orderedFaceTuple e reference)) :
    (regularizedOrderedPattern H R.state).edgeWeight e
        (orderedFaceTuple e x) =
      (regularizedOrderedPattern H R.state).edgeWeight e
        (orderedFaceTuple e reference) := by
  exact
    conditionalMean_eq_of_mem_part
      (R.state e).partition (H.edgeWeight e) hmem

theorem regularized_patternWeight_eq_of_isInCell
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε)
    (hr : 0 < r)
    (reference x : Fin k → G)
    (w : R.BranchSystem)
    (hcell : R.IsInCell reference w x) :
    (regularizedOrderedPattern H R.state).patternWeight x =
      (regularizedOrderedPattern H R.state).patternWeight
        reference := by
  have hsame :=
    (R.same_top_atoms_iff_exists_branchSystem
      hr reference x).2 ⟨w, hcell⟩
  apply Finset.prod_congr rfl
  intro e _he
  exact
    R.regularized_edgeWeight_eq_of_mem_state_part
      e reference x (hsame e)

end GeneratedOrderedPatternRegularization

end Erdos3.FixedDensity

end

end OAI
