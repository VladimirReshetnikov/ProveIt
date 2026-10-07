-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import OAI.Combinatorics.Progressions.FixedDensity.OrderedCounting
import OAI.Combinatorics.Progressions.FixedDensity.OrderedRemoval
import OAI.Compat.BigOperators

namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def IsZeroOneValued {Ω : Type*} (f : Ω → ℝ) : Prop :=
  ∀ x, f x = 0 ∨ f x = 1

namespace FaceRegularityState

noncomputable def structuredSublevel
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : FaceRegularityState Ω) (f : Ω → ℝ) (τ : ℝ) :
    BooleanCutTest Ω := by
  classical
  exact Finset.univ.filter fun x => S.structured f x < τ

@[simp]
theorem mem_structuredSublevel
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : FaceRegularityState Ω) (f : Ω → ℝ) (τ : ℝ)
    (x : Ω) :
    x ∈ S.structuredSublevel f τ ↔
      S.structured f x < τ := by
  simp [structuredSublevel]

theorem structuredSublevel_measurable
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : FaceRegularityState Ω) (f : Ω → ℝ) (τ : ℝ) :
    IsPartitionMeasurable S.partition
      (S.structuredSublevel f τ).eval := by
  intro x y hy
  have hstructured :
      S.structured f y = S.structured f x :=
    conditionalMean_eq_of_mem_part S.partition f hy
  by_cases hx : S.structured f x < τ
  · have hy' : S.structured f y < τ := by
      simpa [hstructured] using hx
    have hmy : y ∈ S.structuredSublevel f τ :=
      mem_structuredSublevel S f τ y |>.2 hy'
    have hmx : x ∈ S.structuredSublevel f τ :=
      mem_structuredSublevel S f τ x |>.2 hx
    rw [BooleanCutTest.eval_of_mem _ hmy,
      BooleanCutTest.eval_of_mem _ hmx]
  · have hy' : ¬S.structured f y < τ := by
      simpa [hstructured] using hx
    have hmy : y ∉ S.structuredSublevel f τ :=
      fun hmem =>
        hy' (mem_structuredSublevel S f τ y |>.1 hmem)
    have hmx : x ∉ S.structuredSublevel f τ :=
      fun hmem =>
        hx (mem_structuredSublevel S f τ x |>.1 hmem)
    rw [BooleanCutTest.eval_of_not_mem _ hmy,
      BooleanCutTest.eval_of_not_mem _ hmx]

theorem mean_mul_structuredSublevel_eq
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : FaceRegularityState Ω) (f : Ω → ℝ) (τ : ℝ) :
    mean (fun x =>
        f x * (S.structuredSublevel f τ).eval x) =
      mean (fun x =>
        S.structured f x *
          (S.structuredSublevel f τ).eval x) := by
  exact
    mean_mul_eq_mean_conditionalMean_mul
      S.partition f (S.structuredSublevel f τ).eval
      (S.structuredSublevel_measurable f τ)

noncomputable def lowStructuredOneFinset
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : FaceRegularityState Ω) (f : Ω → ℝ) (τ : ℝ) :
    Finset Ω := by
  classical
  exact Finset.univ.filter fun x =>
    f x = 1 ∧ S.structured f x < τ

@[simp]
theorem mem_lowStructuredOneFinset
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : FaceRegularityState Ω) (f : Ω → ℝ) (τ : ℝ)
    (x : Ω) :
    x ∈ S.lowStructuredOneFinset f τ ↔
      f x = 1 ∧ S.structured f x < τ := by
  simp [lowStructuredOneFinset]

theorem indicator_lowStructuredOneFinset
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : FaceRegularityState Ω) {f : Ω → ℝ}
    (hf : IsZeroOneValued f) (τ : ℝ) (x : Ω) :
    finsetIndicator (S.lowStructuredOneFinset f τ) x =
      f x * (S.structuredSublevel f τ).eval x := by
  rcases hf x with hzero | hone
  · rw [hzero, zero_mul]
    apply finsetIndicator_of_not_mem
    intro hx
    exact zero_ne_one
      (hzero.symm.trans
        (mem_lowStructuredOneFinset S f τ x |>.1 hx).1)
  · rw [hone, one_mul]
    by_cases hx : S.structured f x < τ
    · rw [finsetIndicator_of_mem,
        BooleanCutTest.eval_of_mem]
      · exact mem_structuredSublevel S f τ x |>.2 hx
      · exact mem_lowStructuredOneFinset S f τ x |>.2
          ⟨hone, hx⟩
    · rw [finsetIndicator_of_not_mem,
        BooleanCutTest.eval_of_not_mem]
      · exact fun hmem =>
          hx (mem_structuredSublevel S f τ x |>.1 hmem)
      · exact fun hmem =>
          hx (mem_lowStructuredOneFinset S f τ x |>.1 hmem).2

theorem mean_indicator_lowStructuredOneFinset_le
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (S : FaceRegularityState Ω) {f : Ω → ℝ}
    (hf01 : IsZeroOneValued f)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    mean (finsetIndicator
      (S.lowStructuredOneFinset f τ)) ≤ τ := by
  rw [show
      finsetIndicator (S.lowStructuredOneFinset f τ) =
        fun x =>
          f x * (S.structuredSublevel f τ).eval x by
    funext x
    exact S.indicator_lowStructuredOneFinset hf01 τ x]
  rw [S.mean_mul_structuredSublevel_eq f τ]
  calc
    mean (fun x =>
        S.structured f x *
          (S.structuredSublevel f τ).eval x) ≤
        mean (fun _x : Ω => τ) := by
      apply mean_mono
      intro x
      by_cases hx : S.structured f x < τ
      · rw [BooleanCutTest.eval_of_mem]
        · simpa using hx.le
        · exact mem_structuredSublevel S f τ x |>.2 hx
      · rw [BooleanCutTest.eval_of_not_mem, mul_zero]
        · exact hτ
        · exact fun hmem =>
            hx (mem_structuredSublevel S f τ x |>.1 hmem)
    _ = τ := mean_const _

end FaceRegularityState

noncomputable def deletedFaceEquiv
    {G : Type*} {n : ℕ} (j : Fin (n + 1)) :
    DeletedVector (fun _ : Fin (n + 1) => G) j ≃
      (Fin n → G) where
  toFun := deletedFaceTuple j
  invFun := finTupleToDeletedVector j
  left_inv := finTupleToDeletedVector_deletedFaceTuple j
  right_inv := deletedFaceTuple_finTupleToDeletedVector j

theorem canonicalEdgeFunction_toWeighted_zeroOne
    {G : Type*} {n : ℕ}
    (H : SimplexHypergraph
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) :
    IsZeroOneValued
      (canonicalEdgeFunction H.toWeighted j) := by
  intro y
  classical
  by_cases hy :
      H.edge j (finTupleToDeletedVector j y)
  · right
    exact H.toWeighted_edgeWeight_of_edge hy
  · left
    exact H.toWeighted_edgeWeight_of_not_edge hy

noncomputable def lowStructuredDeletion
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (H : SimplexHypergraph
      (fun _ : Fin (n + 1) => G))
    (S : SimplexRegularitySystem G n) (τ : ℝ) :
    SimplexHypergraph.DeletionFamily
      (fun _ : Fin (n + 1) => G) :=
  fun j =>
    ((S j).lowStructuredOneFinset
      (canonicalEdgeFunction H.toWeighted j) τ).map
        (deletedFaceEquiv j).symm.toEmbedding

@[simp]
theorem card_lowStructuredDeletion
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (H : SimplexHypergraph
      (fun _ : Fin (n + 1) => G))
    (S : SimplexRegularitySystem G n) (τ : ℝ)
    (j : Fin (n + 1)) :
    (lowStructuredDeletion H S τ j).card =
      ((S j).lowStructuredOneFinset
        (canonicalEdgeFunction H.toWeighted j) τ).card := by
  classical
  simp [lowStructuredDeletion]

@[simp]
theorem mem_lowStructuredDeletion_iff
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (H : SimplexHypergraph
      (fun _ : Fin (n + 1) => G))
    (S : SimplexRegularitySystem G n) (τ : ℝ)
    (j : Fin (n + 1))
    (x : DeletedVector (fun _ : Fin (n + 1) => G) j) :
    x ∈ lowStructuredDeletion H S τ j ↔
      deletedFaceTuple j x ∈
        (S j).lowStructuredOneFinset
          (canonicalEdgeFunction H.toWeighted j) τ := by
  classical
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_map.mp hx
    have heq :
        y = deletedFaceTuple j x := by
      change y = (deletedFaceEquiv j) x
      calc
        y =
            (deletedFaceEquiv j)
              ((deletedFaceEquiv j).symm y) :=
          ((deletedFaceEquiv j).apply_symm_apply y).symm
        _ = (deletedFaceEquiv j) x :=
          congrArg (deletedFaceEquiv j) hyx
    simpa [heq] using hy
  · intro hx
    apply Finset.mem_map.mpr
    refine ⟨deletedFaceTuple j x, hx, ?_⟩
    exact (deletedFaceEquiv j).symm_apply_apply x

theorem lowStructuredDeletion_isEdgeDeletion
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (H : SimplexHypergraph
      (fun _ : Fin (n + 1) => G))
    (S : SimplexRegularitySystem G n) (τ : ℝ) :
    H.IsEdgeDeletion (lowStructuredDeletion H S τ) := by
  intro j x hx
  apply (H.mem_edgeFinset j x).2
  have hlow :=
    (mem_lowStructuredDeletion_iff H S τ j x).1 hx
  have hone :=
    ((S j).mem_lowStructuredOneFinset
      (canonicalEdgeFunction H.toWeighted j) τ
      (deletedFaceTuple j x)).1 hlow |>.1
  by_contra hedge
  have hzero :
      H.toWeighted.edgeWeight j x = 0 :=
    H.toWeighted_edgeWeight_of_not_edge hedge
  have hcanonical :
      canonicalEdgeFunction H.toWeighted j
          (deletedFaceTuple j x) =
        H.toWeighted.edgeWeight j x := by
    simp [canonicalEdgeFunction]
  rw [hcanonical, hzero] at hone
  norm_num at hone

theorem colorDeletionDensity_lowStructuredDeletion_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {n : ℕ}
    (H : SimplexHypergraph
      (fun _ : Fin (n + 1) => G))
    (S : SimplexRegularitySystem G n)
    {τ : ℝ} (hτ : 0 ≤ τ)
    (j : Fin (n + 1)) :
    SimplexHypergraph.colorDeletionDensity
        (lowStructuredDeletion H S τ) j ≤ τ := by
  have hmean :=
    (S j).mean_indicator_lowStructuredOneFinset_le
      (canonicalEdgeFunction_toWeighted_zeroOne H j) hτ
  rw [mean_finsetIndicator] at hmean
  rw [SimplexHypergraph.colorDeletionDensity,
    card_lowStructuredDeletion]
  have hcard :
      Fintype.card
          (DeletedVector
            (fun _ : Fin (n + 1) => G) j) =
        Fintype.card (Fin n → G) :=
    Fintype.card_congr (deletedFaceEquiv j)
  rw [hcard]
  exact hmean

theorem normalizedDeletionCost_lowStructuredDeletion_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {n : ℕ}
    (H : SimplexHypergraph
      (fun _ : Fin (n + 1) => G))
    (S : SimplexRegularitySystem G n)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    SimplexHypergraph.normalizedDeletionCost
        (lowStructuredDeletion H S τ) ≤ τ := by
  let M : ℕ := Fintype.card (Fin n → G)
  have hM : 0 < M := Fintype.card_pos
  have hface (j : Fin (n + 1)) :
      Fintype.card
          (DeletedVector
            (fun _ : Fin (n + 1) => G) j) = M := by
    exact Fintype.card_congr (deletedFaceEquiv j)
  have hcard (j : Fin (n + 1)) :
      ((lowStructuredDeletion H S τ j).card : ℝ) ≤
        τ * M := by
    have hdensity :=
      colorDeletionDensity_lowStructuredDeletion_le
        H S hτ j
    rw [SimplexHypergraph.colorDeletionDensity,
      hface] at hdensity
    have hMR : (0 : ℝ) < M := by exact_mod_cast hM
    exact (div_le_iff₀ hMR).mp hdensity
  have hcount :
      (SimplexHypergraph.deletionCount
          (lowStructuredDeletion H S τ) : ℝ) ≤
        (n + 1 : ℝ) * (τ * M) := by
    calc
      (SimplexHypergraph.deletionCount
          (lowStructuredDeletion H S τ) : ℝ) =
          ∑ j : Fin (n + 1),
            ((lowStructuredDeletion H S τ j).card : ℝ) := by
        simp [SimplexHypergraph.deletionCount]
      _ ≤ ∑ _j : Fin (n + 1), τ * M :=
        Finset.sum_le_sum fun j _ => hcard j
      _ = (n + 1 : ℝ) * (τ * M) := by
        simp
  have hcapacity :
      SimplexHypergraph.deletionCapacity
          (fun _ : Fin (n + 1) => G) =
        (n + 1) * M := by
    unfold SimplexHypergraph.deletionCapacity
    simp_rw [hface]
    simp
  rw [SimplexHypergraph.normalizedDeletionCost,
    hcapacity]
  have hdenom :
      (0 : ℝ) < ((n + 1) * M : ℕ) := by
    exact_mod_cast Nat.mul_pos (by omega) hM
  apply (div_le_iff₀ hdenom).2
  calc
    (SimplexHypergraph.deletionCount
        (lowStructuredDeletion H S τ) : ℝ) ≤
        (n + 1 : ℝ) * (τ * M) := hcount
    _ = τ * (((n + 1) * M : ℕ) : ℝ) := by
      push_cast
      ring

theorem regularized_edgeWeight_ge_of_not_mem_lowDeletion
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (H : SimplexHypergraph
      (fun _ : Fin (n + 1) => G))
    (S : SimplexRegularitySystem G n) (τ : ℝ)
    (j : Fin (n + 1))
    (x : DeletedVector (fun _ : Fin (n + 1) => G) j)
    (hx : H.edge j x)
    (hnot : x ∉ lowStructuredDeletion H S τ j) :
    τ ≤
      (regularizedSimplexSystem H.toWeighted S).edgeWeight j x := by
  have hone :
      canonicalEdgeFunction H.toWeighted j
          (deletedFaceTuple j x) = 1 := by
    rw [canonicalEdgeFunction]
    have hface :
        finTupleToDeletedVector j (deletedFaceTuple j x) = x :=
      finTupleToDeletedVector_deletedFaceTuple j x
    rw [hface]
    exact H.toWeighted_edgeWeight_of_edge hx
  have hnlow :
      deletedFaceTuple j x ∉
        (S j).lowStructuredOneFinset
          (canonicalEdgeFunction H.toWeighted j) τ := by
    exact fun hmem =>
      hnot ((mem_lowStructuredDeletion_iff H S τ j x).2 hmem)
  have hnotlt :
      ¬(S j).structured
          (canonicalEdgeFunction H.toWeighted j)
          (deletedFaceTuple j x) < τ := by
    intro hlt
    apply hnlow
    exact
      ((S j).mem_lowStructuredOneFinset
        (canonicalEdgeFunction H.toWeighted j) τ
        (deletedFaceTuple j x)).2
        ⟨hone, hlt⟩
  exact not_lt.mp hnotlt

theorem pow_le_regularized_simplexWeight_of_avoids_lowDeletion
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (H : SimplexHypergraph
      (fun _ : Fin (n + 1) => G))
    (S : SimplexRegularitySystem G n)
    {τ : ℝ} (hτ : 0 ≤ τ)
    (x : Fin (n + 1) → G)
    (hx : x ∈ H.simplexFinset)
    (havoid :
      ∀ j, deleteCoordinate x j ∉
        lowStructuredDeletion H S τ j) :
    τ ^ (n + 1) ≤
      (regularizedSimplexSystem H.toWeighted S).simplexWeight x := by
  change
    τ ^ (n + 1) ≤
      ∏ j : Fin (n + 1),
        (regularizedSimplexSystem H.toWeighted S).edgeWeight j
          (deleteCoordinate x j)
  calc
    τ ^ (n + 1) = ∏ _j : Fin (n + 1), τ := by
      simp
    _ ≤
        ∏ j : Fin (n + 1),
          (regularizedSimplexSystem H.toWeighted S).edgeWeight j
            (deleteCoordinate x j) := by
      apply Finset.prod_le_prod₀
      · intro _ _
        exact hτ
      · intro j _
        exact regularized_edgeWeight_ge_of_not_mem_lowDeletion
          H S τ j (deleteCoordinate x j)
          ((H.mem_simplexFinset x).1 hx j) (havoid j)

theorem lowStructuredDeletion_isSimplexCover_of_count_lt
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {n : ℕ}
    (H : SimplexHypergraph
      (fun _ : Fin (n + 1) => G))
    (S : SimplexRegularitySystem G n)
    {τ : ℝ} (hτ : 0 < τ)
    (hcount :
      (regularizedSimplexSystem H.toWeighted S).simplexCount <
        τ ^ (n + 1) /
          Fintype.card (Fin (n + 1) → G)) :
    H.IsSimplexCover (lowStructuredDeletion H S τ) := by
  classical
  by_contra hcover
  unfold SimplexHypergraph.IsSimplexCover at hcover
  push Not at hcover
  obtain ⟨x, hx, havoid⟩ := hcover
  let K := regularizedSimplexSystem H.toWeighted S
  have hK :
      EdgeWeightsInUnitInterval K :=
    regularizedSimplexSystem_unitInterval
      (fun j y => ⟨H.toWeighted_edgeWeight_nonneg j y,
        by
          classical
          by_cases hy : H.edge j y
          · rw [H.toWeighted_edgeWeight_of_edge hy]
          · rw [H.toWeighted_edgeWeight_of_not_edge hy]
            norm_num⟩)
      S
  have hpoint :
      τ ^ (n + 1) ≤ K.simplexWeight x :=
    pow_le_regularized_simplexWeight_of_avoids_lowDeletion
      H S hτ.le x hx havoid
  have hsingle :
      K.simplexWeight x ≤ ∑ y, K.simplexWeight y := by
    apply Finset.single_le_sum
    · intro y _
      exact K.simplexWeight_nonneg
        (fun j z => (hK j z).1) y
    · exact Finset.mem_univ x
  have hmean :
      τ ^ (n + 1) /
          Fintype.card (Fin (n + 1) → G) ≤
        K.simplexCount := by
    rw [WeightedSimplexSystem.simplexCount, mean,
      Fintype.expect_eq_sum_div_card]
    exact div_le_div_of_nonneg_right
      (hpoint.trans hsingle) (Nat.cast_nonneg _)
  exact (not_lt_of_ge hmean) hcount

end Erdos3.FixedDensity

end

end OAI
