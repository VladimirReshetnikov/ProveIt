-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import Mathlib.Data.Finset.Max
import Mathlib.Order.Hom.PowersetCard
import OAI.Combinatorics.Progressions.FixedDensity.BooleanCutReduction
import OAI.Combinatorics.Progressions.FixedDensity.OrderedPattern
import OAI.Compat.Order

namespace OAI

section

namespace Erdos3.FixedDensity

def HasDenseAPCount (k N : ℕ) [NeZero N]
    (δ c : ℝ) : Prop :=
  ∀ A : Finset (ZMod N),
    δ ≤ mean (finsetIndicator A) →
      c ≤ cyclicAPCount k N (finsetIndicator A)

def HasWeightedAPCount (k N : ℕ) [NeZero N]
    (δ c : ℝ) : Prop :=
  ∀ g : ZMod N → ℝ,
    (∀ x, 0 ≤ g x) →
    (∀ x, g x ≤ 1) →
    δ ≤ mean g →
      c ≤ cyclicAPCount k N g

def HasUniformDenseAPCount (k : ℕ) (δ c : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N], HasDenseAPCount k N δ c

def HasUniformWeightedAPCount (k : ℕ) (δ c : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N], HasWeightedAPCount k N δ c

theorem weightedAPCount_of_denseAPCount
    {k N : ℕ} [NeZero N] {δ c : ℝ}
    (hδ0 : 0 ≤ δ)
    (hdense : HasDenseAPCount k N (δ / 2) c)
    {g : ZMod N → ℝ}
    (hg0 : ∀ x, 0 ≤ g x)
    (hg1 : ∀ x, g x ≤ 1)
    (hmean : δ ≤ mean g) :
    (δ / 2) ^ k * c ≤ cyclicAPCount k N g := by
  let A : Finset (ZMod N) :=
    Finset.univ.filter fun x => δ / 2 ≤ g x
  have hpoint :
      ∀ x : ZMod N,
        g x ≤ δ / 2 + finsetIndicator A x := by
    intro x
    by_cases hx : x ∈ A
    · rw [finsetIndicator_of_mem hx]
      linarith [hg1 x]
    · rw [finsetIndicator_of_not_mem hx, add_zero]
      have hnot : ¬δ / 2 ≤ g x := by
        simpa [A] using hx
      exact le_of_lt (lt_of_not_ge hnot)
  have hmean_upper :=
    mean_mono (f := g)
      (g := fun x => δ / 2 + finsetIndicator A x) hpoint
  rw [mean_add, mean_const] at hmean_upper
  have hAmean : δ / 2 ≤ mean (finsetIndicator A) := by
    linarith
  have hsetCount := hdense A hAmean
  have hscaled_nonneg :
      ∀ x : ZMod N,
        0 ≤ δ / 2 * finsetIndicator A x := by
    intro x
    exact mul_nonneg (div_nonneg hδ0 (by norm_num))
      (by
        unfold finsetIndicator
        split <;> norm_num)
  have hscaled_le :
      ∀ x : ZMod N,
        δ / 2 * finsetIndicator A x ≤ g x := by
    intro x
    by_cases hx : x ∈ A
    · rw [finsetIndicator_of_mem hx, mul_one]
      simpa [A] using (Finset.mem_filter.mp hx).2
    · rw [finsetIndicator_of_not_mem hx, mul_zero]
      exact hg0 x
  have hcountMono :
      cyclicAPCount k N
          (fun x => δ / 2 * finsetIndicator A x) ≤
        cyclicAPCount k N g :=
    cyclicAPCount_mono (k := k) (N := N)
      hscaled_nonneg hscaled_le
  rw [cyclicAPCount_smul] at hcountMono
  calc
    (δ / 2) ^ k * c ≤
        (δ / 2) ^ k *
          cyclicAPCount k N (finsetIndicator A) :=
      mul_le_mul_of_nonneg_left hsetCount
        (pow_nonneg (div_nonneg hδ0 (by norm_num)) _)
    _ ≤ cyclicAPCount k N g := hcountMono

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace SimplexHypergraph

abbrev DeletionFamily {k : ℕ} (V : Fin k → Type*) :=
  (j : Fin k) → Finset (DeletedVector V j)

noncomputable def deleteEdges {k : ℕ} {V : Fin k → Type*}
    (H : SimplexHypergraph V) (deleted : DeletionFamily V) :
    SimplexHypergraph V := by
  classical
  exact
    { edge := fun j x => H.edge j x ∧ x ∉ deleted j }

@[simp]
theorem deleteEdges_edge {k : ℕ} {V : Fin k → Type*}
    (H : SimplexHypergraph V) (deleted : DeletionFamily V)
    (j : Fin k) (x : DeletedVector V j) :
    (H.deleteEdges deleted).edge j x ↔
      H.edge j x ∧ x ∉ deleted j := by
  classical
  simp [deleteEdges]

@[simp]
theorem mem_deleteEdges_simplexFinset {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (deleted : DeletionFamily V)
    (x : (i : Fin k) → V i) :
    x ∈ (H.deleteEdges deleted).simplexFinset ↔
      x ∈ H.simplexFinset ∧
        ∀ j, deleteCoordinate x j ∉ deleted j := by
  classical
  simp only [mem_simplexFinset, deleteEdges_edge, forall_and]

def IsSimplexFree {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)] (H : SimplexHypergraph V) : Prop :=
  H.simplexFinset = ∅

theorem isSimplexFree_iff {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) :
    H.IsSimplexFree ↔
      ∀ x, ∃ j, ¬H.edge j (deleteCoordinate x j) := by
  classical
  rw [IsSimplexFree, Finset.eq_empty_iff_forall_notMem]
  simp only [mem_simplexFinset]
  push Not
  rfl

def emptyDeletion {k : ℕ} (V : Fin k → Type*) :
    DeletionFamily V :=
  fun _ => ∅

@[simp]
theorem mem_emptyDeletion {k : ℕ} {V : Fin k → Type*}
    (j : Fin k) (x : DeletedVector V j) :
    x ∉ emptyDeletion V j := by
  simp [emptyDeletion]

@[simp]
theorem deleteEdges_empty_simplexFinset {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) :
    (H.deleteEdges (emptyDeletion V)).simplexFinset =
      H.simplexFinset := by
  classical
  ext x
  simp

theorem deleteEdges_simplexFinset_antitone {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V)
    {deleted₁ deleted₂ : DeletionFamily V}
    (hdel : ∀ j, deleted₁ j ⊆ deleted₂ j) :
    (H.deleteEdges deleted₂).simplexFinset ⊆
      (H.deleteEdges deleted₁).simplexFinset := by
  intro x hx
  rw [mem_deleteEdges_simplexFinset] at hx ⊢
  exact ⟨hx.1, fun j hj => hx.2 j (hdel j hj)⟩

theorem IsSimplexCover.mono {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    {H : SimplexHypergraph V}
    {deleted₁ deleted₂ : DeletionFamily V}
    (hcover : H.IsSimplexCover deleted₁)
    (hdel : ∀ j, deleted₁ j ⊆ deleted₂ j) :
    H.IsSimplexCover deleted₂ := by
  intro x hx
  obtain ⟨j, hj⟩ := hcover x hx
  exact ⟨j, hdel j hj⟩

def IsEdgeDeletion {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (deleted : DeletionFamily V) : Prop :=
  ∀ j, deleted j ⊆ H.edgeFinset j

noncomputable def trimDeletion {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (deleted : DeletionFamily V) :
    DeletionFamily V := by
  classical
  exact fun j => deleted j ∩ H.edgeFinset j

theorem trimDeletion_isEdgeDeletion {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (deleted : DeletionFamily V) :
    H.IsEdgeDeletion (H.trimDeletion deleted) := by
  classical
  intro j
  exact Finset.inter_subset_right

theorem trimDeletion_subset {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (deleted : DeletionFamily V)
    (j : Fin k) :
    H.trimDeletion deleted j ⊆ deleted j := by
  classical
  exact Finset.inter_subset_left

theorem IsSimplexCover.trim {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    {H : SimplexHypergraph V} {deleted : DeletionFamily V}
    (hcover : H.IsSimplexCover deleted) :
    H.IsSimplexCover (H.trimDeletion deleted) := by
  classical
  intro x hx
  obtain ⟨j, hj⟩ := hcover x hx
  refine ⟨j, Finset.mem_inter.mpr ⟨hj, ?_⟩⟩
  exact H.mem_edgeFinset j (deleteCoordinate x j) |>.2
    ((H.mem_simplexFinset x).1 hx j)

theorem trimDeletion_simplexFinset {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (deleted : DeletionFamily V) :
    (H.deleteEdges (H.trimDeletion deleted)).simplexFinset =
      (H.deleteEdges deleted).simplexFinset := by
  classical
  ext x
  rw [mem_deleteEdges_simplexFinset,
    mem_deleteEdges_simplexFinset]
  constructor
  · rintro ⟨hx, havoid⟩
    refine ⟨hx, fun j hj => ?_⟩
    apply havoid j
    refine Finset.mem_inter.mpr ⟨hj, ?_⟩
    exact (H.mem_edgeFinset j (deleteCoordinate x j)).2
      ((H.mem_simplexFinset x).1 hx j)
  · rintro ⟨hx, havoid⟩
    exact ⟨hx, fun j hj => havoid j (Finset.mem_inter.mp hj).1⟩

noncomputable def fullEdgeDeletion {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) : DeletionFamily V :=
  H.edgeFinset

theorem fullEdgeDeletion_isEdgeDeletion {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) :
    H.IsEdgeDeletion H.fullEdgeDeletion :=
  fun _ => Finset.Subset.rfl

theorem fullEdgeDeletion_isSimplexCover {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    [Nonempty (Fin k)] (H : SimplexHypergraph V) :
    H.IsSimplexCover H.fullEdgeDeletion := by
  classical
  intro x hx
  let j : Fin k := Classical.choice inferInstance
  refine ⟨j, ?_⟩
  exact (H.mem_edgeFinset j (deleteCoordinate x j)).2
    ((H.mem_simplexFinset x).1 hx j)

noncomputable def projectedSimplexDeletion {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) : DeletionFamily V := by
  classical
  exact fun j =>
    H.simplexFinset.image (fun x => deleteCoordinate x j)

theorem projectedSimplexDeletion_isEdgeDeletion {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) :
    H.IsEdgeDeletion H.projectedSimplexDeletion := by
  classical
  intro j e he
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
  exact (H.mem_edgeFinset j (deleteCoordinate x j)).2
    ((H.mem_simplexFinset x).1 hx j)

theorem projectedSimplexDeletion_isSimplexCover {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    [Nonempty (Fin k)] (H : SimplexHypergraph V) :
    H.IsSimplexCover H.projectedSimplexDeletion := by
  classical
  intro x hx
  let j : Fin k := Classical.choice inferInstance
  refine ⟨j, ?_⟩
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

theorem card_projectedSimplexDeletion_le {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (j : Fin k) :
    (H.projectedSimplexDeletion j).card ≤
      H.simplexFinset.card := by
  classical
  exact Finset.card_image_le

def deletionCount {k : ℕ} {V : Fin k → Type*}
    (deleted : DeletionFamily V) : ℕ :=
  ∑ j, (deleted j).card

@[simp]
theorem deletionCount_empty {k : ℕ} (V : Fin k → Type*) :
    deletionCount (emptyDeletion V) = 0 := by
  simp [deletionCount, emptyDeletion]

theorem deletionCount_mono {k : ℕ} {V : Fin k → Type*}
    {deleted₁ deleted₂ : DeletionFamily V}
    (hdel : ∀ j, deleted₁ j ⊆ deleted₂ j) :
    deletionCount deleted₁ ≤ deletionCount deleted₂ := by
  apply Finset.sum_le_sum
  intro j _
  exact Finset.card_le_card (hdel j)

theorem deletionCount_le_of_card_le {k m : ℕ}
    {V : Fin k → Type*} (deleted : DeletionFamily V)
    (hcard : ∀ j, (deleted j).card ≤ m) :
    deletionCount deleted ≤ k * m := by
  calc
    deletionCount deleted ≤ ∑ _j : Fin k, m := by
      apply Finset.sum_le_sum
      intro j _
      exact hcard j
    _ = k * m := by
      simp

theorem deletionCount_trim_le {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (deleted : DeletionFamily V) :
    deletionCount (H.trimDeletion deleted) ≤
      deletionCount deleted :=
  deletionCount_mono (H.trimDeletion_subset deleted)

theorem deletionCount_projectedSimplexDeletion_le {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) :
    deletionCount H.projectedSimplexDeletion ≤
      k * H.simplexFinset.card := by
  calc
    deletionCount H.projectedSimplexDeletion ≤
        ∑ _j : Fin k, H.simplexFinset.card := by
      apply Finset.sum_le_sum
      intro j _
      exact H.card_projectedSimplexDeletion_le j
    _ = k * H.simplexFinset.card := by
      simp

theorem exists_simplexCover_card_le_simplexFinset {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    [Nonempty (Fin k)] (H : SimplexHypergraph V) :
    ∃ deleted : DeletionFamily V,
      H.IsSimplexCover deleted ∧
      H.IsEdgeDeletion deleted ∧
      (∀ j, (deleted j).card ≤ H.simplexFinset.card) ∧
      deletionCount deleted ≤ k * H.simplexFinset.card :=
  ⟨H.projectedSimplexDeletion,
    H.projectedSimplexDeletion_isSimplexCover,
    H.projectedSimplexDeletion_isEdgeDeletion,
    H.card_projectedSimplexDeletion_le,
    H.deletionCount_projectedSimplexDeletion_le⟩

def deletionCapacity {k : ℕ} (V : Fin k → Type*)
    [∀ i, Fintype (V i)] : ℕ :=
  ∑ j, Fintype.card (DeletedVector V j)

@[simp]
theorem card_deletedVector_fin (k n : ℕ) (j : Fin k) :
    Fintype.card
        (DeletedVector (fun _ : Fin k => Fin n) j) =
      n ^ (k - 1) := by
  simp [DeletedVector, Fintype.card_pi]

@[simp]
theorem deletionCapacity_fin (k n : ℕ) :
    deletionCapacity (fun _ : Fin k => Fin n) =
      k * n ^ (k - 1) := by
  simp [deletionCapacity]

theorem deletionCount_le_capacity {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (deleted : DeletionFamily V) :
    deletionCount deleted ≤ deletionCapacity V := by
  apply Finset.sum_le_sum
  intro j _
  exact (deleted j).card_le_univ

noncomputable def colorDeletionDensity {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (deleted : DeletionFamily V) (j : Fin k) : ℝ :=
  ((deleted j).card : ℝ) /
    Fintype.card (DeletedVector V j)

theorem colorDeletionDensity_nonneg {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (deleted : DeletionFamily V) (j : Fin k) :
    0 ≤ colorDeletionDensity deleted j :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem colorDeletionDensity_le_one {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (deleted : DeletionFamily V) (j : Fin k) :
    colorDeletionDensity deleted j ≤ 1 := by
  apply div_le_one_of_le₀
  · exact_mod_cast (deleted j).card_le_univ
  · exact Nat.cast_nonneg _

@[simp]
theorem colorDeletionDensity_fin {k n : ℕ}
    (deleted :
      DeletionFamily (fun _ : Fin k => Fin n))
    (j : Fin k) :
    colorDeletionDensity deleted j =
      ((deleted j).card : ℝ) / (n ^ (k - 1) : ℕ) := by
  simp [colorDeletionDensity]

noncomputable def normalizedDeletionCost {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (deleted : DeletionFamily V) : ℝ :=
  (deletionCount deleted : ℝ) / (deletionCapacity V : ℝ)

theorem normalizedDeletionCost_nonneg {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (deleted : DeletionFamily V) :
    0 ≤ normalizedDeletionCost deleted := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem normalizedDeletionCost_le_one {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (deleted : DeletionFamily V) :
    normalizedDeletionCost deleted ≤ 1 := by
  apply div_le_one_of_le₀
  · exact_mod_cast deletionCount_le_capacity deleted
  · exact Nat.cast_nonneg _

theorem normalizedDeletionCost_mono {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    {deleted₁ deleted₂ : DeletionFamily V}
    (hdel : ∀ j, deleted₁ j ⊆ deleted₂ j) :
    normalizedDeletionCost deleted₁ ≤
      normalizedDeletionCost deleted₂ := by
  apply div_le_div_of_nonneg_right
  · exact_mod_cast deletionCount_mono hdel
  · exact Nat.cast_nonneg _

theorem normalizedDeletionCost_trim_le {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (deleted : DeletionFamily V) :
    normalizedDeletionCost (H.trimDeletion deleted) ≤
      normalizedDeletionCost deleted :=
  normalizedDeletionCost_mono (H.trimDeletion_subset deleted)

@[simp]
theorem normalizedDeletionCost_empty {k : ℕ}
    (V : Fin k → Type*) [∀ i, Fintype (V i)] :
    normalizedDeletionCost (emptyDeletion V) = 0 := by
  simp [normalizedDeletionCost]

theorem exists_minimum_simplexCover {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    [Nonempty (Fin k)] (H : SimplexHypergraph V) :
    ∃ deleted : DeletionFamily V,
      H.IsSimplexCover deleted ∧
      H.IsEdgeDeletion deleted ∧
      ∀ other : DeletionFamily V,
        H.IsSimplexCover other →
          deletionCount deleted ≤ deletionCount other := by
  classical
  let covers : Finset (DeletionFamily V) :=
    Finset.univ.filter H.IsSimplexCover
  have covers_nonempty : covers.Nonempty := by
    refine ⟨H.fullEdgeDeletion, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, H.fullEdgeDeletion_isSimplexCover⟩
  obtain ⟨deleted, hdeleted, hminimal⟩ :=
    Finset.exists_min_image covers deletionCount covers_nonempty
  have hcover : H.IsSimplexCover deleted :=
    (Finset.mem_filter.mp hdeleted).2
  refine
    ⟨H.trimDeletion deleted, hcover.trim,
      H.trimDeletion_isEdgeDeletion deleted, ?_⟩
  intro other hother
  calc
    deletionCount (H.trimDeletion deleted) ≤
        deletionCount deleted :=
      H.deletionCount_trim_le deleted
    _ ≤ deletionCount other := by
      apply hminimal other
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hother⟩

theorem exists_minimum_normalized_simplexCover {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    [Nonempty (Fin k)] (H : SimplexHypergraph V) :
    ∃ deleted : DeletionFamily V,
      H.IsSimplexCover deleted ∧
      H.IsEdgeDeletion deleted ∧
      ∀ other : DeletionFamily V,
        H.IsSimplexCover other →
          normalizedDeletionCost deleted ≤
            normalizedDeletionCost other := by
  obtain ⟨deleted, hcover, hedge, hminimal⟩ :=
    H.exists_minimum_simplexCover
  refine ⟨deleted, hcover, hedge, ?_⟩
  intro other hother
  apply div_le_div_of_nonneg_right
  · exact_mod_cast hminimal other hother
  · exact Nat.cast_nonneg _

end SimplexHypergraph

def NoSimplexAfterDeleting {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V)
    (deleted : SimplexHypergraph.DeletionFamily V) : Prop :=
  (H.deleteEdges deleted).IsSimplexFree

theorem isSimplexCover_iff_noSimplexAfterDeleting {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V)
    (deleted : SimplexHypergraph.DeletionFamily V) :
    H.IsSimplexCover deleted ↔
      NoSimplexAfterDeleting H deleted := by
  classical
  constructor
  · intro hcover
    rw [NoSimplexAfterDeleting,
      SimplexHypergraph.IsSimplexFree,
      Finset.eq_empty_iff_forall_notMem]
    intro x hx
    rw [SimplexHypergraph.mem_deleteEdges_simplexFinset] at hx
    obtain ⟨j, hj⟩ := hcover x hx.1
    exact hx.2 j hj
  · intro hfree x hx
    by_contra h
    push Not at h
    have hsurvives :
        x ∈ (H.deleteEdges deleted).simplexFinset :=
      (H.mem_deleteEdges_simplexFinset deleted x).2 ⟨hx, h⟩
    rw [NoSimplexAfterDeleting,
      SimplexHypergraph.IsSimplexFree] at hfree
    rw [hfree] at hsurvives
    simp at hsurvives

theorem NoSimplexAfterDeleting.mono {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    {H : SimplexHypergraph V}
    {deleted₁ deleted₂ : SimplexHypergraph.DeletionFamily V}
    (hfree : NoSimplexAfterDeleting H deleted₁)
    (hdel : ∀ j, deleted₁ j ⊆ deleted₂ j) :
    NoSimplexAfterDeleting H deleted₂ := by
  apply (isSimplexCover_iff_noSimplexAfterDeleting H deleted₂).1
  apply SimplexHypergraph.IsSimplexCover.mono
    ((isSimplexCover_iff_noSimplexAfterDeleting
      H deleted₁).2 hfree)
  exact hdel

theorem emptyDeletion_isSimplexCover_iff {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) :
    H.IsSimplexCover (SimplexHypergraph.emptyDeletion V) ↔
      H.IsSimplexFree := by
  rw [isSimplexCover_iff_noSimplexAfterDeleting,
    NoSimplexAfterDeleting,
    SimplexHypergraph.IsSimplexFree,
    SimplexHypergraph.deleteEdges_empty_simplexFinset]
  rfl

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def apSetHypergraph (k N : ℕ) (A : Finset (ZMod N)) :
    SimplexHypergraph (fun _ : Fin k => ZMod N) where
  edge j x := apSimplexForm k N j x ∈ A

@[simp]
theorem apSetHypergraph_edge
    (k N : ℕ) (A : Finset (ZMod N))
    (j : Fin k)
    (x : DeletedVector (fun _ : Fin k => ZMod N) j) :
    (apSetHypergraph k N A).edge j x ↔
      apSimplexForm k N j x ∈ A :=
  Iff.rfl

@[simp]
theorem apSetHypergraph_toWeighted_edgeWeight
    (k N : ℕ) (A : Finset (ZMod N))
    (j : Fin k)
    (x : DeletedVector (fun _ : Fin k => ZMod N) j) :
    (apSetHypergraph k N A).toWeighted.edgeWeight j x =
      finsetIndicator A (apSimplexForm k N j x) := by
  classical
  by_cases hx : apSimplexForm k N j x ∈ A
  · rw [SimplexHypergraph.toWeighted_edgeWeight_of_edge]
    · exact (finsetIndicator_of_mem hx).symm
    · exact hx
  · rw [SimplexHypergraph.toWeighted_edgeWeight_of_not_edge]
    · exact (finsetIndicator_of_not_mem hx).symm
    · exact hx

theorem apSetHypergraph_simplexCount_eq_cyclicAPCount
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N)) :
    (apSetHypergraph (r + 2) N A).toWeighted.simplexCount =
      cyclicAPCount (r + 2) N (finsetIndicator A) := by
  rw [← apSimplexSystem_simplexCount_eq_cyclicAPCount
    r N (finsetIndicator A)]
  simp only [WeightedSimplexSystem.simplexCount]
  apply congrArg mean
  funext x
  apply Finset.prod_congr rfl
  intro j _
  exact apSetHypergraph_toWeighted_edgeWeight
    (r + 2) N A j (deleteCoordinate x j)

abbrev DiagonalAPParameter
    (r N : ℕ) (A : Finset (ZMod N)) :=
  ↥A × (Fin r → ZMod N)

def diagonalAPSimplex
    (r N : ℕ) (A : Finset (ZMod N))
    (p : DiagonalAPParameter r N A) :
    Fin (r + 2) → ZMod N :=
  simplexCoordinatesOfAP r N p.1.1 0 p.2

@[simp]
theorem simplexCoordinateSum_diagonalAPSimplex
    (r N : ℕ) (A : Finset (ZMod N))
    (p : DiagonalAPParameter r N A) :
    simplexCoordinateSum (r + 2) N
      (diagonalAPSimplex r N A p) = 0 := by
  simp [diagonalAPSimplex]

@[simp]
theorem simplexCoordinateMoment_diagonalAPSimplex
    (r N : ℕ) (A : Finset (ZMod N))
    (p : DiagonalAPParameter r N A) :
    simplexCoordinateMoment (r + 2) N
      (diagonalAPSimplex r N A p) = p.1.1 := by
  simp [diagonalAPSimplex]

@[simp]
theorem apSimplexForm_diagonalAPSimplex
    (r N : ℕ) (A : Finset (ZMod N))
    (p : DiagonalAPParameter r N A)
    (j : Fin (r + 2)) :
    apSimplexForm (r + 2) N j
        (deleteCoordinate (diagonalAPSimplex r N A p) j) =
      p.1.1 := by
  rw [apSimplexForm_deleteCoordinate,
    simplexCoordinateMoment_diagonalAPSimplex,
    simplexCoordinateSum_diagonalAPSimplex]
  simp

theorem diagonalAPSimplex_mem_simplexFinset
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (p : DiagonalAPParameter r N A) :
    diagonalAPSimplex r N A p ∈
      (apSetHypergraph (r + 2) N A).simplexFinset := by
  let : ∀ _ : Fin (r + 2), Fintype (ZMod N) :=
    fun _ => inferInstance
  rw [SimplexHypergraph.mem_simplexFinset]
  intro j
  rw [apSetHypergraph_edge,
    apSimplexForm_diagonalAPSimplex]
  exact p.1.2

theorem diagonalAPSimplex_injective
    (r N : ℕ) (A : Finset (ZMod N)) :
    Function.Injective (diagonalAPSimplex r N A) := by
  intro p q hpq
  apply Prod.ext
  · apply Subtype.ext
    have hmoment :=
      congrArg
        (simplexCoordinateMoment (r + 2) N) hpq
    simpa using hmoment
  · funext i
    exact congrFun hpq i.succ.succ

noncomputable def deletedVectorToFinTuple
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : DeletedVector (fun _ : Fin (n + 1) => G) j) :
    Fin n → G :=
  fun t => x (finSuccAboveEquiv j t)

@[simp]
theorem deletedVectorToFinTuple_deleteCoordinate
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : Fin (n + 1) → G) (t : Fin n) :
    deletedVectorToFinTuple j (deleteCoordinate x j) t =
      x (j.succAbove t) :=
  rfl

theorem eq_of_deletedVectorToFinTuple_eq_of_sum_eq
    {G : Type*} [AddCommGroup G] {n : ℕ}
    {x y : Fin (n + 1) → G}
    {j l : Fin (n + 1)}
    (hjl : j = l)
    (hdeleted :
      deletedVectorToFinTuple j (deleteCoordinate x j) =
        deletedVectorToFinTuple l (deleteCoordinate y l))
    (hsum : (∑ i, x i) = ∑ i, y i) :
    x = y := by
  subst l
  have hother :
      ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase j,
          x i =
        ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase j,
          y i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq hij
    subst i
    exact congrFun hdeleted t
  have hj : x j = y j := by
    apply add_left_cancel
      (a :=
        ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase j,
          x i)
    calc
      (∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase j,
          x i) + x j =
          ∑ i, x i :=
        Finset.sum_erase_add _ _ (Finset.mem_univ j)
      _ = ∑ i, y i := hsum
      _ =
          (∑ i ∈
              (Finset.univ : Finset (Fin (n + 1))).erase j,
              y i) + y j :=
        (Finset.sum_erase_add _ _ (Finset.mem_univ j)).symm
      _ =
          (∑ i ∈
              (Finset.univ : Finset (Fin (n + 1))).erase j,
              x i) + y j := by
        rw [hother]
  funext i
  by_cases hij : i = j
  · simpa [hij] using hj
  · obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq hij
    subst i
    exact congrFun hdeleted t

namespace SimplexHypergraph

noncomputable def deletionSlotFinset
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (deleted :
      DeletionFamily (fun _ : Fin (n + 1) => G)) :
    Finset (Fin (n + 1) × (Fin n → G)) := by
  classical
  exact Finset.univ.biUnion fun j =>
    (deleted j).image fun x =>
      (j, deletedVectorToFinTuple j x)

theorem mem_deletionSlotFinset
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (deleted :
      DeletionFamily (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1))
    (x : DeletedVector (fun _ : Fin (n + 1) => G) j)
    (hx : x ∈ deleted j) :
    (j, deletedVectorToFinTuple j x) ∈
      deletionSlotFinset deleted := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨j, Finset.mem_univ j, ?_⟩
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

theorem card_deletionSlotFinset_le_deletionCount
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (deleted :
      DeletionFamily (fun _ : Fin (n + 1) => G)) :
    (deletionSlotFinset deleted).card ≤
      deletionCount deleted := by
  classical
  calc
    (deletionSlotFinset deleted).card ≤
        ∑ j : Fin (n + 1),
          ((deleted j).image fun x =>
            (j, deletedVectorToFinTuple j x)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ j : Fin (n + 1), (deleted j).card := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.card_image_le
    _ = deletionCount deleted := rfl

end SimplexHypergraph

noncomputable def diagonalCoverColor
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted)
    (p : DiagonalAPParameter r N A) :
    Fin (r + 2) :=
  Classical.choose
    (hcover (diagonalAPSimplex r N A p)
      (diagonalAPSimplex_mem_simplexFinset r N A p))

@[simp]
theorem diagonalCoverColor_mem
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted)
    (p : DiagonalAPParameter r N A) :
    deleteCoordinate (diagonalAPSimplex r N A p)
        (diagonalCoverColor r N A deleted hcover p) ∈
      deleted (diagonalCoverColor r N A deleted hcover p) :=
  Classical.choose_spec
    (hcover (diagonalAPSimplex r N A p)
      (diagonalAPSimplex_mem_simplexFinset r N A p))

noncomputable def diagonalCoveredSlot
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted)
    (p : DiagonalAPParameter r N A) :
    Fin (r + 2) × (Fin (r + 1) → ZMod N) :=
  let j := diagonalCoverColor r N A deleted hcover p
  (j, deletedVectorToFinTuple j
    (deleteCoordinate (diagonalAPSimplex r N A p) j))

theorem diagonalCoveredSlot_mem_deletionSlotFinset
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted)
    (p : DiagonalAPParameter r N A) :
    diagonalCoveredSlot r N A deleted hcover p ∈
      SimplexHypergraph.deletionSlotFinset deleted := by
  classical
  exact SimplexHypergraph.mem_deletionSlotFinset deleted
    (diagonalCoverColor r N A deleted hcover p)
    (deleteCoordinate (diagonalAPSimplex r N A p)
      (diagonalCoverColor r N A deleted hcover p))
    (diagonalCoverColor_mem r N A deleted hcover p)

theorem diagonalCoveredSlot_injective
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted) :
    Function.Injective
      (diagonalCoveredSlot r N A deleted hcover) := by
  intro p q hpq
  apply diagonalAPSimplex_injective r N A
  apply eq_of_deletedVectorToFinTuple_eq_of_sum_eq
  · exact congrArg Prod.fst hpq
  · exact congrArg Prod.snd hpq
  · change
      simplexCoordinateSum (r + 2) N
          (diagonalAPSimplex r N A p) =
        simplexCoordinateSum (r + 2) N
          (diagonalAPSimplex r N A q)
    simp

@[simp]
theorem card_diagonalAPParameter
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N)) :
    Fintype.card (DiagonalAPParameter r N A) =
      A.card * N ^ r := by
  simp [DiagonalAPParameter, ZMod.card]

theorem card_diagonalAPParameter_le_deletionCount
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted) :
    Fintype.card (DiagonalAPParameter r N A) ≤
      SimplexHypergraph.deletionCount deleted := by
  classical
  let f := diagonalCoveredSlot r N A deleted hcover
  calc
    Fintype.card (DiagonalAPParameter r N A) =
        (Finset.univ.image f).card := by
      rw [Finset.card_image_of_injective _
        (diagonalCoveredSlot_injective r N A deleted hcover)]
      simp
    _ ≤
        (SimplexHypergraph.deletionSlotFinset deleted).card := by
      apply Finset.card_le_card
      intro y hy
      obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hy
      exact diagonalCoveredSlot_mem_deletionSlotFinset
        r N A deleted hcover p
    _ ≤ SimplexHypergraph.deletionCount deleted :=
      SimplexHypergraph.card_deletionSlotFinset_le_deletionCount
        deleted

@[simp]
theorem deletionCapacity_zmod
    (r N : ℕ) [NeZero N] :
    SimplexHypergraph.deletionCapacity
        (fun _ : Fin (r + 2) => ZMod N) =
      (r + 2) * N ^ (r + 1) := by
  simp [SimplexHypergraph.deletionCapacity, DeletedVector,
    Fintype.card_pi, ZMod.card]

theorem mean_finsetIndicator_div_le_normalizedDeletionCost
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted) :
    mean (finsetIndicator A) / (r + 2 : ℝ) ≤
      SimplexHypergraph.normalizedDeletionCost deleted := by
  have hcount :
      A.card * N ^ r ≤
        SimplexHypergraph.deletionCount deleted := by
    simpa using
      card_diagonalAPParameter_le_deletionCount
        r N A deleted hcover
  have hN : (N : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne N)
  rw [mean_finsetIndicator, ZMod.card,
    SimplexHypergraph.normalizedDeletionCost,
    deletionCapacity_zmod]
  calc
    (A.card : ℝ) / (N : ℝ) / (r + 2 : ℝ) =
        ((A.card * N ^ r : ℕ) : ℝ) /
          (((r + 2) * N ^ (r + 1) : ℕ) : ℝ) := by
      norm_num [Nat.cast_mul, Nat.cast_pow]
      field_simp
      ring
    _ ≤
        (SimplexHypergraph.deletionCount deleted : ℝ) /
          (((r + 2) * N ^ (r + 1) : ℕ) : ℝ) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast hcount
      · positivity

def HasUniformCyclicPartiteSimplexRemoval (k : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ c : ℝ, 0 < c ∧
      ∀ (N : ℕ) [NeZero N],
        ∀ H :
            SimplexHypergraph (fun _ : Fin k => ZMod N),
          H.toWeighted.simplexCount < c →
            ∃ deleted :
                SimplexHypergraph.DeletionFamily
                  (fun _ : Fin k => ZMod N),
              H.IsSimplexCover deleted ∧
                SimplexHypergraph.normalizedDeletionCost
                    deleted ≤ ε

theorem exists_uniformDenseAPCount_of_simplexRemoval
    (r : ℕ)
    (hrem :
      HasUniformCyclicPartiteSimplexRemoval (r + 2))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧
      HasUniformDenseAPCount (r + 2) δ c := by
  let ε : ℝ := (δ / (r + 2 : ℝ)) / 2
  have hk : 0 < (r + 2 : ℝ) := by positivity
  have hbase : 0 < δ / (r + 2 : ℝ) :=
    div_pos hδ hk
  have hε : 0 < ε := by
    exact div_pos hbase (by norm_num)
  obtain ⟨c, hc, hremove⟩ := hrem ε hε
  refine ⟨c, hc, ?_⟩
  intro N inst A hA
  by_contra hcount
  have hcount_lt :
      cyclicAPCount (r + 2) N (finsetIndicator A) < c :=
    lt_of_not_ge hcount
  have hsimplex_lt :
      (apSetHypergraph (r + 2) N A).toWeighted.simplexCount <
        c := by
    simpa [apSetHypergraph_simplexCount_eq_cyclicAPCount]
      using hcount_lt
  obtain ⟨deleted, hcover, hcost⟩ :=
    hremove N (apSetHypergraph (r + 2) N A) hsimplex_lt
  have hlower :
      mean (finsetIndicator A) / (r + 2 : ℝ) ≤
        SimplexHypergraph.normalizedDeletionCost deleted :=
    mean_finsetIndicator_div_le_normalizedDeletionCost
      r N A deleted hcover
  have hdensity :
      δ / (r + 2 : ℝ) ≤
        mean (finsetIndicator A) / (r + 2 : ℝ) :=
    div_le_div_of_nonneg_right hA hk.le
  have hε_lt : ε < δ / (r + 2 : ℝ) := by
    dsimp [ε]
    linarith
  linarith

theorem exists_uniformWeightedAPCount_of_simplexRemoval
    (r : ℕ)
    (hrem :
      HasUniformCyclicPartiteSimplexRemoval (r + 2))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧
      HasUniformWeightedAPCount (r + 2) δ c := by
  obtain ⟨c₀, hc₀, hdense⟩ :=
    exists_uniformDenseAPCount_of_simplexRemoval
      r hrem (half_pos hδ)
  refine ⟨(δ / 2) ^ (r + 2) * c₀, ?_, ?_⟩
  · exact mul_pos (pow_pos (half_pos hδ) _) hc₀
  · intro N inst g hg0 hg1 hmean
    exact weightedAPCount_of_denseAPCount
      hδ.le (hdense N) hg0 hg1 hmean

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def orderedFacet {n : ℕ} (j : Fin (n + 1)) :
    OrderedFace (n + 1) n :=
  Fin.succAboveOrderEmb j

noncomputable def orderedFacetEquiv (n : ℕ) :
    Fin (n + 1) ≃ OrderedFace (n + 1) n :=
  (Set.powersetCard.ofSingleton :
      Fin (n + 1) ≃ Set.powersetCard (Fin (n + 1)) 1) |>.trans
    ((Set.powersetCard.compl (m := n) (n := 1) (by simp) :
        Set.powersetCard (Fin (n + 1)) 1 ≃
          Set.powersetCard (Fin (n + 1)) n) |>.trans
      (Set.powersetCard.ofFinEmbEquiv :
        OrderedFace (n + 1) n ≃
          Set.powersetCard (Fin (n + 1)) n).symm)

@[simp]
theorem orderedFacetEquiv_apply
    {n : ℕ} (j : Fin (n + 1)) :
    orderedFacetEquiv n j = orderedFacet j := by
  apply OrderEmbedding.range_inj_of_wellFoundedLT.mp
  change
    Set.range ((orderedFacetEquiv n) j) =
      Set.range (Fin.succAboveOrderEmb j)
  rw [Fin.range_succAboveOrderEmb]
  ext i
  simp only [orderedFacetEquiv, Equiv.trans_apply]
  rw [
    Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem]
  rw [Set.powersetCard.mem_compl]
  change
    i ∉ ({j} : Finset (Fin (n + 1))) ↔
      i ∈ ({j} : Set (Fin (n + 1)))ᶜ
  simp

@[simp]
theorem deletedVectorToFinTuple_finTupleToDeletedVector
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (y : Fin n → G) :
    deletedVectorToFinTuple j
        (finTupleToDeletedVector j y) = y := by
  funext t
  simp [deletedVectorToFinTuple]

@[simp]
theorem finTupleToDeletedVector_deletedVectorToFinTuple
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : DeletedVector (fun _ : Fin (n + 1) => G) j) :
    finTupleToDeletedVector j
        (deletedVectorToFinTuple j x) = x := by
  funext i
  change
    x (finSuccAboveEquiv j
        ((finSuccAboveEquiv j).symm i)) = x i
  rw [(finSuccAboveEquiv j).apply_symm_apply]

noncomputable def deletedVectorFinTupleEquiv
    {G : Type*} {n : ℕ} (j : Fin (n + 1)) :
    DeletedVector (fun _ : Fin (n + 1) => G) j ≃
      (Fin n → G) where
  toFun := deletedVectorToFinTuple j
  invFun := finTupleToDeletedVector j
  left_inv := finTupleToDeletedVector_deletedVectorToFinTuple j
  right_inv := deletedVectorToFinTuple_finTupleToDeletedVector j

@[simp]
theorem deletedVectorToFinTuple_deleteCoordinate_eq_orderedFaceTuple
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : Fin (n + 1) → G) :
    deletedVectorToFinTuple j (deleteCoordinate x j) =
      orderedFaceTuple (orderedFacet j) x := by
  rfl

@[simp]
theorem finTupleToDeletedVector_orderedFaceTuple
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : Fin (n + 1) → G) :
    finTupleToDeletedVector j
        (orderedFaceTuple (orderedFacet j) x) =
      deleteCoordinate x j := by
  rw [←
    finTupleToDeletedVector_deletedVectorToFinTuple j
      (deleteCoordinate x j)]
  congr

noncomputable def SimplexHypergraph.toOrderedPattern
    {G : Type*} {n : ℕ}
    (H : SimplexHypergraph (fun _ : Fin (n + 1) => G)) :
    OrderedPattern G (n + 1) n where
  edge e y :=
    let j := (orderedFacetEquiv n).symm e
    H.edge j (finTupleToDeletedVector j y)

@[simp]
theorem SimplexHypergraph.toOrderedPattern_edge_orderedFacet
    {G : Type*} {n : ℕ}
    (H : SimplexHypergraph (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) (y : Fin n → G) :
    H.toOrderedPattern.edge (orderedFacet j) y ↔
      H.edge j (finTupleToDeletedVector j y) := by
  change
    H.edge ((orderedFacetEquiv n).symm (orderedFacet j))
        (finTupleToDeletedVector
          ((orderedFacetEquiv n).symm (orderedFacet j)) y) ↔
      H.edge j (finTupleToDeletedVector j y)
  have hj :
      (orderedFacetEquiv n).symm (orderedFacet j) = j := by
    rw [← orderedFacetEquiv_apply]
    exact (orderedFacetEquiv n).symm_apply_apply j
  rw [hj]

theorem SimplexHypergraph.toOrderedPattern_isOccurrence_iff
    {G : Type*} {n : ℕ}
    (H : SimplexHypergraph (fun _ : Fin (n + 1) => G))
    (x : Fin (n + 1) → G) :
    H.toOrderedPattern.IsOccurrence x ↔
      ∀ j, H.edge j (deleteCoordinate x j) := by
  constructor
  · intro hx j
    have hj := hx (orderedFacet j)
    rw [H.toOrderedPattern_edge_orderedFacet] at hj
    simpa using hj
  · intro hx e
    let j := (orderedFacetEquiv n).symm e
    have he : orderedFacet j = e := by
      rw [← orderedFacetEquiv_apply]
      exact (orderedFacetEquiv n).apply_symm_apply e
    rw [← he]
    rw [H.toOrderedPattern_edge_orderedFacet]
    simpa using hx j

theorem SimplexHypergraph.toOrderedPattern_occurrenceFinset
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (H : SimplexHypergraph (fun _ : Fin (n + 1) => G)) :
    H.toOrderedPattern.occurrenceFinset =
      H.simplexFinset := by
  ext x
  rw [OrderedPattern.mem_occurrenceFinset,
    SimplexHypergraph.mem_simplexFinset,
    H.toOrderedPattern_isOccurrence_iff]

theorem SimplexHypergraph.toOrderedPattern_patternCount
    {G : Type*} [Fintype G] [Nonempty G]
    {n : ℕ}
    (H : SimplexHypergraph (fun _ : Fin (n + 1) => G)) :
    H.toOrderedPattern.toWeighted.patternCount =
      H.toWeighted.simplexCount := by
  classical
  rw [OrderedPattern.toWeighted_patternCount_eq,
    SimplexHypergraph.toWeighted_simplexCount_eq_card_div,
    H.toOrderedPattern_occurrenceFinset]

noncomputable def orderedDeletionToSimplex
    {G : Type*} [DecidableEq G] {n : ℕ}
    (D : OrderedPattern.DeletionFamily
      (G := G) (n + 1) n) :
    SimplexHypergraph.DeletionFamily
      (fun _ : Fin (n + 1) => G) := by
  classical
  exact fun j =>
    (D (orderedFacet j)).image
      (finTupleToDeletedVector j)

@[simp]
theorem mem_orderedDeletionToSimplex_iff
    {G : Type*} [DecidableEq G] {n : ℕ}
    (D : OrderedPattern.DeletionFamily
      (G := G) (n + 1) n)
    (j : Fin (n + 1))
    (x : DeletedVector (fun _ : Fin (n + 1) => G) j) :
    x ∈ orderedDeletionToSimplex D j ↔
      deletedVectorToFinTuple j x ∈ D (orderedFacet j) := by
  classical
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
    rw [← hyx]
    simpa using hy
  · intro hx
    exact Finset.mem_image.mpr
      ⟨deletedVectorToFinTuple j x, hx,
        finTupleToDeletedVector_deletedVectorToFinTuple j x⟩

@[simp]
theorem card_orderedDeletionToSimplex
    {G : Type*} [DecidableEq G] {n : ℕ}
    (D : OrderedPattern.DeletionFamily
      (G := G) (n + 1) n)
    (j : Fin (n + 1)) :
    (orderedDeletionToSimplex D j).card =
      (D (orderedFacet j)).card := by
  classical
  rw [orderedDeletionToSimplex,
    Finset.card_image_of_injective _]
  intro y z hyz
  have htuple :=
    congrArg (deletedVectorToFinTuple j) hyz
  simpa using htuple

theorem SimplexHypergraph.isSimplexCover_orderedDeletionToSimplex
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (H : SimplexHypergraph (fun _ : Fin (n + 1) => G))
    (D : OrderedPattern.DeletionFamily
      (G := G) (n + 1) n)
    (hcover : H.toOrderedPattern.IsCover D) :
    H.IsSimplexCover (orderedDeletionToSimplex D) := by
  intro x hx
  have hxOrdered :
      x ∈ H.toOrderedPattern.occurrenceFinset := by
    rw [H.toOrderedPattern_occurrenceFinset]
    exact hx
  obtain ⟨e, he⟩ := hcover x hxOrdered
  let j := (orderedFacetEquiv n).symm e
  have heq : orderedFacet j = e := by
    rw [← orderedFacetEquiv_apply]
    exact (orderedFacetEquiv n).apply_symm_apply e
  refine ⟨j, (mem_orderedDeletionToSimplex_iff D j _).2 ?_⟩
  rw [
    deletedVectorToFinTuple_deleteCoordinate_eq_orderedFaceTuple,
    heq]
  exact he

theorem colorDeletionDensity_orderedDeletionToSimplex
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (D : OrderedPattern.DeletionFamily
      (G := G) (n + 1) n)
    (j : Fin (n + 1)) :
    SimplexHypergraph.colorDeletionDensity
        (orderedDeletionToSimplex D) j =
      OrderedPattern.faceDeletionDensity
        D (orderedFacet j) := by
  rw [SimplexHypergraph.colorDeletionDensity,
    OrderedPattern.faceDeletionDensity,
    card_orderedDeletionToSimplex]
  have hcard :
      Fintype.card
          (DeletedVector
            (fun _ : Fin (n + 1) => G) j) =
        Fintype.card (Fin n → G) :=
    Fintype.card_congr (deletedVectorFinTupleEquiv j)
  rw [hcard]

theorem normalizedDeletionCost_orderedDeletionToSimplex_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {n : ℕ}
    (D : OrderedPattern.DeletionFamily
      (G := G) (n + 1) n)
    {ε : ℝ}
    (hD :
      ∀ e, OrderedPattern.faceDeletionDensity D e ≤ ε) :
    SimplexHypergraph.normalizedDeletionCost
        (orderedDeletionToSimplex D) ≤ ε := by
  let M : ℕ := Fintype.card (Fin n → G)
  have hM : 0 < M := Fintype.card_pos
  have hface (j : Fin (n + 1)) :
      Fintype.card
          (DeletedVector
            (fun _ : Fin (n + 1) => G) j) = M := by
    exact Fintype.card_congr (deletedVectorFinTupleEquiv j)
  have hcard (j : Fin (n + 1)) :
      ((orderedDeletionToSimplex D j).card : ℝ) ≤
        ε * M := by
    have hdensity :=
      colorDeletionDensity_orderedDeletionToSimplex D j
    have hbound := hD (orderedFacet j)
    rw [← hdensity] at hbound
    rw [SimplexHypergraph.colorDeletionDensity,
      hface] at hbound
    have hMR : (0 : ℝ) < M := by
      exact_mod_cast hM
    exact (div_le_iff₀ hMR).mp hbound
  have hcount :
      (SimplexHypergraph.deletionCount
          (orderedDeletionToSimplex D) : ℝ) ≤
        (n + 1 : ℝ) * (ε * M) := by
    calc
      (SimplexHypergraph.deletionCount
          (orderedDeletionToSimplex D) : ℝ) =
          ∑ j : Fin (n + 1),
            ((orderedDeletionToSimplex D j).card : ℝ) := by
        simp [SimplexHypergraph.deletionCount]
      _ ≤ ∑ _j : Fin (n + 1), ε * M :=
        Finset.sum_le_sum fun j _ => hcard j
      _ = (n + 1 : ℝ) * (ε * M) := by
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
        (orderedDeletionToSimplex D) : ℝ) ≤
        (n + 1 : ℝ) * (ε * M) := hcount
    _ = ε * (((n + 1) * M : ℕ) : ℝ) := by
      push_cast
      ring

theorem hasUniformCyclicPartiteSimplexRemoval_of_ordered
    (n : ℕ)
    (hordered :
      HasUniformOrderedPatternRemoval (n + 1) n) :
    HasUniformCyclicPartiteSimplexRemoval (n + 1) := by
  intro ε hε
  obtain ⟨c, hc, hremove⟩ := hordered ε hε
  refine ⟨c, hc, ?_⟩
  intro N inst H hcount
  have horderedCount :
      H.toOrderedPattern.toWeighted.patternCount < c := by
    rw [H.toOrderedPattern_patternCount]
    exact hcount
  obtain ⟨D, hcover, hD⟩ :=
    hremove (ZMod N) H.toOrderedPattern horderedCount
  exact
    ⟨orderedDeletionToSimplex D,
      H.isSimplexCover_orderedDeletionToSimplex D hcover,
      normalizedDeletionCost_orderedDeletionToSimplex_le D hD⟩

theorem hasUniformCyclicPartiteSimplexRemoval_add_two_of_ordered
    (r : ℕ)
    (hordered :
      HasUniformOrderedPatternRemoval (r + 2) (r + 1)) :
    HasUniformCyclicPartiteSimplexRemoval (r + 2) := by
  simpa [Nat.add_assoc] using
    (hasUniformCyclicPartiteSimplexRemoval_of_ordered
      (r + 1) (by simpa [Nat.add_assoc] using hordered))

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

theorem exists_uniformDenseAPCount_of_orderedRemoval
    (r : ℕ)
    (hordered :
      HasUniformOrderedPatternRemoval (r + 2) (r + 1))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧
      HasUniformDenseAPCount (r + 2) δ c :=
  exists_uniformDenseAPCount_of_simplexRemoval r
    (hasUniformCyclicPartiteSimplexRemoval_add_two_of_ordered
      r hordered)
    hδ

theorem exists_uniformWeightedAPCount_of_orderedRemoval
    (r : ℕ)
    (hordered :
      HasUniformOrderedPatternRemoval (r + 2) (r + 1))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧
      HasUniformWeightedAPCount (r + 2) δ c :=
  exists_uniformWeightedAPCount_of_simplexRemoval r
    (hasUniformCyclicPartiteSimplexRemoval_add_two_of_ordered
      r hordered)
    hδ

theorem exists_uniformDenseAPCount_of_orderedRemoval_of_two_le
    (k : ℕ) (hk : 2 ≤ k)
    (hordered :
      HasUniformOrderedPatternRemoval k (k - 1))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧
      HasUniformDenseAPCount k δ c := by
  have hcolors : k - 2 + 2 = k := by
    omega
  have hrank : k - 2 + 1 = k - 1 := by
    omega
  have hordered' :
      HasUniformOrderedPatternRemoval
        (k - 2 + 2) (k - 2 + 1) := by
    simpa only [hcolors, hrank] using hordered
  simpa only [hcolors] using
    (exists_uniformDenseAPCount_of_orderedRemoval
      (k - 2) hordered' hδ)

theorem exists_uniformWeightedAPCount_of_orderedRemoval_of_two_le
    (k : ℕ) (hk : 2 ≤ k)
    (hordered :
      HasUniformOrderedPatternRemoval k (k - 1))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧
      HasUniformWeightedAPCount k δ c := by
  have hcolors : k - 2 + 2 = k := by
    omega
  have hrank : k - 2 + 1 = k - 1 := by
    omega
  have hordered' :
      HasUniformOrderedPatternRemoval
        (k - 2 + 2) (k - 2 + 1) := by
    simpa only [hcolors, hrank] using hordered
  simpa only [hcolors] using
    (exists_uniformWeightedAPCount_of_orderedRemoval
      (k - 2) hordered' hδ)

end Erdos3.FixedDensity

end

end OAI
