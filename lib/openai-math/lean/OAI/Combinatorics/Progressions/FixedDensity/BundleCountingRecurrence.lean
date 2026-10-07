-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import OAI.Combinatorics.Progressions.FixedDensity.Energy
import OAI.Compat.BigOperators

namespace OAI

section

namespace Erdos3.FixedDensity

theorem mean_mul_sq_le_product
    {Ω : Type*} [Fintype Ω]
    (u v : Ω → ℝ) :
    mean (fun x => u x * v x) ^ 2 ≤
      mean (fun x => u x ^ 2) *
        mean (fun x => v x ^ 2) := by
  simpa [mean] using
    (Finset.expect_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset Ω) u v)

theorem mean_sq_eq_mean_pair_mul
    {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) :
    mean f ^ 2 =
      mean (fun p : Ω × Ω => f p.1 * f p.2) := by
  calc
    mean f ^ 2 = mean f * mean f := pow_two _
    _ = mean₂ (fun x y => f x * f y) := by
      unfold mean₂ mean
      exact
        Finset.expect_mul_expect
          Finset.univ Finset.univ f f
    _ = mean (fun p : Ω × Ω => f p.1 * f p.2) :=
      (mean_prod_type fun x y => f x * f y).symm

theorem mean_inner_sq_eq_mean₂_pair
    {X Y : Type*} [Fintype X] [Fintype Y]
    (F : X → Y → ℝ) :
    mean (fun x => mean (F x) ^ 2) =
      mean₂ (fun x => fun p : Y × Y =>
        F x p.1 * F x p.2) := by
  unfold mean₂
  apply congrArg mean
  funext x
  exact mean_sq_eq_mean_pair_mul (F x)

theorem mean_square_le_mean_square
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) :
    mean f ^ 2 ≤ mean (fun x => f x ^ 2) := by
  have h :=
    Finset.expect_mul_sq_le_sq_mul_sq
      Finset.univ f (fun _ : Ω => (1 : ℝ))
  simpa [mean] using h

theorem mean_pow_two_le_mean_pow_two
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) (hf : ∀ x, 0 ≤ f x) (n : ℕ) :
    mean f ^ (2 ^ n) ≤
      mean (fun x => f x ^ (2 ^ n)) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hmean0 : 0 ≤ mean f := mean_nonneg hf
      have hright0 :
          0 ≤ mean (fun x => f x ^ (2 ^ n)) :=
        mean_nonneg fun x => pow_nonneg (hf x) _
      have hsquare :
          (mean f ^ (2 ^ n)) ^ 2 ≤
            mean (fun x => f x ^ (2 ^ n)) ^ 2 := by
        simpa [pow_two] using
          mul_self_le_mul_self
            (pow_nonneg hmean0 _) ih
      calc
        mean f ^ (2 ^ (n + 1)) =
            (mean f ^ (2 ^ n)) ^ 2 := by
          rw [show 2 ^ (n + 1) = 2 ^ n * 2 by
            rw [pow_succ], pow_mul]
        _ ≤ mean (fun x => f x ^ (2 ^ n)) ^ 2 :=
          hsquare
        _ ≤ mean (fun x =>
            (f x ^ (2 ^ n)) ^ 2) :=
          mean_square_le_mean_square _
        _ = mean (fun x => f x ^ (2 ^ (n + 1))) := by
          apply congrArg mean
          funext x
          rw [show 2 ^ (n + 1) = 2 ^ n * 2 by
            rw [pow_succ], pow_mul]

theorem mean_pow_two_le_mean_pow_two_of_pos
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) {n : ℕ} (hn : 0 < n) :
    mean f ^ (2 ^ n) ≤
      mean (fun x => f x ^ (2 ^ n)) := by
  have heven : Even (2 ^ n) :=
    even_two.pow_of_ne_zero (Nat.ne_of_gt hn)
  have habs :
      |mean f| ≤ mean (fun x => |f x|) := by
    exact Finset.abs_expect_le Finset.univ f
  calc
    mean f ^ (2 ^ n) = |mean f| ^ (2 ^ n) :=
      (heven.pow_abs (mean f)).symm
    _ ≤ mean (fun x => |f x|) ^ (2 ^ n) :=
      pow_le_pow_left₀ (abs_nonneg _) habs _
    _ ≤ mean (fun x => |f x| ^ (2 ^ n)) :=
      mean_pow_two_le_mean_pow_two
        (fun x => |f x|) (fun x => abs_nonneg (f x)) n
    _ = mean (fun x => f x ^ (2 ^ n)) := by
      apply congrArg mean
      funext x
      exact heven.pow_abs (f x)

theorem mean_pow_two_le_mean_pow_two'
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) (n : ℕ) :
    mean f ^ (2 ^ n) ≤
      mean (fun x => f x ^ (2 ^ n)) := by
  cases n with
  | zero => simp
  | succ n =>
      exact mean_pow_two_le_mean_pow_two_of_pos f (Nat.succ_pos n)

theorem cauchySchwarz_eliminate_outer_factor
    {X Y : Type*} [Fintype X] [Nonempty X] [Fintype Y]
    (u : X → ℝ) (F : X → Y → ℝ)
    (hu : ∀ x, |u x| ≤ 1) :
    mean₂ (fun x y => u x * F x y) ^ 2 ≤
      mean₂ (fun x => fun p : Y × Y =>
        F x p.1 * F x p.2) := by
  have hrewrite :
      mean₂ (fun x y => u x * F x y) =
        mean (fun x => u x * mean (F x)) := by
    unfold mean₂
    apply congrArg mean
    funext x
    exact mean_smul (u x) (F x)
  rw [hrewrite]
  calc
    mean (fun x => u x * mean (F x)) ^ 2 ≤
        mean (fun x => u x ^ 2) *
          mean (fun x => mean (F x) ^ 2) :=
      mean_mul_sq_le_product u (fun x => mean (F x))
    _ ≤ mean (fun x => mean (F x) ^ 2) := by
      have huSq : mean (fun x => u x ^ 2) ≤ 1 := by
        apply mean_le_of_le_const
        intro x
        have hx := abs_le.mp (hu x)
        nlinarith [sq_nonneg (u x - 1), sq_nonneg (u x + 1)]
      have hmeanSq :
          0 ≤ mean (fun x => mean (F x) ^ 2) :=
        mean_nonneg fun x => sq_nonneg _
      exact mul_le_of_le_one_left hmeanSq huSq
    _ = mean₂ (fun x => fun p : Y × Y =>
          F x p.1 * F x p.2) :=
      mean_inner_sq_eq_mean₂_pair F

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

structure HypergraphBundle
    (J K : Type*) [DecidableEq J] [DecidableEq K]
    (H : Finset (Finset J)) where
  edges : Finset (Finset K)
  projection : K → J
  projection_injective_on_edge :
    ∀ g ∈ edges, Set.InjOn projection (g : Set K)
  projection_mem_base :
    ∀ g ∈ edges, g.image projection ∈ H

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

def IsClosedUnderInclusion
    (B : HypergraphBundle J K H) : Prop :=
  ∀ ⦃g⦄, g ∈ B.edges →
    ∀ ⦃f⦄, f ⊆ g → f ∈ B.edges

def order (B : HypergraphBundle J K H) : ℕ :=
  B.edges.sup Finset.card

def edgeCountAtRank
    (B : HypergraphBundle J K H) (r : ℕ) : ℕ :=
  (B.edges.filter fun g => g.card = r).card

theorem edge_card_le_order
    (B : HypergraphBundle J K H)
    {g : Finset K} (hg : g ∈ B.edges) :
    g.card ≤ B.order := by
  exact Finset.le_sup hg

def eraseEdge
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    HypergraphBundle J K H where
  edges := B.edges.erase g₀
  projection := B.projection
  projection_injective_on_edge := by
    intro g hg
    exact B.projection_injective_on_edge g
      (Finset.mem_of_mem_erase hg)
  projection_mem_base := by
    intro g hg
    exact B.projection_mem_base g
      (Finset.mem_of_mem_erase hg)

@[simp]
theorem eraseEdge_edges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.eraseEdge g₀).edges = B.edges.erase g₀ :=
  rfl

theorem eraseEdge_order_le
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.eraseEdge g₀).order ≤ B.order := by
  unfold order eraseEdge
  apply Finset.sup_le
  intro g hg
  exact B.edge_card_le_order (Finset.mem_of_mem_erase hg)

theorem edgeCountAtRank_eraseEdge
    (B : HypergraphBundle J K H)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    {r : ℕ} (hr : g₀.card = r) :
    (B.eraseEdge g₀).edgeCountAtRank r =
      B.edgeCountAtRank r - 1 := by
  unfold edgeCountAtRank eraseEdge
  have hmem :
      g₀ ∈ B.edges.filter fun g => g.card = r :=
    Finset.mem_filter.mpr ⟨hg₀, hr⟩
  have hfilter :
      (B.edges.erase g₀).filter
          (fun g => g.card = r) =
        (B.edges.filter fun g => g.card = r).erase g₀ := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_erase]
    aesop
  rw [hfilter, Finset.card_erase_of_mem hmem]

theorem eraseEdge_closed_of_maximal
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    {g₀ : Finset K} (_hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card) :
    (B.eraseEdge g₀).IsClosedUnderInclusion := by
  intro g hg f hfg
  have hgB : g ∈ B.edges :=
    Finset.mem_of_mem_erase hg
  have hfB : f ∈ B.edges :=
    hclosed hgB hfg
  apply Finset.mem_erase.mpr
  refine ⟨?_, hfB⟩
  intro hfg₀
  subst f
  have hcard₂ : g.card ≤ g₀.card :=
    hmax g hgB
  have heq : g₀ = g :=
    Finset.eq_of_subset_of_card_le hfg hcard₂
  exact (Finset.mem_erase.mp hg).1 heq.symm

def edgeTuple
    (g : Finset K) (x : K → G) :
    ({v : K // v ∈ g} → G) :=
  fun v => x v.1

noncomputable def projectionEquiv
    (B : HypergraphBundle J K H)
    {g : Finset K} (hg : g ∈ B.edges) :
    {v : K // v ∈ g} ≃
      {j : J // j ∈ g.image B.projection} := by
  classical
  apply Equiv.ofBijective
    (fun v : {v : K // v ∈ g} =>
      (⟨B.projection v.1,
        Finset.mem_image.mpr ⟨v.1, v.2, rfl⟩⟩ :
        {j : J // j ∈ g.image B.projection}))
  constructor
  · intro v w hvw
    apply Subtype.ext
    apply B.projection_injective_on_edge g hg v.2 w.2
    exact congrArg Subtype.val hvw
  · intro j
    obtain ⟨v, hv, hvj⟩ :=
      Finset.mem_image.mp j.2
    refine ⟨⟨v, hv⟩, ?_⟩
    apply Subtype.ext
    exact hvj

noncomputable def projectedEdgeTuple
    (B : HypergraphBundle J K H)
    {g : Finset K} (hg : g ∈ B.edges)
    (y : {v : K // v ∈ g} → G) :
    ({j : J // j ∈ g.image B.projection} → G) :=
  fun j => y ((B.projectionEquiv hg).symm j)

abbrev BaseEdgeWeight
    (J G : Type*) :=
  (e : Finset J) → ({j : J // j ∈ e} → G) → ℝ

def BaseWeightsInUnitInterval
    (H : Finset (Finset J))
    (A : BaseEdgeWeight J G) : Prop :=
  ∀ e ∈ H, ∀ y, 0 ≤ A e y ∧ A e y ≤ 1

noncomputable def pullbackBaseEdgeWeight
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G) :
    (g : Finset K) → ({v : K // v ∈ g} → G) → ℝ := by
  classical
  intro g y
  by_cases hg : g ∈ B.edges
  · exact A (g.image B.projection)
      (B.projectedEdgeTuple hg y)
  · exact 1

@[simp]
theorem pullbackBaseEdgeWeight_of_mem
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G)
    {g : Finset K} (hg : g ∈ B.edges)
    (y : {v : K // v ∈ g} → G) :
    B.pullbackBaseEdgeWeight A g y =
      A (g.image B.projection)
        (B.projectedEdgeTuple hg y) := by
  classical
  simp [pullbackBaseEdgeWeight, hg]

theorem pullbackBaseEdgeWeight_unitInterval
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsInUnitInterval H A)
    {g : Finset K} (hg : g ∈ B.edges)
    (y : {v : K // v ∈ g} → G) :
    0 ≤ B.pullbackBaseEdgeWeight A g y ∧
      B.pullbackBaseEdgeWeight A g y ≤ 1 := by
  rw [B.pullbackBaseEdgeWeight_of_mem A hg y]
  exact hA _ (B.projection_mem_base g hg) _

def WeightsInUnitInterval
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) : Prop :=
  ∀ g ∈ B.edges, ∀ y, 0 ≤ A g y ∧ A g y ≤ 1

theorem pullbackBaseEdgeWeight_weightsInUnitInterval
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsInUnitInterval H A) :
    B.WeightsInUnitInterval
      (B.pullbackBaseEdgeWeight A) := by
  intro g hg y
  exact B.pullbackBaseEdgeWeight_unitInterval A hA hg y

noncomputable def bundleProduct
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (x : K → G) : ℝ :=
  ∏ g ∈ B.edges, A g (edgeTuple g x)

noncomputable def bundleCount
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) : ℝ :=
  mean (B.bundleProduct A)

theorem bundleProduct_nonneg
    (B : HypergraphBundle J K H)
    {A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ}
    (hA : B.WeightsInUnitInterval A)
    (x : K → G) :
    0 ≤ B.bundleProduct A x := by
  unfold bundleProduct
  exact Finset.prod_nonneg fun g hg =>
    (hA g hg (edgeTuple g x)).1

theorem bundleProduct_le_one
    (B : HypergraphBundle J K H)
    {A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ}
    (hA : B.WeightsInUnitInterval A)
    (x : K → G) :
    B.bundleProduct A x ≤ 1 := by
  unfold bundleProduct
  apply Finset.prod_le_one₀
  · intro g hg
    exact (hA g hg (edgeTuple g x)).1
  · intro g hg
    exact (hA g hg (edgeTuple g x)).2

theorem bundleCount_nonneg
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    {A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ}
    (hA : B.WeightsInUnitInterval A) :
    0 ≤ B.bundleCount A :=
  mean_nonneg (B.bundleProduct_nonneg hA)

theorem bundleCount_le_one
    [Fintype K] [Fintype G] [Nonempty G]
    (B : HypergraphBundle J K H)
    {A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ}
    (hA : B.WeightsInUnitInterval A) :
    B.bundleCount A ≤ 1 :=
  mean_le_of_le_const (B.bundleProduct_le_one hA)

theorem WeightsInUnitInterval.eraseEdge
    (B : HypergraphBundle J K H)
    {A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ}
    (hA : B.WeightsInUnitInterval A)
    (g₀ : Finset K) :
    (B.eraseEdge g₀).WeightsInUnitInterval A := by
  intro g hg y
  exact hA g (Finset.mem_of_mem_erase hg) y

noncomputable def edgeRemainder
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (x : K → G) : ℝ :=
  (B.eraseEdge g₀).bundleProduct A x

noncomputable def edgeContribution
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) : ℝ :=
  mean (fun x : K → G =>
    q (edgeTuple g₀ x) * B.edgeRemainder g₀ A x)

theorem bundleCount_eq_edgeContribution
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges) :
    B.bundleCount A =
      B.edgeContribution g₀ (A g₀) A := by
  unfold bundleCount edgeContribution edgeRemainder
  apply congrArg mean
  funext x
  exact
    (Finset.mul_prod_erase B.edges
      (fun g => A g (edgeTuple g x)) hg₀).symm

theorem bundleCount_decompose_edge
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (p : ℝ)
    (b c : ({v : K // v ∈ g₀} → G) → ℝ)
    (hdecomp : ∀ y, A g₀ y = p + b y + c y) :
    B.bundleCount A =
      p * (B.eraseEdge g₀).bundleCount A +
        B.edgeContribution g₀ b A +
        B.edgeContribution g₀ c A := by
  rw [B.bundleCount_eq_edgeContribution A hg₀]
  unfold edgeContribution bundleCount
  calc
    mean (fun x : K → G =>
        A g₀ (edgeTuple g₀ x) *
          B.edgeRemainder g₀ A x) =
        mean (fun x : K → G =>
          p * B.edgeRemainder g₀ A x +
            b (edgeTuple g₀ x) *
              B.edgeRemainder g₀ A x +
            c (edgeTuple g₀ x) *
              B.edgeRemainder g₀ A x) := by
      apply congrArg mean
      funext x
      rw [hdecomp]
      ring
    _ =
        mean (fun x : K → G =>
          p * B.edgeRemainder g₀ A x) +
          mean (fun x : K → G =>
            b (edgeTuple g₀ x) *
              B.edgeRemainder g₀ A x) +
          mean (fun x : K → G =>
            c (edgeTuple g₀ x) *
              B.edgeRemainder g₀ A x) := by
      rw [mean_add, mean_add]
    _ =
        p * (B.eraseEdge g₀).bundleCount A +
          B.edgeContribution g₀ b A +
          B.edgeContribution g₀ c A := by
      rw [mean_smul]
      rfl

theorem edgeContribution_const
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (p : ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.edgeContribution g₀ (fun _ => p) A =
      p * (B.eraseEdge g₀).bundleCount A := by
  unfold edgeContribution bundleCount
  rw [← mean_smul]
  rfl

abbrev EdgeComplement (g : Finset K) :=
  {v : K // v ∉ g}

noncomputable def edgeSumEquiv (g : Finset K) :
    {v : K // v ∈ g} ⊕ EdgeComplement g ≃ K :=
  Equiv.sumCompl fun v : K => v ∈ g

noncomputable def splitEdgeEquiv
    (g : Finset K) :
    (K → G) ≃
      (({v : K // v ∈ g} → G) ×
        (EdgeComplement g → G)) :=
  (Equiv.piCongrLeft (fun _ : K => G)
      (edgeSumEquiv g)).symm.trans
    (Equiv.sumPiEquivProdPi
      (fun _ : {v : K // v ∈ g} ⊕
        EdgeComplement g => G))

@[simp]
theorem splitEdgeEquiv_fst
    (g : Finset K) (x : K → G) :
    (splitEdgeEquiv g x).1 = edgeTuple g x := by
  funext v
  simp [splitEdgeEquiv, edgeSumEquiv, edgeTuple]

@[simp]
theorem edgeTuple_splitEdgeEquiv_symm
    (g : Finset K)
    (y : {v : K // v ∈ g} → G)
    (z : EdgeComplement g → G) :
    edgeTuple g ((splitEdgeEquiv g).symm (y, z)) = y := by
  rw [← splitEdgeEquiv_fst]
  simp

theorem mean_splitEdge
    [Fintype K] [Fintype G]
    (g : Finset K) (f : (K → G) → ℝ) :
    mean f =
      mean₂ (fun y : {v : K // v ∈ g} → G =>
        fun z : EdgeComplement g → G =>
          f ((splitEdgeEquiv g).symm (y, z))) := by
  calc
    mean f =
        mean (fun p :
          ({v : K // v ∈ g} → G) ×
            (EdgeComplement g → G) =>
              f ((splitEdgeEquiv g).symm p)) := by
      unfold mean
      apply Fintype.expect_equiv (splitEdgeEquiv g)
      intro x
      simp
    _ = _ := by
      simpa only [Prod.eta] using
        (mean_prod_type
          (fun y : {v : K // v ∈ g} → G =>
            fun z : EdgeComplement g → G =>
              f ((splitEdgeEquiv g).symm (y, z))))

noncomputable def edgeRemainderFiber
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (y : {v : K // v ∈ g₀} → G)
    (z : EdgeComplement g₀ → G) : ℝ :=
  B.edgeRemainder g₀ A
    ((splitEdgeEquiv g₀).symm (y, z))

noncomputable def edgeRemainderAverage
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (y : {v : K // v ∈ g₀} → G) : ℝ :=
  mean (B.edgeRemainderFiber g₀ A y)

theorem edgeContribution_eq_mean_mul_remainderAverage
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.edgeContribution g₀ q A =
      mean (fun y =>
        q y * B.edgeRemainderAverage g₀ A y) := by
  unfold edgeContribution
  rw [mean_splitEdge g₀]
  unfold mean₂ edgeRemainderAverage edgeRemainderFiber
  apply congrArg mean
  funext y
  simp only [edgeTuple_splitEdgeEquiv_symm]
  rw [mean_smul]

noncomputable def frozenEdgeCorrelation
    [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (z : EdgeComplement g₀ → G) : ℝ :=
  mean (fun y =>
    q y * B.edgeRemainderFiber g₀ A y z)

theorem edgeContribution_eq_mean_frozenEdgeCorrelation
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.edgeContribution g₀ q A =
      mean (B.frozenEdgeCorrelation g₀ q A) := by
  unfold edgeContribution
  rw [mean_splitEdge g₀, mean₂_comm]
  unfold frozenEdgeCorrelation edgeRemainderFiber mean₂
  apply congrArg mean
  funext z
  apply congrArg mean
  funext y
  change
    q (edgeTuple g₀
        ((splitEdgeEquiv g₀).symm (y, z))) *
        B.edgeRemainder g₀ A
          ((splitEdgeEquiv g₀).symm (y, z)) =
      q y *
        B.edgeRemainder g₀ A
          ((splitEdgeEquiv g₀).symm (y, z))
  rw [edgeTuple_splitEdgeEquiv_symm]

theorem abs_edgeContribution_le_of_frozen
    [Fintype K] [Fintype G] [Nonempty G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    {ε : ℝ}
    (hfrozen :
      ∀ z, |B.frozenEdgeCorrelation g₀ q A z| ≤ ε) :
    |B.edgeContribution g₀ q A| ≤ ε := by
  rw [B.edgeContribution_eq_mean_frozenEdgeCorrelation]
  calc
    |mean (B.frozenEdgeCorrelation g₀ q A)| ≤
        mean (fun z =>
          |B.frozenEdgeCorrelation g₀ q A z|) :=
      Finset.abs_expect_le Finset.univ _
    _ ≤ mean (fun _z : EdgeComplement g₀ → G => ε) :=
      mean_mono hfrozen
    _ = ε := mean_const _

noncomputable def doubledRemainderMoment
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) : ℝ :=
  mean (fun y =>
    B.edgeRemainderAverage g₀ A y ^ 2)

theorem doubledRemainderMoment_nonneg
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    0 ≤ B.doubledRemainderMoment g₀ A :=
  mean_nonneg fun _ => sq_nonneg _

theorem edgeRemainderAverage_unitInterval
    [Fintype K] [Fintype G] [Nonempty G]
    (B : HypergraphBundle J K H)
    {A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ}
    (hA : B.WeightsInUnitInterval A)
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G) :
    0 ≤ B.edgeRemainderAverage g₀ A y ∧
      B.edgeRemainderAverage g₀ A y ≤ 1 := by
  constructor
  · apply mean_nonneg
    intro z
    exact
      (B.eraseEdge g₀).bundleProduct_nonneg
        (hA.eraseEdge B g₀) _
  · apply mean_le_of_le_const
    intro z
    exact
      (B.eraseEdge g₀).bundleProduct_le_one
        (hA.eraseEdge B g₀) _

theorem doubledRemainderMoment_le_one
    [Fintype K] [Fintype G] [Nonempty G]
    (B : HypergraphBundle J K H)
    {A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ}
    (hA : B.WeightsInUnitInterval A)
    (g₀ : Finset K) :
    B.doubledRemainderMoment g₀ A ≤ 1 := by
  unfold doubledRemainderMoment
  apply mean_le_of_le_const
  intro y
  have hy :=
    B.edgeRemainderAverage_unitInterval hA g₀ y
  nlinarith

theorem doubledRemainderMoment_eq_mean₂_pair
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.doubledRemainderMoment g₀ A =
      mean₂ (fun y :
          {v : K // v ∈ g₀} → G =>
        fun z :
          (EdgeComplement g₀ → G) ×
            (EdgeComplement g₀ → G) =>
          B.edgeRemainderFiber g₀ A y z.1 *
            B.edgeRemainderFiber g₀ A y z.2) := by
  unfold doubledRemainderMoment edgeRemainderAverage
  exact mean_inner_sq_eq_mean₂_pair
    (B.edgeRemainderFiber g₀ A)

theorem edgeContribution_sq_le_localSquare_mul_doubled
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.edgeContribution g₀ q A ^ 2 ≤
      mean (fun y => q y ^ 2) *
        B.doubledRemainderMoment g₀ A := by
  rw [B.edgeContribution_eq_mean_mul_remainderAverage]
  exact mean_mul_sq_le_product q
    (B.edgeRemainderAverage g₀ A)

theorem edgeContribution_sq_le_of_localized_defect
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (b base : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (β : ℝ)
    (hlocalized :
      mean (fun y => b y ^ 2) ≤
        β * mean base) :
    B.edgeContribution g₀ b A ^ 2 ≤
      (β * mean base) *
        B.doubledRemainderMoment g₀ A := by
  calc
    B.edgeContribution g₀ b A ^ 2 ≤
        mean (fun y => b y ^ 2) *
          B.doubledRemainderMoment g₀ A :=
      B.edgeContribution_sq_le_localSquare_mul_doubled
        g₀ b A
    _ ≤
        (β * mean base) *
          B.doubledRemainderMoment g₀ A :=
      mul_le_mul_of_nonneg_right hlocalized
        (B.doubledRemainderMoment_nonneg g₀ A)

theorem edgeContribution_sq_le_of_localized_defect_unitInterval
    [Fintype K] [Fintype G] [Nonempty G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (b base : ({v : K // v ∈ g₀} → G) → ℝ)
    {A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ}
    (hA : B.WeightsInUnitInterval A)
    {β : ℝ} (hβ : 0 ≤ β)
    (hbase : ∀ y, 0 ≤ base y)
    (hlocalized :
      mean (fun y => b y ^ 2) ≤
        β * mean base) :
    B.edgeContribution g₀ b A ^ 2 ≤
      β * mean base := by
  calc
    B.edgeContribution g₀ b A ^ 2 ≤
        (β * mean base) *
          B.doubledRemainderMoment g₀ A :=
      B.edgeContribution_sq_le_of_localized_defect
        g₀ b base A β hlocalized
    _ ≤ β * mean base := by
      apply mul_le_of_le_one_right
      · exact mul_nonneg hβ (mean_nonneg hbase)
      · exact B.doubledRemainderMoment_le_one hA g₀

end HypergraphBundle

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem abs_finiteCount_sub_prod_le_card_mul
    {ι : Type*} [DecidableEq ι]
    (count : Finset ι → ℝ)
    (p : ι → ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hempty : count ∅ = 1)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hstep :
      ∀ s : Finset ι, s.Nonempty →
        ∃ e ∈ s,
          |count s - p e * count (s.erase e)| ≤ δ)
    (s : Finset ι) :
    |count s - ∏ e ∈ s, p e| ≤
      (s.card : ℝ) * δ := by
  refine Finset.strongInductionOn s ?_
  intro s ih
  by_cases hs : s = ∅
  · subst s
    simp [hempty]
  · have hsne : s.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hs
    obtain ⟨e, he, hrec⟩ := hstep s hsne
    have herase : s.erase e ⊂ s :=
      Finset.erase_ssubset he
    have hind :
        |count (s.erase e) -
            ∏ f ∈ s.erase e, p f| ≤
          ((s.erase e).card : ℝ) * δ :=
      ih (s.erase e) herase
    have hpe0 : 0 ≤ p e := (hp e).1
    have hpe1 : p e ≤ 1 := (hp e).2
    have hright0 :
        0 ≤ ((s.erase e).card : ℝ) * δ :=
      mul_nonneg (Nat.cast_nonneg _) hδ
    have hprod :
        (∏ f ∈ s, p f) =
          p e * ∏ f ∈ s.erase e, p f := by
      exact
        (Finset.mul_prod_erase s p he).symm
    calc
      |count s - ∏ f ∈ s, p f| =
          |(count s - p e * count (s.erase e)) +
            p e *
              (count (s.erase e) -
                ∏ f ∈ s.erase e, p f)| := by
        rw [hprod]
        congr 1
        ring
      _ ≤
          |count s - p e * count (s.erase e)| +
            |p e *
              (count (s.erase e) -
                ∏ f ∈ s.erase e, p f)| :=
        abs_add_le _ _
      _ =
          |count s - p e * count (s.erase e)| +
            p e *
              |count (s.erase e) -
                ∏ f ∈ s.erase e, p f| := by
        rw [abs_mul, abs_of_nonneg hpe0]
      _ ≤
          δ + p e *
            (((s.erase e).card : ℝ) * δ) := by
        exact add_le_add hrec
          (mul_le_mul_of_nonneg_left hind hpe0)
      _ ≤
          δ + ((s.erase e).card : ℝ) * δ := by
        exact add_le_add le_rfl
          (mul_le_of_le_one_left hright0 hpe1)
      _ = (s.card : ℝ) * δ := by
        rw [Finset.card_erase_of_mem he]
        have hcard : 1 ≤ s.card :=
          Finset.one_le_card.mpr hsne
        rw [Nat.cast_sub hcard]
        ring

theorem finiteCount_prod_sub_card_mul_le
    {ι : Type*} [DecidableEq ι]
    (count : Finset ι → ℝ)
    (p : ι → ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hempty : count ∅ = 1)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hstep :
      ∀ s : Finset ι, s.Nonempty →
        ∃ e ∈ s,
          |count s - p e * count (s.erase e)| ≤ δ)
    (s : Finset ι) :
    (∏ e ∈ s, p e) - (s.card : ℝ) * δ ≤
      count s := by
  have habs :=
    abs_finiteCount_sub_prod_le_card_mul
      count p hδ hempty hp hstep s
  exact
    sub_le_iff_le_add.mpr
      ((abs_le.mp habs).1 |>
        fun h => by linarith)

theorem pow_sub_card_mul_le_finiteCount
    {ι : Type*} [DecidableEq ι]
    (count : Finset ι → ℝ)
    (p : ι → ℝ)
    {α δ : ℝ} (hα : 0 ≤ α) (hδ : 0 ≤ δ)
    (hempty : count ∅ = 1)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hpLower : ∀ i, α ≤ p i)
    (hstep :
      ∀ s : Finset ι, s.Nonempty →
        ∃ e ∈ s,
          |count s - p e * count (s.erase e)| ≤ δ)
    (s : Finset ι) :
    α ^ s.card - (s.card : ℝ) * δ ≤ count s := by
  have hproduct :
      α ^ s.card ≤ ∏ e ∈ s, p e := by
    calc
      α ^ s.card =
          ∏ _e ∈ s, α := by simp
      _ ≤ ∏ e ∈ s, p e := by
        apply Finset.prod_le_prod₀
        · intro e he
          exact hα
        · intro e he
          exact hpLower e
  exact le_trans
    (sub_le_sub_right hproduct _)
    (finiteCount_prod_sub_card_mul_le
      count p hδ hempty hp hstep s)

theorem finiteCount_pos_of_card_mul_lt_pow
    {ι : Type*} [DecidableEq ι]
    (count : Finset ι → ℝ)
    (p : ι → ℝ)
    {α δ : ℝ} (hα : 0 ≤ α) (hδ : 0 ≤ δ)
    (hempty : count ∅ = 1)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hpLower : ∀ i, α ≤ p i)
    (hstep :
      ∀ s : Finset ι, s.Nonempty →
        ∃ e ∈ s,
          |count s - p e * count (s.erase e)| ≤ δ)
    (s : Finset ι)
    (hsmall : (s.card : ℝ) * δ < α ^ s.card) :
    0 < count s := by
  have hlower :=
    pow_sub_card_mul_le_finiteCount
      count p hα hδ hempty hp hpLower hstep s
  linarith

theorem abs_finiteCount_sub_prod_le_sum_error
    {ι : Type*} [DecidableEq ι]
    (count : Finset ι → ℝ)
    (p error : ι → ℝ)
    (herror : ∀ i, 0 ≤ error i)
    (hempty : count ∅ = 1)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hstep :
      ∀ s : Finset ι, s.Nonempty →
        ∃ e ∈ s,
          |count s - p e * count (s.erase e)| ≤ error e)
    (s : Finset ι) :
    |count s - ∏ e ∈ s, p e| ≤
      ∑ e ∈ s, error e := by
  refine Finset.strongInductionOn s ?_
  intro s ih
  by_cases hs : s = ∅
  · subst s
    simp [hempty]
  · have hsne : s.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hs
    obtain ⟨e, he, hrec⟩ := hstep s hsne
    have herase : s.erase e ⊂ s :=
      Finset.erase_ssubset he
    have hind :
        |count (s.erase e) -
            ∏ f ∈ s.erase e, p f| ≤
          ∑ f ∈ s.erase e, error f :=
      ih (s.erase e) herase
    have hpe0 : 0 ≤ p e := (hp e).1
    have hpe1 : p e ≤ 1 := (hp e).2
    have hsum0 :
        0 ≤ ∑ f ∈ s.erase e, error f :=
      Finset.sum_nonneg fun f _ => herror f
    have hprod :
        (∏ f ∈ s, p f) =
          p e * ∏ f ∈ s.erase e, p f := by
      exact
        (Finset.mul_prod_erase s p he).symm
    calc
      |count s - ∏ f ∈ s, p f| =
          |(count s - p e * count (s.erase e)) +
            p e *
              (count (s.erase e) -
                ∏ f ∈ s.erase e, p f)| := by
        rw [hprod]
        congr 1
        ring
      _ ≤
          |count s - p e * count (s.erase e)| +
            |p e *
              (count (s.erase e) -
                ∏ f ∈ s.erase e, p f)| :=
        abs_add_le _ _
      _ =
          |count s - p e * count (s.erase e)| +
            p e *
              |count (s.erase e) -
                ∏ f ∈ s.erase e, p f| := by
        rw [abs_mul, abs_of_nonneg hpe0]
      _ ≤
          error e +
            p e * (∑ f ∈ s.erase e, error f) := by
        exact add_le_add hrec
          (mul_le_mul_of_nonneg_left hind hpe0)
      _ ≤
          error e + ∑ f ∈ s.erase e, error f := by
        exact add_le_add le_rfl
          (mul_le_of_le_one_left hsum0 hpe1)
      _ = ∑ f ∈ s, error f := by
        rw [← Finset.sum_erase_add s error he]
        ring

theorem finiteCount_prod_sub_sum_error_le
    {ι : Type*} [DecidableEq ι]
    (count : Finset ι → ℝ)
    (p error : ι → ℝ)
    (herror : ∀ i, 0 ≤ error i)
    (hempty : count ∅ = 1)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hstep :
      ∀ s : Finset ι, s.Nonempty →
        ∃ e ∈ s,
          |count s - p e * count (s.erase e)| ≤ error e)
    (s : Finset ι) :
    (∏ e ∈ s, p e) - (∑ e ∈ s, error e) ≤
      count s := by
  have habs :=
    abs_finiteCount_sub_prod_le_sum_error
      count p error herror hempty hp hstep s
  exact
    sub_le_iff_le_add.mpr
      ((abs_le.mp habs).1 |>
        fun h => by linarith)

theorem finiteCount_pos_of_sum_error_lt_prod
    {ι : Type*} [DecidableEq ι]
    (count : Finset ι → ℝ)
    (p error : ι → ℝ)
    (herror : ∀ i, 0 ≤ error i)
    (hempty : count ∅ = 1)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hstep :
      ∀ s : Finset ι, s.Nonempty →
        ∃ e ∈ s,
          |count s - p e * count (s.erase e)| ≤ error e)
    (s : Finset ι)
    (hsmall :
      (∑ e ∈ s, error e) < ∏ e ∈ s, p e) :
    0 < count s := by
  have hlower :=
    finiteCount_prod_sub_sum_error_le
      count p error herror hempty hp hstep s
  linarith

end Erdos3.FixedDensity

end

end OAI
