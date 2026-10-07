-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import OAI.Combinatorics.Progressions.FixedDensity.HypergraphBundleFiltration
import OAI.Compat.BigOperators

namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

def BaseWeightsIdempotent
    (H : Finset (Finset J))
    (A : BaseEdgeWeight J G) : Prop :=
  ∀ e ∈ H, ∀ y, A e y * A e y = A e y

def finsetMembershipEquivOfEq
    {α : Type*} {s t : Finset α} (h : s = t) :
    {a : α // a ∈ s} ≃ {a : α // a ∈ t} :=
  Equiv.cast
    (congrArg (fun u : Finset α => {a : α // a ∈ u}) h)

@[simp]
theorem finsetMembershipEquivOfEq_symm_val
    {α : Type*} {s t : Finset α} (h : s = t)
    (a : {a : α // a ∈ t}) :
    ((finsetMembershipEquivOfEq h).symm a).1 = a.1 := by
  subst t
  rfl

theorem cast_finsetPi_apply
    {α G' : Type*} {s t : Finset α} (h : s = t)
    (f : {a : α // a ∈ s} → G')
    (a : {a : α // a ∈ t}) :
    cast
        (congrArg
          (fun u : Finset α =>
            ({a : α // a ∈ u} → G'))
          h)
        f a =
      f ((finsetMembershipEquivOfEq h).symm a) := by
  subst t
  rfl

@[simp]
theorem projectionEquiv_apply_val
    (B : HypergraphBundle J K H)
    {g : Finset K} (hg : g ∈ B.edges)
    (v : {v : K // v ∈ g}) :
    ((B.projectionEquiv hg) v).1 =
      B.projection v.1 := by
  rfl

theorem prod_comp_eq_prod_image_of_idempotent
    {α β M : Type*} [DecidableEq β]
    [CommMonoid M]
    (s : Finset α) (f : α → β) (w : β → M)
    (hw : ∀ b ∈ s.image f, w b * w b = w b) :
    (∏ a ∈ s, w (f a)) =
      ∏ b ∈ s.image f, w b := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      have hw' :
          ∀ b ∈ s.image f, w b * w b = w b := by
        intro b hb
        exact hw b (by
          rw [Finset.image_insert]
          exact Finset.mem_insert_of_mem hb)
      rw [Finset.prod_insert ha, ih hw',
        Finset.image_insert]
      by_cases hfa : f a ∈ s.image f
      · rw [Finset.insert_eq_of_mem hfa]
        calc
          w (f a) * ∏ b ∈ s.image f, w b =
              w (f a) *
                (w (f a) *
                  ∏ b ∈ (s.image f).erase (f a), w b) := by
            rw [Finset.mul_prod_erase (s.image f) w hfa]
          _ =
              w (f a) *
                ∏ b ∈ (s.image f).erase (f a), w b := by
            rw [← mul_assoc,
              hw (f a) (by
                rw [Finset.image_insert]
                exact Finset.mem_insert_self _ _)]
          _ = ∏ b ∈ s.image f, w b :=
            Finset.mul_prod_erase (s.image f) w hfa
      · rw [Finset.prod_insert hfa]

theorem doubledEdgeOfSource_eq_iff
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (s t : B.DoubledEdgeSource g₀) :
    B.doubledEdgeOfSource g₀ s =
        B.doubledEdgeOfSource g₀ t ↔
      s.2.1 = t.2.1 ∧
        (s.1 = t.1 ∨ s.2.1 ⊆ g₀) := by
  classical
  constructor
  · intro hst
    have hgg : s.2.1 = t.2.1 := by
      have himage :=
        congrArg
          (Finset.image (doubledVertexForget g₀))
          hst
      simpa [doubledEdgeOfSource] using himage
    refine ⟨hgg, ?_⟩
    by_cases hcopy : s.1 = t.1
    · exact Or.inl hcopy
    · right
      have hedges :
          doubledEdge g₀ s.1 s.2.1 =
            doubledEdge g₀ t.1 s.2.1 := by
        simpa [doubledEdgeOfSource, hgg] using hst
      cases hs : s.1 <;> cases ht : t.1
      · exact False.elim (hcopy (by simp [hs, ht]))
      · exact
          (doubledEdge_false_eq_true_iff_subset
            g₀ s.2.1).1 (by
              simpa [hs, ht] using hedges)
      · exact
          (doubledEdge_false_eq_true_iff_subset
            g₀ s.2.1).1 (by
              simpa [hs, ht] using hedges.symm)
      · exact False.elim (hcopy (by simp [hs, ht]))
  · rintro ⟨hgg, hcopy⟩
    rcases hcopy with hcopy | hsubset
    · simp [doubledEdgeOfSource, hgg, hcopy]
    · simpa [doubledEdgeOfSource, hgg] using
        doubledEdge_copy_independent_of_subset
          g₀ hsubset s.1 t.1

theorem pullbackBaseEdgeWeight_duplicateOutside_doubledEdge
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : BaseEdgeWeight J G)
    (copy : Bool) {g : Finset K}
    (hg : g ∈ B.edges.erase g₀)
    (x : DoubledOccurrenceVertex g₀ → G) :
    (B.duplicateOutside g₀).pullbackBaseEdgeWeight A
        (doubledEdge g₀ copy g)
        (edgeTuple (doubledEdge g₀ copy g) x) =
      B.pullbackBaseEdgeWeight A g
        (fun v => x (doubledVertexLift g₀ copy v.1)) := by
  classical
  have hgB : g ∈ B.edges :=
    Finset.mem_of_mem_erase hg
  have hd :
      doubledEdge g₀ copy g ∈
        (B.duplicateOutside g₀).edges := by
    exact
      (B.mem_doubledEdges_iff g₀
        (doubledEdge g₀ copy g)).2
        ⟨copy, g, hg, rfl⟩
  rw [(B.duplicateOutside g₀).pullbackBaseEdgeWeight_of_mem
      A hd,
    B.pullbackBaseEdgeWeight_of_mem A hgB]
  have himage :
      (doubledEdge g₀ copy g).image
          (B.duplicateOutside g₀).projection =
        g.image B.projection := by
    exact B.image_doubledProjection_doubledEdge g₀ copy g
  let lhsInput :
      (Σ e : Finset J,
        ({j : J // j ∈ e} → G)) :=
    ⟨(doubledEdge g₀ copy g).image
        (B.duplicateOutside g₀).projection,
      (B.duplicateOutside g₀).projectedEdgeTuple hd
        (edgeTuple (doubledEdge g₀ copy g) x)⟩
  let rhsInput :
      (Σ e : Finset J,
        ({j : J // j ∈ e} → G)) :=
    ⟨g.image B.projection,
      B.projectedEdgeTuple hgB
        (fun v =>
          x (doubledVertexLift g₀ copy v.1))⟩
  change
    (fun p :
        (Σ e : Finset J,
          ({j : J // j ∈ e} → G)) =>
      A p.1 p.2) lhsInput =
    (fun p :
        (Σ e : Finset J,
          ({j : J // j ∈ e} → G)) =>
      A p.1 p.2) rhsInput
  apply congrArg
    (fun p :
        (Σ e : Finset J,
          ({j : J // j ∈ e} → G)) =>
      A p.1 p.2)
  apply Sigma.ext himage
  apply heq_of_eqRec_eq
    (congrArg
      (fun e : Finset J =>
        ({j : J // j ∈ e} → G))
      himage)
  funext j
  change
    cast
        (congrArg
          (fun e : Finset J =>
            ({j : J // j ∈ e} → G))
          himage)
        lhsInput.2 j =
      rhsInput.2 j
  rw [cast_finsetPi_apply himage]
  let jleft :
      {j : J //
        j ∈ (doubledEdge g₀ copy g).image
          (B.duplicateOutside g₀).projection} :=
    (finsetMembershipEquivOfEq himage).symm j
  let v : {v : K // v ∈ g} :=
    (B.projectionEquiv hgB).symm j
  have hjv :
      (⟨B.projection v.1,
          Finset.mem_image.mpr ⟨v.1, v.2, rfl⟩⟩ :
        {j : J // j ∈ g.image B.projection}) = j := by
    exact
      (B.projectionEquiv hgB).apply_symm_apply j
  have hvlift :
      doubledVertexLift g₀ copy v.1 ∈
        doubledEdge g₀ copy g :=
    mem_doubledEdge g₀ copy g v.1 v.2
  have hpreimage :
      ((B.duplicateOutside g₀).projectionEquiv hd).symm jleft =
        ⟨doubledVertexLift g₀ copy v.1, hvlift⟩ := by
    apply ((B.duplicateOutside g₀).projectionEquiv hd).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    calc
      jleft.1 = j.1 := by
        exact
          finsetMembershipEquivOfEq_symm_val
            himage j
      _ = B.projection v.1 :=
        congrArg Subtype.val hjv.symm
      _ =
          (((B.duplicateOutside g₀).projectionEquiv hd)
            ⟨doubledVertexLift g₀ copy v.1,
              hvlift⟩).1 := by
        rw [projectionEquiv_apply_val,
          duplicateOutside_projection,
          doubledProjection_lift]
  unfold lhsInput rhsInput projectedEdgeTuple edgeTuple
  change
    x (((B.duplicateOutside g₀).projectionEquiv hd).symm
        jleft).1 =
      x (doubledVertexLift g₀ copy v.1)
  rw [hpreimage]

noncomputable def doubledBundleEdgeFactor
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : BaseEdgeWeight J G)
    (x : DoubledOccurrenceVertex g₀ → G)
    (d : Finset (DoubledOccurrenceVertex g₀)) : ℝ :=
  (B.duplicateOutside g₀).pullbackBaseEdgeWeight A d
    (edgeTuple d x)

theorem doubledBundleEdgeFactor_doubledEdgeOfSource
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : BaseEdgeWeight J G)
    (x : DoubledOccurrenceVertex g₀ → G)
    (s : B.DoubledEdgeSource g₀) :
    B.doubledBundleEdgeFactor g₀ A x
        (B.doubledEdgeOfSource g₀ s) =
      B.pullbackBaseEdgeWeight A s.2.1
        (fun v =>
          x (doubledVertexLift g₀ s.1 v.1)) := by
  exact
    B.pullbackBaseEdgeWeight_duplicateOutside_doubledEdge
      g₀ A s.1 s.2.2 x

theorem doubledBundleEdgeFactor_idempotent
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsIdempotent H A)
    (x : DoubledOccurrenceVertex g₀ → G)
    (d : Finset (DoubledOccurrenceVertex g₀))
    (hd : d ∈ B.doubledEdges g₀) :
    B.doubledBundleEdgeFactor g₀ A x d *
        B.doubledBundleEdgeFactor g₀ A x d =
      B.doubledBundleEdgeFactor g₀ A x d := by
  classical
  unfold doubledBundleEdgeFactor
  rw [(B.duplicateOutside g₀).pullbackBaseEdgeWeight_of_mem
      A hd]
  exact hA _ ((B.duplicateOutside g₀).projection_mem_base d hd) _

theorem doubledSourceProduct_pullback_eq_duplicateOutside_bundleProduct
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsIdempotent H A)
    (x : DoubledOccurrenceVertex g₀ → G) :
    B.doubledSourceProduct g₀
        (B.pullbackBaseEdgeWeight A) x =
      (B.duplicateOutside g₀).bundleProduct
        ((B.duplicateOutside g₀).pullbackBaseEdgeWeight A) x := by
  classical
  unfold doubledSourceProduct
  calc
    (∏ s : B.DoubledEdgeSource g₀,
        B.pullbackBaseEdgeWeight A s.2.1
          (fun v =>
            x (doubledVertexLift g₀ s.1 v.1))) =
        ∏ s : B.DoubledEdgeSource g₀,
          B.doubledBundleEdgeFactor g₀ A x
            (B.doubledEdgeOfSource g₀ s) := by
      apply Finset.prod_congr rfl
      intro s _hs
      exact
        (B.doubledBundleEdgeFactor_doubledEdgeOfSource
          g₀ A x s).symm
    _ =
        ∏ d ∈
            (Finset.univ :
              Finset (B.DoubledEdgeSource g₀)).image
                (B.doubledEdgeOfSource g₀),
          B.doubledBundleEdgeFactor g₀ A x d := by
      apply prod_comp_eq_prod_image_of_idempotent
      intro d hd
      apply B.doubledBundleEdgeFactor_idempotent
        g₀ A hA x d
      simpa [doubledEdges] using hd
    _ =
        (B.duplicateOutside g₀).bundleProduct
          ((B.duplicateOutside g₀).pullbackBaseEdgeWeight A) x := by
      rfl

theorem doubledRemainderMoment_pullback_eq_duplicateOutside_bundleCount
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsIdempotent H A) :
    B.doubledRemainderMoment g₀
        (B.pullbackBaseEdgeWeight A) =
      (B.duplicateOutside g₀).bundleCount
        ((B.duplicateOutside g₀).pullbackBaseEdgeWeight A) := by
  have _hduplicateClosed :
      (B.duplicateOutside g₀).IsClosedUnderInclusion :=
    B.duplicateOutside_closed_of_maximal
      hclosed hg₀ hmax
  rw [B.doubledRemainderMoment_eq_mean_doubledSourceProduct]
  unfold bundleCount
  apply congrArg mean
  funext x
  exact
    B.doubledSourceProduct_pullback_eq_duplicateOutside_bundleProduct
      g₀ A hA x

end HypergraphBundle

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

def restrictEdgeTuple
    {f g : Finset K} (hfg : f ⊆ g)
    (y : {v : K // v ∈ g} → G) :
    {v : K // v ∈ f} → G :=
  fun v => y ⟨v.1, hfg v.2⟩

omit [DecidableEq K] in
@[simp]
theorem restrictEdgeTuple_edgeTuple
    {f g : Finset K} (hfg : f ⊆ g)
    (x : K → G) :
    restrictEdgeTuple hfg (edgeTuple g x) =
      edgeTuple f x := by
  rfl

noncomputable def strictBoundaryLocalProduct
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (y : {v : K // v ∈ g₀} → G) : ℝ :=
  ∏ g :
      {g : Finset K //
        g ∈ (B.strictBoundary g₀).edges},
    A g.1
      (restrictEdgeTuple
        (((B.mem_strictBoundary_edges g₀ g.1).1
          g.2).2.1)
        y)

theorem strictBoundaryLocalProduct_edgeTuple
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (x : K → G) :
    B.strictBoundaryLocalProduct g₀ A
        (edgeTuple g₀ x) =
      (B.strictBoundary g₀).bundleProduct A x := by
  classical
  unfold strictBoundaryLocalProduct
  calc
    (∏ g :
        {g : Finset K //
          g ∈ (B.strictBoundary g₀).edges},
      A g.1
        (restrictEdgeTuple
          (((B.mem_strictBoundary_edges g₀ g.1).1
            g.2).2.1)
          (edgeTuple g₀ x))) =
        ∏ g :
          {g : Finset K //
            g ∈ (B.strictBoundary g₀).edges},
          A g.1 (edgeTuple g.1 x) := by
      apply Finset.prod_congr rfl
      intro g _hg
      apply congrArg (A g.1)
      exact restrictEdgeTuple_edgeTuple _ x
    _ =
        ∏ g ∈ (B.strictBoundary g₀).edges,
          A g (edgeTuple g x) :=
      Finset.prod_coe_sort
        (B.strictBoundary g₀).edges
        (fun g => A g (edgeTuple g x))
    _ = (B.strictBoundary g₀).bundleProduct A x := by
      rfl

theorem strictBoundary_edges_subset_erase
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.strictBoundary g₀).edges ⊆
      B.edges.erase g₀ := by
  intro g hg
  have hg' :=
    (B.mem_strictBoundary_edges g₀ g).1 hg
  exact Finset.mem_erase.mpr
    ⟨hg'.2.ne, hg'.1⟩

def WeightsIdempotent
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) : Prop :=
  ∀ g ∈ B.edges, ∀ y,
    A g y * A g y = A g y

theorem pullbackBaseEdgeWeight_weightsIdempotent
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsIdempotent H A) :
    B.WeightsIdempotent
      (B.pullbackBaseEdgeWeight A) := by
  intro g hg y
  rw [B.pullbackBaseEdgeWeight_of_mem A hg y]
  exact hA _ (B.projection_mem_base g hg) _

theorem prod_mul_prod_eq_right_of_subset_of_idempotent
    {ι : Type*}
    (s t : Finset ι) (f : ι → ℝ)
    (hst : s ⊆ t)
    (hf : ∀ i ∈ s, f i * f i = f i) :
    (∏ i ∈ s, f i) * (∏ i ∈ t, f i) =
      ∏ i ∈ t, f i := by
  classical
  induction s using Finset.induction_on generalizing t with
  | empty =>
      simp
  | @insert a s ha ih =>
      have hat : a ∈ t :=
        hst (Finset.mem_insert_self a s)
      have hst' : s ⊆ t.erase a := by
        intro i hi
        exact Finset.mem_erase.mpr
          ⟨fun hia => ha (hia ▸ hi),
            hst (Finset.mem_insert_of_mem hi)⟩
      have hf' :
          ∀ i ∈ s, f i * f i = f i := by
        intro i hi
        exact hf i (Finset.mem_insert_of_mem hi)
      rw [Finset.prod_insert ha]
      rw [← Finset.mul_prod_erase t f hat]
      calc
        (f a * ∏ i ∈ s, f i) *
              (f a * ∏ i ∈ t.erase a, f i) =
            (f a * f a) *
              ((∏ i ∈ s, f i) *
                ∏ i ∈ t.erase a, f i) := by
          ring
        _ =
            f a *
              ((∏ i ∈ s, f i) *
                ∏ i ∈ t.erase a, f i) := by
          rw [hf a (Finset.mem_insert_self a s)]
        _ = f a * ∏ i ∈ t.erase a, f i := by
          rw [ih (t.erase a) hst' hf']

theorem strictBoundaryLocalProduct_mul_edgeRemainder
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (hA : B.WeightsIdempotent A)
    (x : K → G) :
    B.strictBoundaryLocalProduct g₀ A
          (edgeTuple g₀ x) *
        B.edgeRemainder g₀ A x =
      B.edgeRemainder g₀ A x := by
  rw [B.strictBoundaryLocalProduct_edgeTuple]
  unfold edgeRemainder bundleProduct
  apply prod_mul_prod_eq_right_of_subset_of_idempotent
    (B.strictBoundary g₀).edges
    (B.edges.erase g₀)
    (fun g => A g (edgeTuple g x))
    (B.strictBoundary_edges_subset_erase g₀)
  intro g hg
  exact hA g
    (Finset.mem_of_mem_erase
      (B.strictBoundary_edges_subset_erase g₀ hg))
    (edgeTuple g x)

theorem edgeContribution_mul_strictBoundaryLocalProduct
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (hA : B.WeightsIdempotent A) :
    B.edgeContribution g₀ q A =
      B.edgeContribution g₀
        (fun y =>
          q y *
            B.strictBoundaryLocalProduct g₀ A y)
        A := by
  unfold edgeContribution
  apply congrArg mean
  funext x
  rw [mul_assoc,
    B.strictBoundaryLocalProduct_mul_edgeRemainder
      g₀ A hA x]

noncomputable def lowerExteriorMainProduct
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (p : Finset J → ℝ) : ℝ :=
  ∏ g ∈ B.edges.filter
      (fun g =>
        g.card < g₀.card ∧ ¬ g ⊆ g₀),
    p (g.image B.projection)

noncomputable def maximalRemainderMainProduct
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (p : Finset J → ℝ) : ℝ :=
  ∏ g ∈ (B.edges.erase g₀).filter
      (fun g => ¬ g.card < g₀.card),
    p (g.image B.projection)

theorem card_image_projection
    (B : HypergraphBundle J K H)
    {g : Finset K} (hg : g ∈ B.edges) :
    (g.image B.projection).card = g.card := by
  have hcard :=
    Fintype.card_congr (B.projectionEquiv hg)
  simpa using hcard.symm

theorem pow_card_edges_le_bundleMainProduct
    (B : HypergraphBundle J K H)
    (p : Finset J → ℝ) {a : ℝ}
    (ha : 0 ≤ a)
    (hp : ∀ e ∈ H, a ≤ p e) :
    a ^ B.edges.card ≤ B.bundleMainProduct p := by
  classical
  unfold bundleMainProduct
  calc
    a ^ B.edges.card =
        ∏ _g ∈ B.edges, a := by
      simp
    _ ≤
        ∏ g ∈ B.edges,
          p (g.image B.projection) := by
      apply Finset.prod_le_prod₀
      · intro g hg
        exact ha
      · intro g hg
        exact hp _ (B.projection_mem_base g hg)

theorem bundleMainProduct_nonneg
    (B : HypergraphBundle J K H)
    (p : Finset J → ℝ)
    (hp : ∀ e ∈ H, 0 ≤ p e) :
    0 ≤ B.bundleMainProduct p := by
  unfold bundleMainProduct
  exact Finset.prod_nonneg fun g hg =>
    hp _ (B.projection_mem_base g hg)

theorem bundleMainProduct_lowerOrder_eq_boundary_mul_exterior
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (p : Finset J → ℝ) :
    (B.lowerOrder g₀.card).bundleMainProduct p =
      (B.strictBoundary g₀).bundleMainProduct p *
        B.lowerExteriorMainProduct g₀ p := by
  classical
  let s :=
    B.edges.filter
      (fun g => g.card < g₀.card)
  have hboundary :
      s.filter (fun g => g ⊆ g₀) =
        B.edges.filter (fun g => g ⊂ g₀) := by
    ext g
    simp only [s, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hgB, hgcard⟩, hgsub⟩
      exact ⟨hgB,
        Finset.ssubset_iff_subset_ne.mpr
          ⟨hgsub, fun hgeq => by
            subst g
            exact (Nat.lt_irrefl _ hgcard)⟩⟩
    · rintro ⟨hgB, hgstrict⟩
      exact ⟨⟨hgB, Finset.card_lt_card hgstrict⟩,
        hgstrict.1⟩
  have hexterior :
      s.filter (fun g => ¬ g ⊆ g₀) =
        B.edges.filter
          (fun g =>
            g.card < g₀.card ∧ ¬ g ⊆ g₀) := by
    ext g
    simp only [s, Finset.mem_filter]
    tauto
  have hsplit :=
    Finset.prod_filter_mul_prod_filter_not
      s (fun g => g ⊆ g₀)
        (fun g => p (g.image B.projection))
  unfold bundleMainProduct lowerExteriorMainProduct
  simp only [lowerOrder_edges, strictBoundary_edges]
  rw [← hboundary, ← hexterior]
  exact hsplit.symm

theorem boundary_mul_duplicateLower_main_eq_lowerOrder_sq
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (p : Finset J → ℝ) :
    (B.strictBoundary g₀).bundleMainProduct p *
        ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleMainProduct p =
      ((B.lowerOrder g₀.card).bundleMainProduct p) ^ 2 := by
  rw [B.bundleMainProduct_duplicateOutside_lowerOrder
    g₀ p]
  rw [Finset.prod_pow]
  rw [B.bundleMainProduct_lowerOrder_eq_boundary_mul_exterior
    g₀ p]
  unfold lowerExteriorMainProduct
  ring

theorem lowerOrder_mul_maximalRemainder_eq_erase_main
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (p : Finset J → ℝ) :
    (B.lowerOrder g₀.card).bundleMainProduct p *
        B.maximalRemainderMainProduct g₀ p =
      (B.eraseEdge g₀).bundleMainProduct p := by
  classical
  have hlower :
      (B.edges.erase g₀).filter
          (fun g => g.card < g₀.card) =
        B.edges.filter
          (fun g => g.card < g₀.card) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨_hne, hgB⟩, hgcard⟩
      exact ⟨hgB, hgcard⟩
    · rintro ⟨hgB, hgcard⟩
      exact ⟨⟨fun hgg₀ => by
        subst g
        exact Nat.lt_irrefl _ hgcard, hgB⟩,
        hgcard⟩
  have hsplit :=
    Finset.prod_filter_mul_prod_filter_not
      (B.edges.erase g₀)
      (fun g => g.card < g₀.card)
      (fun g => p (g.image B.projection))
  unfold bundleMainProduct maximalRemainderMainProduct
  simp only [lowerOrder_edges, eraseEdge_edges]
  rw [← hlower]
  exact hsplit

theorem card_eq_selected_of_mem_maximalRemainder
    (B : HypergraphBundle J K H)
    {g₀ g : Finset K}
    (hmax : ∀ f ∈ B.edges, f.card ≤ g₀.card)
    (hg :
      g ∈ (B.edges.erase g₀).filter
        (fun f => ¬ f.card < g₀.card)) :
    g.card = g₀.card := by
  have hg' := Finset.mem_filter.mp hg
  exact Nat.le_antisymm
    (hmax g (Finset.mem_of_mem_erase hg'.1))
    (Nat.le_of_not_gt hg'.2)

theorem card_maximalRemainder_le_erase
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    ((B.edges.erase g₀).filter
      (fun g => ¬ g.card < g₀.card)).card ≤
        (B.edges.erase g₀).card :=
  Finset.card_le_card (Finset.filter_subset _ _)

theorem pow_card_maximalRemainder_le
    (B : HypergraphBundle J K H)
    {g₀ : Finset K}
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (p : Finset J → ℝ) {a : ℝ}
    (ha : 0 ≤ a)
    (hp :
      ∀ e ∈ H, e.card = g₀.card →
        a ≤ p e) :
    a ^
          ((B.edges.erase g₀).filter
            (fun g => ¬ g.card < g₀.card)).card ≤
      B.maximalRemainderMainProduct g₀ p := by
  classical
  unfold maximalRemainderMainProduct
  calc
    a ^
          ((B.edges.erase g₀).filter
            (fun g => ¬ g.card < g₀.card)).card =
        ∏ _g ∈
            (B.edges.erase g₀).filter
              (fun g => ¬ g.card < g₀.card),
          a := by
      simp
    _ ≤
        ∏ g ∈
            (B.edges.erase g₀).filter
              (fun g => ¬ g.card < g₀.card),
          p (g.image B.projection) := by
      apply Finset.prod_le_prod₀
      · intro g hg
        exact ha
      · intro g hg
        apply hp _ (B.projection_mem_base g
          (Finset.mem_of_mem_erase
            (Finset.mem_filter.mp hg).1))
        rw [B.card_image_projection
          (Finset.mem_of_mem_erase
            (Finset.mem_filter.mp hg).1)]
        exact B.card_eq_selected_of_mem_maximalRemainder
          hmax hg

theorem pullbackBaseEdgeWeight_eq_of_projection_eq
    (B C : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G)
    (hprojection : B.projection = C.projection)
    {g : Finset K}
    (hgB : g ∈ B.edges) (hgC : g ∈ C.edges)
    (y : {v : K // v ∈ g} → G) :
    B.pullbackBaseEdgeWeight A g y =
      C.pullbackBaseEdgeWeight A g y := by
  classical
  rw [B.pullbackBaseEdgeWeight_of_mem A hgB y,
    C.pullbackBaseEdgeWeight_of_mem A hgC y]
  have himage :
      g.image B.projection = g.image C.projection :=
    congrArg (fun q : K → J => g.image q) hprojection
  let lhsInput :
      (Σ e : Finset J,
        ({j : J // j ∈ e} → G)) :=
    ⟨g.image B.projection,
      B.projectedEdgeTuple hgB y⟩
  let rhsInput :
      (Σ e : Finset J,
        ({j : J // j ∈ e} → G)) :=
    ⟨g.image C.projection,
      C.projectedEdgeTuple hgC y⟩
  change
    (fun p :
        (Σ e : Finset J,
          ({j : J // j ∈ e} → G)) =>
      A p.1 p.2) lhsInput =
    (fun p :
        (Σ e : Finset J,
          ({j : J // j ∈ e} → G)) =>
      A p.1 p.2) rhsInput
  apply congrArg
    (fun p :
        (Σ e : Finset J,
          ({j : J // j ∈ e} → G)) =>
      A p.1 p.2)
  apply Sigma.ext himage
  apply heq_of_eqRec_eq
    (congrArg
      (fun e : Finset J =>
        ({j : J // j ∈ e} → G))
      himage)
  funext j
  change
    cast
        (congrArg
          (fun e : Finset J =>
            ({j : J // j ∈ e} → G))
          himage)
        lhsInput.2 j =
      rhsInput.2 j
  rw [cast_finsetPi_apply himage]
  let jB :
      {j : J // j ∈ g.image B.projection} :=
    (finsetMembershipEquivOfEq himage).symm j
  let vB := (B.projectionEquiv hgB).symm jB
  let vC := (C.projectionEquiv hgC).symm j
  have hjB : jB.1 = j.1 :=
    finsetMembershipEquivOfEq_symm_val himage j
  have hvB :
      B.projection vB.1 = jB.1 := by
    exact congrArg Subtype.val
      ((B.projectionEquiv hgB).apply_symm_apply jB)
  have hvC' :
      C.projection vC.1 = j.1 := by
    exact congrArg Subtype.val
      ((C.projectionEquiv hgC).apply_symm_apply j)
  have hvC :
      B.projection vC.1 = j.1 := by
    rw [hprojection]
    exact hvC'
  have hval : vB.1 = vC.1 :=
    B.projection_injective_on_edge g hgB
      vB.2 vC.2
      ((hvB.trans hjB).trans hvC.symm)
  unfold lhsInput rhsInput projectedEdgeTuple
  change y vB = y vC
  exact congrArg y (Subtype.ext hval)

theorem doubledEdges_lowerOrder_subset
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.lowerOrder g₀.card).doubledEdges g₀ ⊆
      B.doubledEdges g₀ := by
  intro d hd
  obtain ⟨copy, g, hg, hgd⟩ :=
    ((B.lowerOrder g₀.card).mem_doubledEdges_iff
      g₀ d).1 hd
  apply (B.mem_doubledEdges_iff g₀ d).2
  refine ⟨copy, g, ?_, hgd⟩
  have hgLower :
      g ∈ (B.lowerOrder g₀.card).edges :=
    Finset.mem_of_mem_erase hg
  exact Finset.mem_erase.mpr
    ⟨(Finset.mem_erase.mp hg).1,
      ((B.mem_lowerOrder_edges g₀.card g).1
        hgLower).1⟩

theorem duplicateOutside_bundleProduct_le_lowerOrder
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsInUnitInterval H A)
    (x : DoubledOccurrenceVertex g₀ → G) :
    (B.duplicateOutside g₀).bundleProduct
          ((B.duplicateOutside g₀).pullbackBaseEdgeWeight A) x ≤
      ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleProduct
          (((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight A) x := by
  classical
  let C := B.duplicateOutside g₀
  let D := (B.lowerOrder g₀.card).duplicateOutside g₀
  have hDC : D.edges ⊆ C.edges := by
    simpa [C, D] using
      B.doubledEdges_lowerOrder_subset g₀
  have hprojection : C.projection = D.projection := by
    rfl
  unfold bundleProduct
  calc
    (∏ d ∈ C.edges,
        C.pullbackBaseEdgeWeight A
          d (edgeTuple d x)) ≤
        ∏ d ∈ D.edges,
          C.pullbackBaseEdgeWeight A
            d (edgeTuple d x) := by
      apply Finset.prod_le_prod_of_subset_of_le_one₀
        hDC
      · intro d hd
        exact
          (C.pullbackBaseEdgeWeight_unitInterval
            A hA hd (edgeTuple d x)).1
      · intro d hd _hdD
        exact
          (C.pullbackBaseEdgeWeight_unitInterval
            A hA hd (edgeTuple d x)).2
    _ =
        ∏ d ∈ D.edges,
          D.pullbackBaseEdgeWeight A
            d (edgeTuple d x) := by
      apply Finset.prod_congr rfl
      intro d hd
      exact C.pullbackBaseEdgeWeight_eq_of_projection_eq
        D A hprojection (hDC hd) hd (edgeTuple d x)

theorem doubledRemainderMoment_pullback_le_lowerOrder
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (A : BaseEdgeWeight J G)
    (hA01 : BaseWeightsInUnitInterval H A)
    (hAidempotent : BaseWeightsIdempotent H A) :
    B.doubledRemainderMoment g₀
          (B.pullbackBaseEdgeWeight A) ≤
      ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount
          (((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight A) := by
  rw [B.doubledRemainderMoment_pullback_eq_duplicateOutside_bundleCount
    hclosed hg₀ hmax A hAidempotent]
  unfold bundleCount
  apply mean_mono
  intro x
  exact B.duplicateOutside_bundleProduct_le_lowerOrder
    g₀ A hA01 x

theorem abs_edgeContribution_pullback_le_sqrt_boundary_mul_lowerOrder
    [Fintype K] [Fintype G] [Nonempty G]
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (A : BaseEdgeWeight J G)
    (hA01 : BaseWeightsInUnitInterval H A)
    (hAidempotent : BaseWeightsIdempotent H A)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    {β : ℝ} (hβ : 0 ≤ β)
    (hlocalized :
      mean (fun y => q y ^ 2) ≤
        β *
          (B.strictBoundary g₀).bundleCount
            ((B.strictBoundary g₀).pullbackBaseEdgeWeight A)) :
    |B.edgeContribution g₀ q
        (B.pullbackBaseEdgeWeight A)| ≤
      Real.sqrt
        ((β *
            (B.strictBoundary g₀).bundleCount
              ((B.strictBoundary g₀).pullbackBaseEdgeWeight A)) *
          ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount
              (((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight A)) := by
  let boundaryCount :=
    (B.strictBoundary g₀).bundleCount
      ((B.strictBoundary g₀).pullbackBaseEdgeWeight A)
  let lowerDoubledCount :=
    ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount
        (((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight A)
  have hboundary0 : 0 ≤ boundaryCount := by
    apply (B.strictBoundary g₀).bundleCount_nonneg
    exact
      (B.strictBoundary g₀).pullbackBaseEdgeWeight_weightsInUnitInterval
          A hA01
  have hlower0 : 0 ≤ lowerDoubledCount := by
    apply
      ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount_nonneg
    exact
      ((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight_weightsInUnitInterval
          A hA01
  have hmoment0 :
      0 ≤ B.doubledRemainderMoment g₀
        (B.pullbackBaseEdgeWeight A) :=
    B.doubledRemainderMoment_nonneg g₀
      (B.pullbackBaseEdgeWeight A)
  have hmoment :
      B.doubledRemainderMoment g₀
          (B.pullbackBaseEdgeWeight A) ≤
        lowerDoubledCount :=
    B.doubledRemainderMoment_pullback_le_lowerOrder
      hclosed hg₀ hmax A hA01 hAidempotent
  have hsq :
      B.edgeContribution g₀ q
          (B.pullbackBaseEdgeWeight A) ^ 2 ≤
        (β * boundaryCount) * lowerDoubledCount := by
    calc
      B.edgeContribution g₀ q
            (B.pullbackBaseEdgeWeight A) ^ 2 ≤
          mean (fun y => q y ^ 2) *
            B.doubledRemainderMoment g₀
              (B.pullbackBaseEdgeWeight A) :=
        B.edgeContribution_sq_le_localSquare_mul_doubled
          g₀ q (B.pullbackBaseEdgeWeight A)
      _ ≤
          (β * boundaryCount) *
            B.doubledRemainderMoment g₀
              (B.pullbackBaseEdgeWeight A) :=
        mul_le_mul_of_nonneg_right hlocalized hmoment0
      _ ≤ (β * boundaryCount) * lowerDoubledCount :=
        mul_le_mul_of_nonneg_left hmoment
          (mul_nonneg hβ hboundary0)
  have hradicand :
      0 ≤ (β * boundaryCount) * lowerDoubledCount :=
    mul_nonneg (mul_nonneg hβ hboundary0) hlower0
  apply
    (sq_le_sq₀
      (abs_nonneg
        (B.edgeContribution g₀ q
          (B.pullbackBaseEdgeWeight A)))
      (Real.sqrt_nonneg _)).mp
  rw [sq_abs, Real.sq_sqrt hradicand]
  exact hsq

end HypergraphBundle

structure IsBundleCountingEnvelope
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ) : Prop where
  density_pos : ∀ d, 0 < α d
  density_le_one : ∀ d, α d ≤ 1
  defect_nonneg : ∀ d, 0 ≤ β d
  uniform_nonneg : 0 ≤ τ
  floor_pos : ∀ d, 0 < μ d
  rankFloor :
    ∀ ⦃i d : ℕ⦄, i ≤ d → μ d ≤ α i
  error_nonneg :
    ∀ d n, 0 ≤ E d n
  error_mono_order :
    ∀ ⦃d d' n : ℕ⦄, d ≤ d' →
      E d n ≤ E d' n
  error_mono_card :
    ∀ ⦃d n n' : ℕ⦄, n ≤ n' →
      E d n ≤ E d n'
  step :
    ∀ d n,
      E (d + 1) n +
            Real.sqrt
                (β (d + 1) *
                  (1 + E d (n + 1)) *
                  (1 + E d (2 * (n + 1)))) /
              (α (d + 1)) ^ (n + 1) +
          τ / (μ (d + 1)) ^ (n + 1) ≤
        E (d + 1) (n + 1)

noncomputable def bundleCountingStepIncrement
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ)
    (d n : ℕ) : ℝ :=
  Real.sqrt
        (β (d + 1) *
          (1 + E d (n + 1)) *
          (1 + E d (2 * (n + 1)))) /
      (α (d + 1)) ^ (n + 1) +
    τ / (μ (d + 1)) ^ (n + 1)

theorem IsBundleCountingEnvelope.add_stepIncrement_le
    {α β μ : ℕ → ℝ} {τ : ℝ}
    {E : ℕ → ℕ → ℝ}
    (hE : IsBundleCountingEnvelope α β μ τ E)
    (d n : ℕ) :
    E (d + 1) n +
        bundleCountingStepIncrement α β μ τ E d n ≤
      E (d + 1) (n + 1) := by
  simpa [bundleCountingStepIncrement, add_assoc] using hE.step d n

theorem IsBundleCountingEnvelope.lower_correction_nonneg
    {α β μ : ℕ → ℝ} {τ : ℝ}
    {E : ℕ → ℕ → ℝ}
    (hE : IsBundleCountingEnvelope α β μ τ E)
    (d n : ℕ) :
    0 ≤
      (1 + E d (n + 1)) *
        (1 + E d (2 * (n + 1))) := by
  exact mul_nonneg
    (by linarith [hE.error_nonneg d (n + 1)])
    (by linarith [hE.error_nonneg d (2 * (n + 1))])

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open Filter Topology

noncomputable def bundleCommonStepIncrement
    (a t : ℝ) (lower : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.sqrt
        (t ^ 2 *
          (1 + lower (n + 1)) *
          (1 + lower (2 * (n + 1)))) /
      a ^ (n + 1) +
    t ^ 2 / a ^ (n + 1)

noncomputable def bundleCommonNextRow
    (a t : ℝ) (lower : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      bundleCommonNextRow a t lower n +
        bundleCommonStepIncrement a t lower n

noncomputable def bundleCommonEnvelopeError
    (a t : ℝ) : ℕ → ℕ → ℝ
  | 0 => fun _ => 0
  | d + 1 =>
      bundleCommonNextRow a t
        (bundleCommonEnvelopeError a t d)

@[simp]
theorem bundleCommonNextRow_zero
    (a t : ℝ) (lower : ℕ → ℝ) :
    bundleCommonNextRow a t lower 0 = 0 :=
  rfl

@[simp]
theorem bundleCommonNextRow_succ
    (a t : ℝ) (lower : ℕ → ℝ) (n : ℕ) :
    bundleCommonNextRow a t lower (n + 1) =
      bundleCommonNextRow a t lower n +
        bundleCommonStepIncrement a t lower n :=
  rfl

@[simp]
theorem bundleCommonEnvelopeError_zero_order
    (a t : ℝ) (n : ℕ) :
    bundleCommonEnvelopeError a t 0 n = 0 :=
  rfl

@[simp]
theorem bundleCommonEnvelopeError_succ_order
    (a t : ℝ) (d n : ℕ) :
    bundleCommonEnvelopeError a t (d + 1) n =
      bundleCommonNextRow a t
        (bundleCommonEnvelopeError a t d) n :=
  rfl

theorem bundleCommonNextRow_nonneg
    {a t : ℝ} (ha : 0 ≤ a)
    (lower : ℕ → ℝ) :
    ∀ n, 0 ≤ bundleCommonNextRow a t lower n := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ihn =>
      rw [bundleCommonNextRow_succ]
      apply add_nonneg ihn
      unfold bundleCommonStepIncrement
      exact add_nonneg
        (div_nonneg (Real.sqrt_nonneg _)
          (pow_nonneg ha _))
        (div_nonneg (sq_nonneg t)
          (pow_nonneg ha _))

theorem bundleCommonEnvelopeError_nonneg
    {a t : ℝ} (ha : 0 ≤ a) :
    ∀ d n, 0 ≤ bundleCommonEnvelopeError a t d n := by
  intro d
  induction d with
  | zero =>
      intro n
      simp
  | succ d _ih =>
      intro n
      rw [bundleCommonEnvelopeError_succ_order]
      exact bundleCommonNextRow_nonneg ha _ n

theorem bundleCommonStepIncrement_mono
    {a t : ℝ} (ha : 0 ≤ a)
    {lower₁ lower₂ : ℕ → ℝ}
    (hlower₁ : ∀ n, 0 ≤ lower₁ n)
    (hlower : ∀ n, lower₁ n ≤ lower₂ n)
    (n : ℕ) :
    bundleCommonStepIncrement a t lower₁ n ≤
      bundleCommonStepIncrement a t lower₂ n := by
  have h₁nonneg :
      0 ≤ 1 + lower₁ (n + 1) := by
    linarith [hlower₁ (n + 1)]
  have h₂nonneg :
      0 ≤ 1 + lower₁ (2 * (n + 1)) := by
    linarith [hlower₁ (2 * (n + 1))]
  have hright₁nonneg :
      0 ≤ 1 + lower₂ (n + 1) := by
    linarith [hlower₁ (n + 1), hlower (n + 1)]
  have hproduct :
      (1 + lower₁ (n + 1)) *
          (1 + lower₁ (2 * (n + 1))) ≤
        (1 + lower₂ (n + 1)) *
          (1 + lower₂ (2 * (n + 1))) := by
    exact mul_le_mul
      (by linarith [hlower (n + 1)])
      (by linarith [hlower (2 * (n + 1))])
      h₂nonneg hright₁nonneg
  have hradicand :
      t ^ 2 *
          (1 + lower₁ (n + 1)) *
          (1 + lower₁ (2 * (n + 1))) ≤
        t ^ 2 *
          (1 + lower₂ (n + 1)) *
          (1 + lower₂ (2 * (n + 1))) := by
    simpa [mul_assoc] using
      mul_le_mul_of_nonneg_left hproduct (sq_nonneg t)
  unfold bundleCommonStepIncrement
  apply add_le_add
  · exact div_le_div_of_nonneg_right
      (Real.sqrt_le_sqrt hradicand)
      (pow_nonneg ha _)
  · exact le_rfl

theorem bundleCommonNextRow_mono
    {a t : ℝ} (ha : 0 ≤ a)
    {lower₁ lower₂ : ℕ → ℝ}
    (hlower₁ : ∀ n, 0 ≤ lower₁ n)
    (hlower : ∀ n, lower₁ n ≤ lower₂ n) :
    ∀ n,
      bundleCommonNextRow a t lower₁ n ≤
        bundleCommonNextRow a t lower₂ n := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ihn =>
      rw [bundleCommonNextRow_succ,
        bundleCommonNextRow_succ]
      exact add_le_add ihn
        (bundleCommonStepIncrement_mono
          ha hlower₁ hlower n)

theorem bundleCommonEnvelopeError_monotone_card
    {a t : ℝ} (ha : 0 ≤ a) (d : ℕ) :
    Monotone (bundleCommonEnvelopeError a t d) := by
  apply monotone_nat_of_le_succ
  intro n
  cases d with
  | zero =>
      simp
  | succ d =>
      rw [bundleCommonEnvelopeError_succ_order,
        bundleCommonEnvelopeError_succ_order,
        bundleCommonNextRow_succ]
      exact le_add_of_nonneg_right
        (by
          unfold bundleCommonStepIncrement
          exact add_nonneg
            (div_nonneg (Real.sqrt_nonneg _)
              (pow_nonneg ha _))
            (div_nonneg (sq_nonneg t)
              (pow_nonneg ha _)))

theorem bundleCommonEnvelopeError_monotone_order
    {a t : ℝ} (ha : 0 ≤ a) :
    ∀ n, Monotone (fun d =>
      bundleCommonEnvelopeError a t d n) := by
  intro n
  apply monotone_nat_of_le_succ
  intro d
  induction d generalizing n with
  | zero =>
      simp only [bundleCommonEnvelopeError_zero_order]
      exact bundleCommonEnvelopeError_nonneg ha 1 n
  | succ d ihd =>
      rw [bundleCommonEnvelopeError_succ_order,
        bundleCommonEnvelopeError_succ_order]
      apply bundleCommonNextRow_mono ha
      · exact bundleCommonEnvelopeError_nonneg ha d
      · intro m
        exact ihd m

theorem bundleCommonEnvelopeError_isEnvelope
    {a t : ℝ} (ha : 0 < a) (ha_one : a ≤ 1) :
    IsBundleCountingEnvelope
      (fun _ => a) (fun _ => t ^ 2) (fun _ => a) (t ^ 2)
      (bundleCommonEnvelopeError a t) := by
  refine
    { density_pos := fun _ => ha
      density_le_one := fun _ => ha_one
      defect_nonneg := fun _ => sq_nonneg t
      uniform_nonneg := sq_nonneg t
      floor_pos := fun _ => ha
      rankFloor := ?_
      error_nonneg :=
        bundleCommonEnvelopeError_nonneg ha.le
      error_mono_order := ?_
      error_mono_card := ?_
      step := ?_ }
  · intro i d hid
    exact le_rfl
  · intro d d' n hdd'
    exact
      (bundleCommonEnvelopeError_monotone_order
        ha.le n) hdd'
  · intro d n n' hnn'
    exact
      (bundleCommonEnvelopeError_monotone_card
        ha.le d) hnn'
  · intro d n
    rw [bundleCommonEnvelopeError_succ_order,
      bundleCommonEnvelopeError_succ_order,
      bundleCommonNextRow_succ]
    unfold bundleCommonStepIncrement
    ring_nf
    exact le_rfl

@[simp]
theorem bundleCommonNextRow_zero_parameter
    (a : ℝ) (lower : ℕ → ℝ)
    (hlower : ∀ n, lower n = 0) :
    ∀ n, bundleCommonNextRow a 0 lower n = 0 := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ihn =>
      rw [bundleCommonNextRow_succ, ihn]
      simp [bundleCommonStepIncrement, hlower]

@[simp]
theorem bundleCommonEnvelopeError_zero_parameter
    (a : ℝ) :
    ∀ d n, bundleCommonEnvelopeError a 0 d n = 0 := by
  intro d
  induction d with
  | zero =>
      intro n
      simp
  | succ d ihd =>
      intro n
      rw [bundleCommonEnvelopeError_succ_order]
      exact bundleCommonNextRow_zero_parameter a
        (bundleCommonEnvelopeError a 0 d) ihd n

theorem continuous_bundleCommonNextRow
    (a : ℝ) (lower : ℝ → ℕ → ℝ)
    (hlower : ∀ n, Continuous (fun t => lower t n)) :
    ∀ n,
      Continuous
        (fun t =>
          bundleCommonNextRow a t (lower t) n) := by
  intro n
  induction n with
  | zero =>
      simp only [bundleCommonNextRow_zero]
      fun_prop
  | succ n ihn =>
      simp only [bundleCommonNextRow_succ,
        bundleCommonStepIncrement]
      have h₁ := hlower (n + 1)
      have h₂ := hlower (2 * (n + 1))
      fun_prop

theorem continuous_bundleCommonEnvelopeError_real
    (a : ℝ) :
    ∀ d n,
      Continuous
        (fun t : ℝ =>
          bundleCommonEnvelopeError a t d n) := by
  intro d
  induction d with
  | zero =>
      intro n
      simp only [bundleCommonEnvelopeError_zero_order]
      fun_prop
  | succ d ihd =>
      intro n
      change
        Continuous (fun t : ℝ =>
          bundleCommonNextRow a t
            (bundleCommonEnvelopeError a t d) n)
      exact continuous_bundleCommonNextRow
        a
        (fun t m =>
          bundleCommonEnvelopeError a t d m)
        ihd n

theorem tendsto_bundleCommonEnvelopeError_zero
    (a : ℝ) (d n : ℕ) :
    Tendsto
      (fun t : ℝ =>
        bundleCommonEnvelopeError a t d n)
      (𝓝 0) (𝓝 0) := by
  simpa using
    (continuous_bundleCommonEnvelopeError_real a d n).tendsto 0

theorem exists_bundleCommonEnvelopeError_lt
    (a : ℝ) (rankBound edgeBound : ℕ)
    {parameterReserve errorReserve : ℝ}
    (hparameter : 0 < parameterReserve)
    (herror : 0 < errorReserve) :
    ∃ t : ℝ,
      0 < t ∧ t < parameterReserve ∧ t < 1 ∧
        bundleCommonEnvelopeError
            a t rankBound edgeBound <
          errorReserve := by
  have heventually :
      ∀ᶠ t : ℝ in 𝓝 0,
        bundleCommonEnvelopeError
            a t rankBound edgeBound <
          errorReserve :=
    (tendsto_bundleCommonEnvelopeError_zero
      a rankBound edgeBound).eventually_lt_const herror
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.eventually_nhds_iff_ball.mp heventually
  let t : ℝ := min δ (min parameterReserve 1) / 2
  have hmin :
      0 < min δ (min parameterReserve 1) := by
    exact lt_min hδ (lt_min hparameter zero_lt_one)
  have ht : 0 < t := by
    dsimp [t]
    linarith
  have htδ : t < δ := by
    dsimp [t]
    have hle :
        min δ (min parameterReserve 1) ≤ δ :=
      min_le_left _ _
    linarith
  have htparameter : t < parameterReserve := by
    dsimp [t]
    have hle :
        min δ (min parameterReserve 1) ≤
          min parameterReserve 1 :=
      min_le_right _ _
    have hle' : min parameterReserve 1 ≤ parameterReserve :=
      min_le_left _ _
    linarith
  have htone : t < 1 := by
    dsimp [t]
    have hle :
        min δ (min parameterReserve 1) ≤
          min parameterReserve 1 :=
      min_le_right _ _
    have hle' : min parameterReserve 1 ≤ 1 :=
      min_le_right _ _
    linarith
  refine ⟨t, ht, htparameter, htone, ?_⟩
  apply hball
  simpa [Real.dist_eq, abs_of_pos ht] using htδ

theorem exists_bundleCommonEnvelopeError_lt_half
    {a : ℝ} (ha : 0 < a) (ha_one : a ≤ 1)
    (rankBound edgeBound : ℕ) :
    ∃ t : ℝ,
      0 < t ∧ t < 1 ∧
      IsBundleCountingEnvelope
        (fun _ => a) (fun _ => t ^ 2) (fun _ => a) (t ^ 2)
        (bundleCommonEnvelopeError a t) ∧
      bundleCommonEnvelopeError
          a t rankBound edgeBound < 1 / 2 := by
  obtain ⟨t, ht, htone, _htone', hfinal⟩ :=
    exists_bundleCommonEnvelopeError_lt
      a rankBound edgeBound zero_lt_one
        (by norm_num : (0 : ℝ) < 1 / 2)
  exact ⟨t, ht, htone,
    bundleCommonEnvelopeError_isEnvelope ha ha_one,
    hfinal⟩

end Erdos3.FixedDensity

end

end OAI
