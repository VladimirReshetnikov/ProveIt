-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import OAI.Combinatorics.Progressions.FixedDensity.BundleCountingRecurrence
import OAI.Compat.Core

namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

abbrev DoubledOccurrenceVertex (g₀ : Finset K) :=
  {v : K // v ∈ g₀} ⊕ (Bool × EdgeComplement g₀)

def doubledVertexForget
    (g₀ : Finset K) :
    DoubledOccurrenceVertex g₀ → K
  | Sum.inl v => v.1
  | Sum.inr v => v.2.1

def doubledVertexLift
    (g₀ : Finset K) (copy : Bool) (v : K) :
    DoubledOccurrenceVertex g₀ :=
  if hv : v ∈ g₀ then
    Sum.inl ⟨v, hv⟩
  else
    Sum.inr ⟨copy, ⟨v, hv⟩⟩

@[simp]
theorem doubledVertexForget_lift
    (g₀ : Finset K) (copy : Bool) (v : K) :
    doubledVertexForget g₀
        (doubledVertexLift g₀ copy v) = v := by
  by_cases hv : v ∈ g₀ <;>
    simp [doubledVertexLift, doubledVertexForget, hv]

theorem doubledVertexLift_injective
    (g₀ : Finset K) (copy : Bool) :
    Function.Injective (doubledVertexLift g₀ copy) := by
  intro v w hvw
  have h :=
    congrArg (doubledVertexForget g₀) hvw
  simpa using h

def doubledAssignment
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : (EdgeComplement g₀ → G) ×
      (EdgeComplement g₀ → G)) :
    DoubledOccurrenceVertex g₀ → G
  | Sum.inl v => y v
  | Sum.inr (false, v) => z.1 v
  | Sum.inr (true, v) => z.2 v

def splitDoubledAssignmentEquiv
    (g₀ : Finset K) :
    (DoubledOccurrenceVertex g₀ → G) ≃
      (({v : K // v ∈ g₀} → G) ×
        ((EdgeComplement g₀ → G) ×
          (EdgeComplement g₀ → G))) where
  toFun x :=
    (fun v => x (Sum.inl v),
      (fun v => x (Sum.inr (false, v)),
        fun v => x (Sum.inr (true, v))))
  invFun p := doubledAssignment g₀ p.1 p.2
  left_inv x := by
    funext v
    rcases v with v | ⟨copy, v⟩
    · rfl
    · cases copy <;> rfl
  right_inv p := by
    rcases p with ⟨y, zfalse, ztrue⟩
    rfl

omit [DecidableEq K] in
@[simp]
theorem splitDoubledAssignmentEquiv_symm_apply
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : (EdgeComplement g₀ → G) ×
      (EdgeComplement g₀ → G)) :
    (splitDoubledAssignmentEquiv g₀).symm (y, z) =
      doubledAssignment g₀ y z :=
  rfl

theorem mean_splitDoubledAssignment
    [Fintype K] [Fintype G]
    (g₀ : Finset K)
    (f : (DoubledOccurrenceVertex g₀ → G) → ℝ) :
    mean f =
      mean₂ (fun y : {v : K // v ∈ g₀} → G =>
        fun z :
          (EdgeComplement g₀ → G) ×
            (EdgeComplement g₀ → G) =>
          f (doubledAssignment g₀ y z)) := by
  calc
    mean f =
        mean (fun p :
          ({v : K // v ∈ g₀} → G) ×
            ((EdgeComplement g₀ → G) ×
              (EdgeComplement g₀ → G)) =>
          f ((splitDoubledAssignmentEquiv g₀).symm p)) := by
      unfold mean
      apply Fintype.expect_equiv
        (splitDoubledAssignmentEquiv g₀)
      intro x
      simp
    _ = _ := by
      change
        mean (fun p :
          ({v : K // v ∈ g₀} → G) ×
            ((EdgeComplement g₀ → G) ×
              (EdgeComplement g₀ → G)) =>
          f (doubledAssignment g₀ p.1 p.2)) =
        _
      exact
        mean_prod_type
          (fun y : {v : K // v ∈ g₀} → G =>
            fun z :
              (EdgeComplement g₀ → G) ×
              (EdgeComplement g₀ → G) =>
              f (doubledAssignment g₀ y z))

@[simp]
theorem doubledAssignment_lift_false
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : (EdgeComplement g₀ → G) ×
      (EdgeComplement g₀ → G))
    (v : K) :
    doubledAssignment g₀ y z
        (doubledVertexLift g₀ false v) =
      (splitEdgeEquiv g₀).symm (y, z.1) v := by
  classical
  by_cases hv : v ∈ g₀
  · simp only [doubledVertexLift, dite_eq_left hv,
      doubledAssignment]
    unfold splitEdgeEquiv
    convert
      (Equiv.piCongrLeft_sumInl
        (fun _ : K => G) (edgeSumEquiv g₀)
        y z.1 ⟨v, hv⟩).symm using 1 ;
      simp [edgeSumEquiv]
  · simp only [doubledVertexLift, dite_eq_right hv,
      doubledAssignment]
    unfold splitEdgeEquiv
    convert
      (Equiv.piCongrLeft_sumInr
        (fun _ : K => G) (edgeSumEquiv g₀)
        y z.1 ⟨v, hv⟩).symm using 1 ;
      simp [edgeSumEquiv]

@[simp]
theorem doubledAssignment_lift_true
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : (EdgeComplement g₀ → G) ×
      (EdgeComplement g₀ → G))
    (v : K) :
    doubledAssignment g₀ y z
        (doubledVertexLift g₀ true v) =
      (splitEdgeEquiv g₀).symm (y, z.2) v := by
  classical
  by_cases hv : v ∈ g₀
  · simp only [doubledVertexLift, dite_eq_left hv,
      doubledAssignment]
    unfold splitEdgeEquiv
    convert
      (Equiv.piCongrLeft_sumInl
        (fun _ : K => G) (edgeSumEquiv g₀)
        y z.2 ⟨v, hv⟩).symm using 1 ;
      simp [edgeSumEquiv]
  · simp only [doubledVertexLift, dite_eq_right hv,
      doubledAssignment]
    unfold splitEdgeEquiv
    convert
      (Equiv.piCongrLeft_sumInr
        (fun _ : K => G) (edgeSumEquiv g₀)
        y z.2 ⟨v, hv⟩).symm using 1 ;
      simp [edgeSumEquiv]

def doubledEdge
    (g₀ : Finset K) (copy : Bool) (g : Finset K) :
    Finset (DoubledOccurrenceVertex g₀) :=
  g.image (doubledVertexLift g₀ copy)

theorem mem_doubledEdge
    (g₀ : Finset K) (copy : Bool)
    (g : Finset K) (v : K) (hv : v ∈ g) :
    doubledVertexLift g₀ copy v ∈
      doubledEdge g₀ copy g :=
  Finset.mem_image.mpr ⟨v, hv, rfl⟩

@[simp]
theorem image_forget_doubledEdge
    (g₀ : Finset K) (copy : Bool) (g : Finset K) :
    (doubledEdge g₀ copy g).image
        (doubledVertexForget g₀) = g := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    have huv : u = v := by
      simpa using hwv
    exact huv ▸ hu
  · intro hv
    exact
      Finset.mem_image.mpr
        ⟨doubledVertexLift g₀ copy v,
          mem_doubledEdge g₀ copy g v hv, by simp⟩

@[simp]
theorem card_doubledEdge
    (g₀ : Finset K) (copy : Bool) (g : Finset K) :
    (doubledEdge g₀ copy g).card = g.card := by
  rw [doubledEdge,
    Finset.card_image_of_injective _
      (doubledVertexLift_injective g₀ copy)]

theorem doubledEdge_copy_independent_of_subset
    (g₀ : Finset K) {g : Finset K}
    (hg : g ⊆ g₀) (copy copy' : Bool) :
    doubledEdge g₀ copy g =
      doubledEdge g₀ copy' g := by
  unfold doubledEdge
  apply Finset.image_congr
  intro v hv
  simp [doubledVertexLift, hg hv]

theorem doubledEdge_false_ne_true_of_mem_complement
    (g₀ : Finset K) {g : Finset K}
    {v : K} (hvg : v ∈ g) (hvoutside : v ∉ g₀) :
    doubledEdge g₀ false g ≠
      doubledEdge g₀ true g := by
  intro hedges
  have hv :
      doubledVertexLift g₀ false v ∈
        doubledEdge g₀ true g := by
    rw [← hedges]
    exact mem_doubledEdge g₀ false g v hvg
  obtain ⟨w, hwg, hwv⟩ :=
    Finset.mem_image.mp hv
  have hwv' : w = v := by
    have := congrArg
      (doubledVertexForget g₀) hwv
    simpa using this
  subst w
  simp [doubledVertexLift, hvoutside] at hwv

theorem doubledEdge_false_eq_true_iff_subset
    (g₀ : Finset K) (g : Finset K) :
    doubledEdge g₀ false g =
        doubledEdge g₀ true g ↔
      g ⊆ g₀ := by
  constructor
  · intro hedges v hvg
    by_contra hvoutside
    exact
      doubledEdge_false_ne_true_of_mem_complement
        g₀ hvg hvoutside hedges
  · intro hg
    exact doubledEdge_copy_independent_of_subset
      g₀ hg false true

abbrev DoubledEdgeSource
    (B : HypergraphBundle J K H) (g₀ : Finset K) :=
  Bool × {g : Finset K // g ∈ (B.edges.erase g₀)}

def doubledEdgeOfSource
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (s : B.DoubledEdgeSource g₀) :
    Finset (DoubledOccurrenceVertex g₀) :=
  doubledEdge g₀ s.1 s.2.1

noncomputable def doubledSourceProduct
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (x : DoubledOccurrenceVertex g₀ → G) : ℝ :=
  ∏ s : B.DoubledEdgeSource g₀,
    A s.2.1 (fun v =>
      x (doubledVertexLift g₀ s.1 v.1))

theorem doubledSourceProduct_doubledAssignment
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (y : {v : K // v ∈ g₀} → G)
    (z : (EdgeComplement g₀ → G) ×
      (EdgeComplement g₀ → G)) :
    B.doubledSourceProduct g₀ A
        (doubledAssignment g₀ y z) =
      B.edgeRemainderFiber g₀ A y z.1 *
        B.edgeRemainderFiber g₀ A y z.2 := by
  classical
  unfold doubledSourceProduct
  rw [Fintype.prod_prod_type, Fintype.prod_bool]
  simp_rw [doubledAssignment_lift_true,
    doubledAssignment_lift_false]
  have hfalse :
      (∏ g : {g : Finset K //
          g ∈ B.edges.erase g₀},
        A g.1 (fun v =>
          (splitEdgeEquiv g₀).symm
            (y, z.1) v.1)) =
        ∏ g ∈ B.edges.erase g₀,
          A g (edgeTuple g
            ((splitEdgeEquiv g₀).symm
              (y, z.1))) := by
    calc
      _ = ∏ g : {g : Finset K //
            g ∈ B.edges.erase g₀},
          A g.1 (edgeTuple g.1
            ((splitEdgeEquiv g₀).symm
              (y, z.1))) := by
        apply Finset.prod_congr rfl
        intro g _hg
        apply congrArg (A g.1)
        rfl
      _ = _ :=
        Finset.prod_coe_sort
          (B.edges.erase g₀)
          (fun g => A g (edgeTuple g
            ((splitEdgeEquiv g₀).symm
              (y, z.1))))
  have htrue :
      (∏ g : {g : Finset K //
          g ∈ B.edges.erase g₀},
        A g.1 (fun v =>
          (splitEdgeEquiv g₀).symm
            (y, z.2) v.1)) =
        ∏ g ∈ B.edges.erase g₀,
          A g (edgeTuple g
            ((splitEdgeEquiv g₀).symm
              (y, z.2))) := by
    calc
      _ = ∏ g : {g : Finset K //
            g ∈ B.edges.erase g₀},
          A g.1 (edgeTuple g.1
            ((splitEdgeEquiv g₀).symm
              (y, z.2))) := by
        apply Finset.prod_congr rfl
        intro g _hg
        apply congrArg (A g.1)
        rfl
      _ = _ :=
        Finset.prod_coe_sort
          (B.edges.erase g₀)
          (fun g => A g (edgeTuple g
            ((splitEdgeEquiv g₀).symm
              (y, z.2))))
  rw [htrue, hfalse]
  unfold edgeRemainderFiber edgeRemainder bundleProduct
  rw [mul_comm]
  rfl

theorem doubledRemainderMoment_eq_mean_doubledSourceProduct
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.doubledRemainderMoment g₀ A =
      mean (B.doubledSourceProduct g₀ A) := by
  rw [B.doubledRemainderMoment_eq_mean₂_pair]
  rw [mean_splitDoubledAssignment]
  simp_rw [B.doubledSourceProduct_doubledAssignment]

def doubledEdges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    Finset (Finset (DoubledOccurrenceVertex g₀)) :=
  Finset.univ.image (B.doubledEdgeOfSource g₀)

theorem doubledEdgeOfSource_mem_doubledEdges
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (s : B.DoubledEdgeSource g₀) :
    B.doubledEdgeOfSource g₀ s ∈
      B.doubledEdges g₀ := by
  classical
  exact Finset.mem_image.mpr
    ⟨s, Finset.mem_univ s, rfl⟩

theorem mem_doubledEdges_iff
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (d : Finset (DoubledOccurrenceVertex g₀)) :
    d ∈ B.doubledEdges g₀ ↔
      ∃ (copy : Bool) (g : Finset K),
        g ∈ B.edges.erase g₀ ∧
          doubledEdge g₀ copy g = d := by
  classical
  constructor
  · intro hd
    obtain ⟨s, _hs, hsd⟩ :=
      Finset.mem_image.mp hd
    exact ⟨s.1, s.2.1, s.2.2, hsd⟩
  · rintro ⟨copy, g, hg, rfl⟩
    exact
      Finset.mem_image.mpr
        ⟨(copy, ⟨g, hg⟩), Finset.mem_univ _, rfl⟩

def doubledProjection
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    DoubledOccurrenceVertex g₀ → J :=
  fun v => B.projection (doubledVertexForget g₀ v)

@[simp]
theorem doubledProjection_lift
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (copy : Bool) (v : K) :
    B.doubledProjection g₀
        (doubledVertexLift g₀ copy v) =
      B.projection v := by
  simp [doubledProjection]

@[simp]
theorem image_doubledProjection_doubledEdge
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (copy : Bool) (g : Finset K) :
    (doubledEdge g₀ copy g).image
        (B.doubledProjection g₀) =
      g.image B.projection := by
  classical
  ext j
  constructor
  · intro hj
    obtain ⟨v, hv, hvj⟩ := Finset.mem_image.mp hj
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr
      ⟨w, hw, by simpa using hvj⟩
  · intro hj
    obtain ⟨v, hv, hvj⟩ := Finset.mem_image.mp hj
    exact
      Finset.mem_image.mpr
        ⟨doubledVertexLift g₀ copy v,
          mem_doubledEdge g₀ copy g v hv,
          by simpa using hvj⟩

def duplicateOutside
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    HypergraphBundle J (DoubledOccurrenceVertex g₀) H where
  edges := B.doubledEdges g₀
  projection := B.doubledProjection g₀
  projection_injective_on_edge := by
    intro d hd v hv w hw hvw
    obtain ⟨copy, g, hg, rfl⟩ :=
      (B.mem_doubledEdges_iff g₀ d).1 hd
    obtain ⟨v₀, hv₀, rfl⟩ :=
      Finset.mem_image.mp hv
    obtain ⟨w₀, hw₀, rfl⟩ :=
      Finset.mem_image.mp hw
    apply congrArg (doubledVertexLift g₀ copy)
    apply B.projection_injective_on_edge g
      (Finset.mem_of_mem_erase hg) hv₀ hw₀
    simpa using hvw
  projection_mem_base := by
    intro d hd
    obtain ⟨copy, g, hg, rfl⟩ :=
      (B.mem_doubledEdges_iff g₀ d).1 hd
    rw [image_doubledProjection_doubledEdge]
    exact B.projection_mem_base g
      (Finset.mem_of_mem_erase hg)

@[simp]
theorem duplicateOutside_edges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.duplicateOutside g₀).edges =
      B.doubledEdges g₀ :=
  rfl

@[simp]
theorem duplicateOutside_projection
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.duplicateOutside g₀).projection =
      B.doubledProjection g₀ :=
  rfl

theorem duplicateOutside_edge_card
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    {d : Finset (DoubledOccurrenceVertex g₀)}
    (hd : d ∈ (B.duplicateOutside g₀).edges) :
    ∃ g ∈ B.edges.erase g₀, d.card = g.card := by
  obtain ⟨copy, g, hg, hgd⟩ :=
    (B.mem_doubledEdges_iff g₀ d).1 hd
  subst d
  exact ⟨g, hg, card_doubledEdge g₀ copy g⟩

theorem duplicateOutside_order_le_eraseEdge
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.duplicateOutside g₀).order ≤
      (B.eraseEdge g₀).order := by
  unfold order
  apply Finset.sup_le
  intro d hd
  obtain ⟨g, hg, hdg⟩ :=
    B.duplicateOutside_edge_card g₀ hd
  rw [hdg]
  exact (B.eraseEdge g₀).edge_card_le_order hg

theorem duplicateOutside_order_le
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.duplicateOutside g₀).order ≤ B.order :=
  (B.duplicateOutside_order_le_eraseEdge g₀).trans
    (B.eraseEdge_order_le g₀)

theorem card_doubledEdges_le
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.doubledEdges g₀).card ≤
      2 * (B.edges.erase g₀).card := by
  unfold doubledEdges
  calc
    (Finset.univ.image
        (B.doubledEdgeOfSource g₀)).card ≤
        (Finset.univ :
          Finset (B.DoubledEdgeSource g₀)).card :=
      Finset.card_image_le
    _ = 2 * (B.edges.erase g₀).card := by
      simp [DoubledEdgeSource]

def RemainingEdgesMeetComplement
    (B : HypergraphBundle J K H) (g₀ : Finset K) : Prop :=
  ∀ g ∈ B.edges.erase g₀,
    ∃ v ∈ g, v ∉ g₀

theorem doubledEdgeOfSource_injective
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (houtside : B.RemainingEdgesMeetComplement g₀) :
    Function.Injective (B.doubledEdgeOfSource g₀) := by
  rintro ⟨copy, ⟨g, hg⟩⟩
    ⟨copy', ⟨g', hg'⟩⟩ hedges
  change
    doubledEdge g₀ copy g =
      doubledEdge g₀ copy' g' at hedges
  have hgg' : g = g' := by
    have himage :=
      congrArg
        (Finset.image (doubledVertexForget g₀))
        hedges
    simpa using himage
  subst g'
  have hcopy : copy = copy' := by
    obtain ⟨v, hvg, hvoutside⟩ :=
      houtside g hg
    have hv :
        doubledVertexLift g₀ copy v ∈
          doubledEdge g₀ copy' g := by
      rw [← hedges]
      exact mem_doubledEdge g₀ copy g v hvg
    obtain ⟨w, hwg, hwv⟩ :=
      Finset.mem_image.mp hv
    have hwv' : w = v := by
      have := congrArg
        (doubledVertexForget g₀) hwv
      simpa using this
    subst w
    simpa [doubledVertexLift, hvoutside] using
      hwv.symm
  subst copy'
  rfl

noncomputable def doubledEdgeSourceEquiv
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (houtside : B.RemainingEdgesMeetComplement g₀) :
    B.DoubledEdgeSource g₀ ≃
      {d : Finset (DoubledOccurrenceVertex g₀) //
        d ∈ B.doubledEdges g₀} := by
  classical
  apply Equiv.ofBijective
    (fun s =>
      ⟨B.doubledEdgeOfSource g₀ s,
        B.doubledEdgeOfSource_mem_doubledEdges
          g₀ s⟩)
  constructor
  · intro s t hst
    apply B.doubledEdgeOfSource_injective
      g₀ houtside
    exact congrArg Subtype.val hst
  · rintro ⟨d, hd⟩
    obtain ⟨s, _hs, hsd⟩ :=
      Finset.mem_image.mp hd
    refine ⟨s, ?_⟩
    apply Subtype.ext
    exact hsd

noncomputable def sourceOfDoubledEdge
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (houtside : B.RemainingEdgesMeetComplement g₀)
    {d : Finset (DoubledOccurrenceVertex g₀)}
    (hd : d ∈ B.doubledEdges g₀) :
    B.DoubledEdgeSource g₀ :=
  (B.doubledEdgeSourceEquiv g₀ houtside).symm
    ⟨d, hd⟩

theorem doubledEdgeOfSource_sourceOfDoubledEdge
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (houtside : B.RemainingEdgesMeetComplement g₀)
    {d : Finset (DoubledOccurrenceVertex g₀)}
    (hd : d ∈ B.doubledEdges g₀) :
    B.doubledEdgeOfSource g₀
        (B.sourceOfDoubledEdge g₀ houtside hd) = d := by
  exact congrArg Subtype.val
    (Equiv.apply_symm_apply
      (B.doubledEdgeSourceEquiv g₀ houtside)
      ⟨d, hd⟩)

theorem sourceOfDoubledEdge_doubledEdgeOfSource
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (houtside : B.RemainingEdgesMeetComplement g₀)
    (s : B.DoubledEdgeSource g₀) :
    B.sourceOfDoubledEdge g₀ houtside
        (B.doubledEdgeOfSource_mem_doubledEdges
          g₀ s) = s := by
  exact
    Equiv.symm_apply_apply
      (B.doubledEdgeSourceEquiv g₀ houtside) s

theorem card_doubledEdges_eq
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (houtside : B.RemainingEdgesMeetComplement g₀) :
    (B.doubledEdges g₀).card =
      2 * (B.edges.erase g₀).card := by
  unfold doubledEdges
  rw [Finset.card_image_of_injective _
    (B.doubledEdgeOfSource_injective g₀ houtside)]
  simp [DoubledEdgeSource]

theorem doubledEdge_image_forget_of_subset
    (g₀ : Finset K) (copy : Bool)
    {g : Finset K}
    {d : Finset (DoubledOccurrenceVertex g₀)}
    (hd : d ⊆ doubledEdge g₀ copy g) :
    doubledEdge g₀ copy
        (d.image (doubledVertexForget g₀)) = d := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
    obtain ⟨u, hu, huw⟩ := Finset.mem_image.mp hw
    have huLift :
        doubledVertexLift g₀ copy
            (doubledVertexForget g₀ u) = u := by
      obtain ⟨t, ht, rfl⟩ :=
        Finset.mem_image.mp (hd hu)
      simp
    rw [← hwv, ← huw, huLift]
    exact hu
  · intro hv
    have hvLift :
        doubledVertexLift g₀ copy
            (doubledVertexForget g₀ v) = v := by
      obtain ⟨t, ht, rfl⟩ :=
        Finset.mem_image.mp (hd hv)
      simp
    exact Finset.mem_image.mpr
      ⟨doubledVertexForget g₀ v,
        Finset.mem_image.mpr ⟨v, hv, rfl⟩,
        hvLift⟩

theorem duplicateOutside_closed
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (hclosed :
      (B.eraseEdge g₀).IsClosedUnderInclusion) :
    (B.duplicateOutside g₀).IsClosedUnderInclusion := by
  intro d hd f hfd
  obtain ⟨copy, g, hg, rfl⟩ :=
    (B.mem_doubledEdges_iff g₀ d).1 hd
  let h : Finset K :=
    f.image (doubledVertexForget g₀)
  have hhg : h ⊆ g := by
    intro v hv
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
    obtain ⟨u, hu, huw⟩ :=
      Finset.mem_image.mp (hfd hw)
    rw [← hwv, ← huw]
    simpa using hu
  have hh : h ∈ B.edges.erase g₀ :=
    hclosed hg hhg
  have hlift :
      doubledEdge g₀ copy h = f :=
    doubledEdge_image_forget_of_subset
      g₀ copy hfd
  rw [← hlift]
  exact
    (B.mem_doubledEdges_iff g₀
      (doubledEdge g₀ copy h)).2
      ⟨copy, h, hh, rfl⟩

theorem duplicateOutside_closed_of_maximal
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card) :
    (B.duplicateOutside g₀).IsClosedUnderInclusion :=
  B.duplicateOutside_closed g₀
    (B.eraseEdge_closed_of_maximal
      hclosed hg₀ hmax)

end HypergraphBundle

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace HypergraphBundle

variable {J K : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

def filterEdges
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P] :
    HypergraphBundle J K H where
  edges := B.edges.filter P
  projection := B.projection
  projection_injective_on_edge := by
    intro g hg
    exact B.projection_injective_on_edge g
      (Finset.mem_filter.mp hg).1
  projection_mem_base := by
    intro g hg
    exact B.projection_mem_base g
      (Finset.mem_filter.mp hg).1

@[simp]
theorem filterEdges_edges
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P] :
    (B.filterEdges P).edges = B.edges.filter P :=
  rfl

@[simp]
theorem mem_filterEdges_edges
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P]
    (g : Finset K) :
    g ∈ (B.filterEdges P).edges ↔
      g ∈ B.edges ∧ P g := by
  simp [filterEdges]

@[simp]
theorem filterEdges_projection
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P] :
    (B.filterEdges P).projection = B.projection :=
  rfl

theorem filterEdges_order_le
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P] :
    (B.filterEdges P).order ≤ B.order := by
  unfold order
  apply Finset.sup_le
  intro g hg
  exact B.edge_card_le_order
    (Finset.mem_filter.mp hg).1

theorem card_filterEdges_edges_le
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P] :
    (B.filterEdges P).edges.card ≤ B.edges.card := by
  exact Finset.card_le_card (Finset.filter_subset _ _)

theorem filterEdges_closed
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P]
    (hclosed : B.IsClosedUnderInclusion)
    (hP : ∀ ⦃g⦄, P g →
      ∀ ⦃f⦄, f ⊆ g → P f) :
    (B.filterEdges P).IsClosedUnderInclusion := by
  intro g hg f hfg
  have hg' := (B.mem_filterEdges_edges P g).1 hg
  exact (B.mem_filterEdges_edges P f).2
    ⟨hclosed hg'.1 hfg, hP hg'.2 hfg⟩

def lowerOrder
    (B : HypergraphBundle J K H) (d : ℕ) :
    HypergraphBundle J K H :=
  B.filterEdges fun g => g.card < d

@[simp]
theorem lowerOrder_edges
    (B : HypergraphBundle J K H) (d : ℕ) :
    (B.lowerOrder d).edges =
      B.edges.filter fun g => g.card < d :=
  rfl

@[simp]
theorem mem_lowerOrder_edges
    (B : HypergraphBundle J K H)
    (d : ℕ) (g : Finset K) :
    g ∈ (B.lowerOrder d).edges ↔
      g ∈ B.edges ∧ g.card < d := by
  simp [lowerOrder]

theorem lowerOrder_order_lt
    (B : HypergraphBundle J K H)
    {d : ℕ} (hd : 0 < d) :
    (B.lowerOrder d).order < d := by
  unfold order
  rw [Finset.sup_lt_iff hd]
  intro g hg
  exact (Finset.mem_filter.mp hg).2

theorem lowerOrder_order_le
    (B : HypergraphBundle J K H) (d : ℕ) :
    (B.lowerOrder d).order ≤ B.order :=
  B.filterEdges_order_le _

theorem card_lowerOrder_edges_le
    (B : HypergraphBundle J K H) (d : ℕ) :
    (B.lowerOrder d).edges.card ≤ B.edges.card :=
  B.card_filterEdges_edges_le _

theorem lowerOrder_closed
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    (d : ℕ) :
    (B.lowerOrder d).IsClosedUnderInclusion := by
  apply B.filterEdges_closed _ hclosed
  intro g hg f hfg
  exact (Finset.card_le_card hfg).trans_lt hg

def strictBoundary
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    HypergraphBundle J K H :=
  B.filterEdges fun g => g ⊂ g₀

@[simp]
theorem strictBoundary_edges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.strictBoundary g₀).edges =
      B.edges.filter fun g => g ⊂ g₀ :=
  rfl

@[simp]
theorem mem_strictBoundary_edges
    (B : HypergraphBundle J K H)
    (g₀ g : Finset K) :
    g ∈ (B.strictBoundary g₀).edges ↔
      g ∈ B.edges ∧ g ⊂ g₀ := by
  simp [strictBoundary]

theorem strictBoundary_order_le
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.strictBoundary g₀).order ≤ B.order :=
  B.filterEdges_order_le _

theorem strictBoundary_order_lt
    (B : HypergraphBundle J K H)
    {g₀ : Finset K} (hg₀ : g₀.Nonempty) :
    (B.strictBoundary g₀).order < g₀.card := by
  unfold order
  rw [Finset.sup_lt_iff (Finset.card_pos.mpr hg₀)]
  intro g hg
  exact Finset.card_lt_card (Finset.mem_filter.mp hg).2

theorem card_strictBoundary_edges_le
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.strictBoundary g₀).edges.card ≤ B.edges.card :=
  B.card_filterEdges_edges_le _

theorem strictBoundary_closed
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    (g₀ : Finset K) :
    (B.strictBoundary g₀).IsClosedUnderInclusion := by
  apply B.filterEdges_closed _ hclosed
  intro g hg f hfg
  exact lt_of_le_of_lt hfg hg

noncomputable def bundleMainProduct
    (B : HypergraphBundle J K H)
    (p : Finset J → ℝ) : ℝ :=
  ∏ g ∈ B.edges, p (g.image B.projection)

@[simp]
theorem bundleMainProduct_filterEdges
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P]
    (p : Finset J → ℝ) :
    (B.filterEdges P).bundleMainProduct p =
      ∏ g ∈ B.edges.filter P,
        p (g.image B.projection) :=
  rfl

@[simp]
theorem bundleMainProduct_lowerOrder
    (B : HypergraphBundle J K H)
    (d : ℕ) (p : Finset J → ℝ) :
    (B.lowerOrder d).bundleMainProduct p =
      ∏ g ∈ B.edges.filter (fun g => g.card < d),
        p (g.image B.projection) :=
  rfl

@[simp]
theorem bundleMainProduct_strictBoundary
    (B : HypergraphBundle J K H)
    (g₀ : Finset K) (p : Finset J → ℝ) :
    (B.strictBoundary g₀).bundleMainProduct p =
      ∏ g ∈ B.edges.filter (fun g => g ⊂ g₀),
        p (g.image B.projection) :=
  rfl

theorem bundleMainProduct_filter_mul_filter_not
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P]
    (p : Finset J → ℝ) :
    (B.filterEdges P).bundleMainProduct p *
        (B.filterEdges fun g => ¬ P g).bundleMainProduct p =
      B.bundleMainProduct p := by
  classical
  exact Finset.prod_filter_mul_prod_filter_not
    (s := B.edges)
    (p := P)
    (f := fun g => p (g.image B.projection))

theorem bundleMainProduct_eraseEdge_mul
    (B : HypergraphBundle J K H)
    (p : Finset J → ℝ)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges) :
    (B.eraseEdge g₀).bundleMainProduct p *
        p (g₀.image B.projection) =
      B.bundleMainProduct p := by
  classical
  unfold bundleMainProduct
  simp only [eraseEdge]
  rw [Finset.prod_erase_mul _ _ hg₀]

theorem doubledEdge_injective
    (g₀ : Finset K) (copy : Bool) :
    Function.Injective (doubledEdge g₀ copy) := by
  intro g h hgh
  have himage :=
    congrArg
      (Finset.image (doubledVertexForget g₀)) hgh
  simpa using himage

theorem doubledEdges_eq_image_union
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    B.doubledEdges g₀ =
      (B.edges.erase g₀).image
          (doubledEdge g₀ false) ∪
        (B.edges.erase g₀).image
          (doubledEdge g₀ true) := by
  classical
  ext d
  constructor
  · intro hd
    obtain ⟨copy, g, hg, rfl⟩ :=
      (B.mem_doubledEdges_iff g₀ d).1 hd
    cases copy
    · exact Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
  · intro hd
    rcases Finset.mem_union.mp hd with hd | hd
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hd
      exact (B.mem_doubledEdges_iff g₀ _).2
        ⟨false, g, hg, rfl⟩
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hd
      exact (B.mem_doubledEdges_iff g₀ _).2
        ⟨true, g, hg, rfl⟩

theorem image_true_sdiff_image_false
    (g₀ : Finset K) (s : Finset (Finset K)) :
    s.image (doubledEdge g₀ true) \
        s.image (doubledEdge g₀ false) =
      (s.filter fun g => ¬ g ⊆ g₀).image
        (doubledEdge g₀ true) := by
  classical
  ext d
  constructor
  · intro hd
    have hdtrue :
        d ∈ s.image (doubledEdge g₀ true) :=
      (Finset.mem_sdiff.mp hd).1
    obtain ⟨g, hg, hgd⟩ :=
      Finset.mem_image.mp hdtrue
    subst d
    apply Finset.mem_image.mpr
    refine ⟨g, Finset.mem_filter.mpr ⟨hg, ?_⟩, rfl⟩
    intro hgsub
    apply (Finset.mem_sdiff.mp hd).2
    apply Finset.mem_image.mpr
    refine ⟨g, hg, ?_⟩
    exact
      (doubledEdge_copy_independent_of_subset
        g₀ hgsub false true)
  · intro hd
    obtain ⟨g, hg, hgd⟩ :=
      Finset.mem_image.mp hd
    subst d
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_image.mpr
      ⟨g, (Finset.mem_filter.mp hg).1, rfl⟩, ?_⟩
    intro hfalse
    obtain ⟨h, hh, hhg⟩ :=
      Finset.mem_image.mp hfalse
    have hgh : h = g := by
      have himage :=
        congrArg
          (Finset.image (doubledVertexForget g₀)) hhg
      simpa using himage
    subst h
    exact (Finset.mem_filter.mp hg).2
      ((doubledEdge_false_eq_true_iff_subset
        g₀ g).1 hhg)

theorem prod_image_doubledEdge_main
    (B : HypergraphBundle J K H)
    (g₀ : Finset K) (copy : Bool)
    (s : Finset (Finset K))
    (p : Finset J → ℝ) :
    (∏ d ∈ s.image (doubledEdge g₀ copy),
        p (d.image (B.doubledProjection g₀))) =
      ∏ g ∈ s, p (g.image B.projection) := by
  classical
  rw [Finset.prod_image
    (doubledEdge_injective g₀ copy).injOn]
  simp

theorem bundleMainProduct_duplicateOutside
    (B : HypergraphBundle J K H)
    (g₀ : Finset K) (p : Finset J → ℝ) :
    (B.duplicateOutside g₀).bundleMainProduct p =
      (∏ g ∈ (B.edges.erase g₀).filter
          (fun g => g ⊆ g₀),
        p (g.image B.projection)) *
      ∏ g ∈ (B.edges.erase g₀).filter
          (fun g => ¬ g ⊆ g₀),
        (p (g.image B.projection)) ^ 2 := by
  classical
  let s := B.edges.erase g₀
  let first :=
    s.image (doubledEdge g₀ false)
  let second :=
    s.image (doubledEdge g₀ true)
  have hsplit :
      (∏ g ∈ s.filter (fun g => g ⊆ g₀),
          p (g.image B.projection)) *
          (∏ g ∈ s.filter (fun g => ¬ g ⊆ g₀),
            p (g.image B.projection)) =
        ∏ g ∈ s, p (g.image B.projection) :=
    Finset.prod_filter_mul_prod_filter_not
      s (fun g => g ⊆ g₀)
        (fun g => p (g.image B.projection))
  calc
    (B.duplicateOutside g₀).bundleMainProduct p =
        ∏ d ∈ first ∪ second,
          p (d.image (B.doubledProjection g₀)) := by
      unfold bundleMainProduct first second
      simp only [duplicateOutside_edges,
        duplicateOutside_projection]
      rw [B.doubledEdges_eq_image_union g₀]
    _ = ∏ d ∈ first ∪ (second \ first),
          p (d.image (B.doubledProjection g₀)) := by
      rw [Finset.union_sdiff_self_eq_union]
    _ =
        (∏ d ∈ first,
          p (d.image (B.doubledProjection g₀))) *
        ∏ d ∈ second \ first,
          p (d.image (B.doubledProjection g₀)) := by
      exact Finset.prod_union Finset.disjoint_sdiff
    _ =
        (∏ g ∈ s, p (g.image B.projection)) *
        ∏ g ∈ s.filter (fun g => ¬ g ⊆ g₀),
          p (g.image B.projection) := by
      unfold first second
      rw [image_true_sdiff_image_false]
      rw [B.prod_image_doubledEdge_main g₀ false]
      rw [B.prod_image_doubledEdge_main g₀ true]
    _ =
        ((∏ g ∈ s.filter (fun g => g ⊆ g₀),
            p (g.image B.projection)) *
          ∏ g ∈ s.filter (fun g => ¬ g ⊆ g₀),
            p (g.image B.projection)) *
        ∏ g ∈ s.filter (fun g => ¬ g ⊆ g₀),
          p (g.image B.projection) := by
      rw [hsplit]
    _ =
        (∏ g ∈ s.filter (fun g => g ⊆ g₀),
            p (g.image B.projection)) *
          ∏ g ∈ s.filter (fun g => ¬ g ⊆ g₀),
            (p (g.image B.projection)) ^ 2 := by
      rw [mul_assoc, ← Finset.prod_mul_distrib]
      simp only [pow_two]
    _ = _ := rfl

theorem bundleMainProduct_duplicateOutside_lowerOrder
    (B : HypergraphBundle J K H)
    (g₀ : Finset K) (p : Finset J → ℝ) :
    ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleMainProduct p =
      (B.strictBoundary g₀).bundleMainProduct p *
      ∏ g ∈ B.edges.filter
          (fun g => g.card < g₀.card ∧ ¬ g ⊆ g₀),
        (p (g.image B.projection)) ^ 2 := by
  classical
  rw [(B.lowerOrder g₀.card).bundleMainProduct_duplicateOutside g₀ p]
  have hg₀' :
      g₀ ∉ B.edges.filter (fun g => g.card < g₀.card) := by
    simp
  have hboundary :
      (B.edges.filter (fun g => g.card < g₀.card)).filter
          (fun g => g ⊆ g₀) =
        B.edges.filter (fun g => g ⊂ g₀) := by
    ext g
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hgB, hgcard⟩, hgsub⟩
      exact ⟨hgB,
        Finset.ssubset_iff_subset_ne.mpr
          ⟨hgsub, fun hgeq => by
            subst g
            exact (Nat.lt_irrefl _ hgcard)⟩⟩
    · rintro ⟨hgB, hgstrict⟩
      exact ⟨⟨hgB,
        Finset.card_lt_card hgstrict⟩, hgstrict.1⟩
  have hexterior :
      (B.edges.filter (fun g => g.card < g₀.card)).filter
          (fun g => ¬ g ⊆ g₀) =
        B.edges.filter
          (fun g => g.card < g₀.card ∧ ¬ g ⊆ g₀) := by
    ext g
    simp only [Finset.mem_filter]
    tauto
  simp only [lowerOrder, strictBoundary,
    filterEdges, bundleMainProduct]
  rw [Finset.erase_eq_of_notMem hg₀',
    hboundary, hexterior]

end HypergraphBundle

end Erdos3.FixedDensity

end

end OAI
