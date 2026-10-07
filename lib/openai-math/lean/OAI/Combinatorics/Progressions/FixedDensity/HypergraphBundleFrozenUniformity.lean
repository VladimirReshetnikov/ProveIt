-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import Mathlib.Data.Fin.Tuple.Finset
import OAI.Combinatorics.Progressions.FixedDensity.ConfigurationWeightedDefect
import OAI.Combinatorics.Progressions.FixedDensity.HypergraphBundleRelativeCounting
import OAI.Compat.Core
import OAI.Compat.Order

namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def positiveOrderedFaceEdge
    {k r : ℕ} (e : PositiveOrderedFace k r) :
    Finset (Fin k) :=
  Finset.univ.map e.face.toEmbedding

@[simp]
theorem positiveOrderedFaceEdge_card
    {k r : ℕ} (e : PositiveOrderedFace k r) :
    (positiveOrderedFaceEdge e).card = e.rank := by
  simp [positiveOrderedFaceEdge, PositiveOrderedFace.rank]

theorem positiveOrderedFaceEdge_nonempty
    {k r : ℕ} (e : PositiveOrderedFace k r) :
    (positiveOrderedFaceEdge e).Nonempty := by
  apply Finset.card_pos.mp
  rw [positiveOrderedFaceEdge_card]
  exact e.rank_pos

theorem positiveOrderedFaceEdge_card_le
    {k r : ℕ} (e : PositiveOrderedFace k r) :
    (positiveOrderedFaceEdge e).card ≤ r := by
  rw [positiveOrderedFaceEdge_card]
  unfold PositiveOrderedFace.rank
  omega

@[simp]
theorem mem_positiveOrderedFaceEdge
    {k r : ℕ} (e : PositiveOrderedFace k r)
    (v : Fin k) :
    v ∈ positiveOrderedFaceEdge e ↔
      v ∈ Set.range e.face := by
  simp [positiveOrderedFaceEdge]

noncomputable def positiveOrderedFaceOfEdge
    {k r : ℕ} (t : Finset (Fin k))
    (ht : t.Nonempty) (htr : t.card ≤ r) :
    PositiveOrderedFace k r := by
  let j : Fin r :=
    ⟨t.card - 1, by
      have htcard : 0 < t.card :=
        Finset.card_pos.mpr ht
      omega⟩
  refine ⟨j, ?_⟩
  have hcard : t.card = j.1 + 1 := by
    dsimp [j]
    have htcard : 0 < t.card :=
      Finset.card_pos.mpr ht
    omega
  exact t.orderEmbOfFin hcard

@[simp]
theorem positiveOrderedFaceEdge_ofEdge
    {k r : ℕ} (t : Finset (Fin k))
    (ht : t.Nonempty) (htr : t.card ≤ r) :
    positiveOrderedFaceEdge
        (positiveOrderedFaceOfEdge t ht htr) = t := by
  dsimp only [positiveOrderedFaceEdge, positiveOrderedFaceOfEdge]
  exact Finset.map_orderEmbOfFin_univ t _

theorem positiveOrderedFaceEdge_injective
    {k r : ℕ} :
    Function.Injective
      (positiveOrderedFaceEdge :
        PositiveOrderedFace k r → Finset (Fin k)) := by
  intro e f hef
  have hrank : e.rank = f.rank := by
    rw [← positiveOrderedFaceEdge_card e,
      ← positiveOrderedFaceEdge_card f, hef]
  rcases e with ⟨je, e⟩
  rcases f with ⟨jf, f⟩
  simp only [PositiveOrderedFace.rank] at hrank
  have hj : je = jf := by
    apply Fin.ext
    omega
  subst jf
  have hrange : Set.range e = Set.range f := by
    ext v
    have hv :=
      congrArg
        (fun s : Finset (Fin k) => v ∈ s) hef
    simpa [positiveOrderedFaceEdge] using hv
  have hef' : e = f :=
    (OrderEmbedding.range_inj_of_wellFoundedLT).mp hrange
  subst f
  rfl

@[simp]
theorem positiveOrderedFaceOfEdge_edge
    {k r : ℕ} (e : PositiveOrderedFace k r) :
    positiveOrderedFaceOfEdge
        (positiveOrderedFaceEdge e)
        (positiveOrderedFaceEdge_nonempty e)
        (positiveOrderedFaceEdge_card_le e) = e := by
  apply positiveOrderedFaceEdge_injective
  exact positiveOrderedFaceEdge_ofEdge
    (positiveOrderedFaceEdge e)
    (positiveOrderedFaceEdge_nonempty e)
    (positiveOrderedFaceEdge_card_le e)

abbrev PositiveOrderedBundleEdge (k r : ℕ) :=
  {t : Finset (Fin k) // t.Nonempty ∧ t.card ≤ r}

noncomputable def positiveOrderedFaceEdgeEquiv
    (k r : ℕ) :
    PositiveOrderedFace k r ≃
      PositiveOrderedBundleEdge k r where
  toFun e :=
    ⟨positiveOrderedFaceEdge e,
      positiveOrderedFaceEdge_nonempty e,
      positiveOrderedFaceEdge_card_le e⟩
  invFun t :=
    positiveOrderedFaceOfEdge t.1 t.2.1 t.2.2
  left_inv e :=
    positiveOrderedFaceOfEdge_edge e
  right_inv t := by
    apply Subtype.ext
    exact positiveOrderedFaceEdge_ofEdge
      t.1 t.2.1 t.2.2

noncomputable def orderedConfigurationBaseEdges
    (k r : ℕ) : Finset (Finset (Fin k)) :=
  insert ∅
    (Finset.univ.image
      (positiveOrderedFaceEdge :
        PositiveOrderedFace k r → Finset (Fin k)))

@[simp]
theorem empty_mem_orderedConfigurationBaseEdges
    (k r : ℕ) :
    ∅ ∈ orderedConfigurationBaseEdges k r := by
  simp [orderedConfigurationBaseEdges]

theorem empty_not_mem_positiveOrderedFaceEdge_image
    (k r : ℕ) :
    (∅ : Finset (Fin k)) ∉
      Finset.univ.image
        (positiveOrderedFaceEdge :
          PositiveOrderedFace k r → Finset (Fin k)) := by
  intro h
  obtain ⟨e, _he, hedge⟩ :=
    Finset.mem_image.mp h
  exact (positiveOrderedFaceEdge_nonempty e).ne_empty
    hedge

@[simp]
theorem mem_orderedConfigurationBaseEdges_iff
    {k r : ℕ} (t : Finset (Fin k)) :
    t ∈ orderedConfigurationBaseEdges k r ↔
      t.card ≤ r := by
  constructor
  · intro ht
    rw [orderedConfigurationBaseEdges,
      Finset.mem_insert] at ht
    rcases ht with rfl | ht
    · simp
    · obtain ⟨e, _he, rfl⟩ :=
        Finset.mem_image.mp ht
      exact positiveOrderedFaceEdge_card_le e
  · intro htr
    by_cases ht0 : t = ∅
    · subst t
      exact empty_mem_orderedConfigurationBaseEdges k r
    · have ht : t.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr ht0
      rw [orderedConfigurationBaseEdges,
        Finset.mem_insert]
      right
      apply Finset.mem_image.mpr
      refine
        ⟨positiveOrderedFaceOfEdge t ht htr,
          Finset.mem_univ _, ?_⟩
      exact positiveOrderedFaceEdge_ofEdge t ht htr

noncomputable def orderedConfigurationInitialBundle
    (k r : ℕ) :
    HypergraphBundle (Fin k) (Fin k)
      (orderedConfigurationBaseEdges k r) where
  edges := orderedConfigurationBaseEdges k r
  projection := id
  projection_injective_on_edge := by
    intro g hg x hx y hy hxy
    exact hxy
  projection_mem_base := by
    intro g hg
    simpa using hg

@[simp]
theorem orderedConfigurationInitialBundle_edges
    (k r : ℕ) :
    (orderedConfigurationInitialBundle k r).edges =
      orderedConfigurationBaseEdges k r :=
  rfl

@[simp]
theorem orderedConfigurationInitialBundle_projection
    (k r : ℕ) :
    (orderedConfigurationInitialBundle k r).projection =
      id :=
  rfl

theorem orderedConfigurationInitialBundle_closed
    (k r : ℕ) :
    (orderedConfigurationInitialBundle k r).IsClosedUnderInclusion := by
  intro g hg f hfg
  rw [orderedConfigurationInitialBundle_edges] at hg ⊢
  rw [mem_orderedConfigurationBaseEdges_iff] at hg ⊢
  exact (Finset.card_le_card hfg).trans hg

noncomputable def orderedConfigurationEdgeTuple
    {G : Type*} {k r : ℕ}
    (t : Finset (Fin k))
    (ht : t.Nonempty) (htr : t.card ≤ r)
    (y : {v : Fin k // v ∈ t} → G) :
    Fin ((positiveOrderedFaceOfEdge t ht htr).lowerRank.1 + 1) → G := by
  let e := positiveOrderedFaceOfEdge t ht htr
  have hcard : t.card = e.lowerRank.1 + 1 := by
    dsimp [e, positiveOrderedFaceOfEdge]
    have htcard : 0 < t.card :=
      Finset.card_pos.mpr ht
    omega
  exact fun i => y (t.orderIsoOfFin hcard i)

@[simp]
theorem positiveOrderedFaceEdge_orderIsoOfFin_val
    {k r : ℕ} (e : PositiveOrderedFace k r)
    (i : Fin (e.lowerRank.1 + 1)) :
    ((positiveOrderedFaceEdge e).orderIsoOfFin
        (by
          simp [PositiveOrderedFace.rank]) i).1 =
      e.face i := by
  rw [Finset.coe_orderIsoOfFin_apply]
  have hcanonical :
      e.face =
        (positiveOrderedFaceEdge e).orderEmbOfFin
          (by
            simp [PositiveOrderedFace.rank]) := by
    apply Finset.orderEmbOfFin_unique'
    intro q
    simp [positiveOrderedFaceEdge]
  exact congrArg (fun f => f i) hcanonical.symm

noncomputable def orderedConfigurationBaseWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C) :
    HypergraphBundle.BaseEdgeWeight (Fin k) G := by
  classical
  intro t y
  by_cases ht : t.Nonempty
  · by_cases htr : t.card ≤ r
    · exact configurationFaceWeight A
        (positiveOrderedFaceOfEdge t ht htr)
        (orderedConfigurationEdgeTuple t ht htr y)
    · exact 1
  · exact 1

@[simp]
theorem orderedConfigurationBaseWeight_empty
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (y : {v : Fin k // v ∈ (∅ : Finset (Fin k))} → G) :
    orderedConfigurationBaseWeight A ∅ y = 1 := by
  simp [orderedConfigurationBaseWeight]

@[simp]
theorem orderedConfigurationBaseWeight_positiveOrderedFaceEdge
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (e : PositiveOrderedFace k r)
    (y :
      {v : Fin k // v ∈ positiveOrderedFaceEdge e} → G) :
    orderedConfigurationBaseWeight A
        (positiveOrderedFaceEdge e) y =
      configurationFaceWeight A e
        (fun i =>
          y ⟨e.face i,
            (mem_positiveOrderedFaceEdge e
              (e.face i)).2 ⟨i, rfl⟩⟩) := by
  classical
  simp only [orderedConfigurationBaseWeight,
    dite_eq_left (positiveOrderedFaceEdge_nonempty e),
    dite_eq_left (positiveOrderedFaceEdge_card_le e)]
  change
    (fun p :
        (Σ f : PositiveOrderedFace k r,
          Fin (f.lowerRank.1 + 1) → G) =>
      configurationFaceWeight A p.1 p.2)
        ⟨positiveOrderedFaceOfEdge
            (positiveOrderedFaceEdge e)
            (positiveOrderedFaceEdge_nonempty e)
            (positiveOrderedFaceEdge_card_le e),
          orderedConfigurationEdgeTuple
            (positiveOrderedFaceEdge e)
            (positiveOrderedFaceEdge_nonempty e)
            (positiveOrderedFaceEdge_card_le e) y⟩ =
      (fun p :
          (Σ f : PositiveOrderedFace k r,
            Fin (f.lowerRank.1 + 1) → G) =>
        configurationFaceWeight A p.1 p.2)
          ⟨e, fun i =>
            y ⟨e.face i,
              (mem_positiveOrderedFaceEdge e
                (e.face i)).2 ⟨i, rfl⟩⟩⟩
  apply congrArg
    (fun p :
        (Σ f : PositiveOrderedFace k r,
          Fin (f.lowerRank.1 + 1) → G) =>
      configurationFaceWeight A p.1 p.2)
  have he :
      positiveOrderedFaceOfEdge
          (positiveOrderedFaceEdge e)
          (positiveOrderedFaceEdge_nonempty e)
          (positiveOrderedFaceEdge_card_le e) = e :=
    positiveOrderedFaceOfEdge_edge e
  apply Sigma.ext he
  simp only
  apply Function.hfunext
    (congrArg
      (fun f : PositiveOrderedFace k r =>
        Fin (f.lowerRank.1 + 1)) he)
  intro i i' hii
  apply heq_of_eq
  unfold orderedConfigurationEdgeTuple
  apply congrArg y
  apply Subtype.ext
  have hn :
      (positiveOrderedFaceOfEdge
          (positiveOrderedFaceEdge e)
          (positiveOrderedFaceEdge_nonempty e)
          (positiveOrderedFaceEdge_card_le e)).lowerRank.1 + 1 =
        e.lowerRank.1 + 1 :=
    congrArg (fun f : PositiveOrderedFace k r =>
      f.lowerRank.1 + 1) he
  have hval : i.1 = i'.1 := by
    have hcast :
        cast (congrArg Fin hn) i = i' := by
      exact eq_of_heq
        ((cast_heq (congrArg Fin hn) i).trans hii)
    calc
      i.1 = (cast (congrArg Fin hn) i).1 := by
        symm
        have hcastVal :
            ∀ {m n : ℕ} (h : m = n) (a : Fin m),
              (cast (congrArg Fin h) a).1 = a.1 := by
          intro m n h a
          cases h
          rfl
        exact hcastVal hn i
      _ = i'.1 := congrArg Fin.val hcast
  rw [Finset.coe_orderIsoOfFin_apply]
  calc
    (positiveOrderedFaceEdge e).orderEmbOfFin _ i =
        (positiveOrderedFaceEdge e).orderEmbOfFin _ i' :=
      Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr hval
    _ = e.face i' := by
      simpa only [Finset.coe_orderIsoOfFin_apply] using
        positiveOrderedFaceEdge_orderIsoOfFin_val e i'

theorem orderedConfigurationBaseWeight_unitInterval
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C) :
    HypergraphBundle.BaseWeightsInUnitInterval
      (orderedConfigurationBaseEdges k r)
      (orderedConfigurationBaseWeight A) := by
  intro t ht y
  unfold orderedConfigurationBaseWeight
  by_cases ht0 : t.Nonempty
  · simp only [dite_eq_left ht0]
    by_cases htr : t.card ≤ r
    · simp only [dite_eq_left htr]
      exact
        ⟨configurationFaceWeight_nonneg A _ _,
          configurationFaceWeight_le_one A _ _⟩
    · simp [htr]
  · simp [ht0]

theorem orderedConfigurationBaseWeight_idempotent
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C) :
    HypergraphBundle.BaseWeightsIdempotent
      (orderedConfigurationBaseEdges k r)
      (orderedConfigurationBaseWeight A) := by
  intro t ht y
  unfold orderedConfigurationBaseWeight
  by_cases ht0 : t.Nonempty
  · simp only [dite_eq_left ht0]
    by_cases htr : t.card ≤ r
    · simp only [dite_eq_left htr]
      simpa [configurationFaceWeight, pow_two] using
        (partitionAtomIndicator_sq
          (C.partition
            (positiveOrderedFaceOfEdge t ht0 htr).lowerRank.succ
            (positiveOrderedFaceOfEdge t ht0 htr).face)
          (A.atom
            (positiveOrderedFaceOfEdge t ht0 htr).lowerRank.succ
            (positiveOrderedFaceOfEdge t ht0 htr).face)
          (orderedConfigurationEdgeTuple t ht0 htr y))
    · simp [htr]
  · simp [ht0]

noncomputable def orderedConfigurationBaseDensity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse) :
    Finset (Fin k) → ℝ := by
  classical
  intro t
  by_cases ht : t.Nonempty
  · by_cases htr : t.card ≤ r
    · exact mixedConfigurationCoarseDensity P A
        (positiveOrderedFaceOfEdge t ht htr)
    · exact 1
  · exact 1

@[simp]
theorem orderedConfigurationBaseDensity_empty
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse) :
    orderedConfigurationBaseDensity P A ∅ = 1 := by
  simp [orderedConfigurationBaseDensity]

@[simp]
theorem orderedConfigurationBaseDensity_positiveOrderedFaceEdge
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r) :
    orderedConfigurationBaseDensity P A
        (positiveOrderedFaceEdge e) =
      mixedConfigurationCoarseDensity P A e := by
  classical
  unfold orderedConfigurationBaseDensity
  simp only [dite_eq_left (positiveOrderedFaceEdge_nonempty e)]
  have hcard :
      (positiveOrderedFaceEdge e).card ≤ r := by
    simpa [positiveOrderedFaceEdge_card] using
      positiveOrderedFaceEdge_card_le e
  simp only [dite_eq_left hcard]
  exact congrArg (mixedConfigurationCoarseDensity P A)
    (positiveOrderedFaceOfEdge_edge e)

theorem orderedConfigurationBaseDensity_unitInterval
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse) :
    ∀ t ∈ orderedConfigurationBaseEdges k r,
      0 ≤ orderedConfigurationBaseDensity P A t ∧
        orderedConfigurationBaseDensity P A t ≤ 1 := by
  intro t ht
  unfold orderedConfigurationBaseDensity
  by_cases ht0 : t.Nonempty
  · simp only [dite_eq_left ht0]
    by_cases htr : t.card ≤ r
    · simp only [dite_eq_left htr]
      exact
        ⟨mixedConfigurationCoarseDensity_nonneg P A _,
          mixedConfigurationCoarseDensity_le_one P A _⟩
    · simp [htr]
  · simp [ht0]

theorem orderedConfigurationInitialBundle_projectedEdgeTuple
    {G : Type*} {k r : ℕ}
    {g : Finset (Fin k)}
    (hg :
      g ∈ (orderedConfigurationInitialBundle k r).edges)
    (x : Fin k → G) :
    (orderedConfigurationInitialBundle k r).projectedEdgeTuple hg
          (HypergraphBundle.edgeTuple g x) =
      fun j => x j.1 := by
  funext j
  have hj :
      (((orderedConfigurationInitialBundle k r).projectionEquiv hg).symm j).1 =
        j.1 := by
    have happly :=
      congrArg Subtype.val
        (((orderedConfigurationInitialBundle k r).projectionEquiv hg).apply_symm_apply j)
    change
      (orderedConfigurationInitialBundle k r).projection
          (((orderedConfigurationInitialBundle k r).projectionEquiv hg).symm j).1 =
        j.1 at happly
    change
      (((orderedConfigurationInitialBundle k r).projectionEquiv hg).symm j).1 =
        j.1 at happly
    exact happly
  unfold HypergraphBundle.projectedEdgeTuple
    HypergraphBundle.edgeTuple
  exact congrArg x hj

theorem orderedConfigurationInitialBundle_pullback_empty
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (x : Fin k → G) :
    (orderedConfigurationInitialBundle k r).pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A) ∅
          (HypergraphBundle.edgeTuple ∅ x) = 1 := by
  rw [(orderedConfigurationInitialBundle k r).pullbackBaseEdgeWeight_of_mem
      (orderedConfigurationBaseWeight A)
      (empty_mem_orderedConfigurationBaseEdges k r)]
  exact orderedConfigurationBaseWeight_empty A _

theorem orderedConfigurationInitialBundle_pullback_positiveOrderedFaceEdge
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (e : PositiveOrderedFace k r)
    (x : Fin k → G) :
    (orderedConfigurationInitialBundle k r).pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A)
          (positiveOrderedFaceEdge e)
          (HypergraphBundle.edgeTuple
            (positiveOrderedFaceEdge e) x) =
      configurationFaceWeight A e
        (orderedFaceTuple e.face x) := by
  have hedge :
      positiveOrderedFaceEdge e ∈
        (orderedConfigurationInitialBundle k r).edges := by
    rw [orderedConfigurationInitialBundle_edges,
      mem_orderedConfigurationBaseEdges_iff]
    exact positiveOrderedFaceEdge_card_le e
  rw [(orderedConfigurationInitialBundle k r).pullbackBaseEdgeWeight_of_mem
    (orderedConfigurationBaseWeight A) hedge]
  have himage :
      (positiveOrderedFaceEdge e).image
          (orderedConfigurationInitialBundle k r).projection =
        positiveOrderedFaceEdge e := by
    simpa only [orderedConfigurationInitialBundle_projection] using
      (Finset.image_id :
        (positiveOrderedFaceEdge e).image id =
          positiveOrderedFaceEdge e)
  have hpair :
      (⟨(positiveOrderedFaceEdge e).image
            (orderedConfigurationInitialBundle k r).projection,
          (orderedConfigurationInitialBundle k r).projectedEdgeTuple
            hedge
            (HypergraphBundle.edgeTuple
              (positiveOrderedFaceEdge e) x)⟩ :
        Σ t : Finset (Fin k), ({j : Fin k // j ∈ t} → G)) =
      ⟨positiveOrderedFaceEdge e,
        HypergraphBundle.edgeTuple
          (positiveOrderedFaceEdge e) x⟩ := by
    apply Sigma.ext himage
    simp only
    apply Function.hfunext
      (congrArg
        (fun t : Finset (Fin k) =>
          {j : Fin k // j ∈ t}) himage)
    intro j j' hjj
    apply heq_of_eq
    rw [congrFun
      (orderedConfigurationInitialBundle_projectedEdgeTuple
        hedge x) j]
    apply congrArg x
    exact
      (Subtype.heq_iff_coe_eq
        (fun v : Fin k => by
          rw [himage])).1 hjj
  have hweight :=
    congrArg
      (fun p :
          (Σ t : Finset (Fin k),
            ({j : Fin k // j ∈ t} → G)) =>
        orderedConfigurationBaseWeight A p.1 p.2)
      hpair
  rw [hweight]
  rw [orderedConfigurationBaseWeight_positiveOrderedFaceEdge]
  apply congrArg (configurationFaceWeight A e)
  funext i
  rfl

theorem orderedConfigurationInitialBundle_bundleProduct
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (x : Fin k → G) :
    (orderedConfigurationInitialBundle k r).bundleProduct
        ((orderedConfigurationInitialBundle k r).pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A)) x =
      partialConfigurationWeight A Finset.univ x := by
  classical
  change
    (∏ g ∈ (orderedConfigurationInitialBundle k r).edges,
      (orderedConfigurationInitialBundle k r).pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A) g
          (HypergraphBundle.edgeTuple g x)) =
      partialConfigurationWeight A Finset.univ x
  rw [orderedConfigurationInitialBundle_edges]
  change
    (∏ g ∈ insert ∅
        (Finset.univ.image
          (positiveOrderedFaceEdge :
            PositiveOrderedFace k r → Finset (Fin k))),
      (orderedConfigurationInitialBundle k r).pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A) g
          (HypergraphBundle.edgeTuple g x)) =
      partialConfigurationWeight A Finset.univ x
  rw [
    Finset.prod_insert
      (empty_not_mem_positiveOrderedFaceEdge_image k r)]
  rw [orderedConfigurationInitialBundle_pullback_empty]
  simp only [one_mul]
  rw [Finset.prod_image
    positiveOrderedFaceEdge_injective.injOn]
  unfold partialConfigurationWeight
  apply Finset.prod_congr rfl
  intro e he
  exact
    orderedConfigurationInitialBundle_pullback_positiveOrderedFaceEdge
      A e x

theorem orderedConfigurationInitialBundle_bundleCount
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C) :
    (orderedConfigurationInitialBundle k r).bundleCount
        ((orderedConfigurationInitialBundle k r).pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A)) =
      fullConfigurationCount A := by
  unfold HypergraphBundle.bundleCount
    fullConfigurationCount partialConfigurationCount
  apply congrArg mean
  funext x
  exact orderedConfigurationInitialBundle_bundleProduct A x

theorem orderedConfigurationInitialBundle_bundleMainProduct
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse) :
    (orderedConfigurationInitialBundle k r).bundleMainProduct
          (orderedConfigurationBaseDensity P A) =
      ∏ e : PositiveOrderedFace k r,
        mixedConfigurationCoarseDensity P A e := by
  classical
  change
    (∏ g ∈ (orderedConfigurationInitialBundle k r).edges,
      orderedConfigurationBaseDensity P A
        (g.image
          (orderedConfigurationInitialBundle k r).projection)) =
      ∏ e : PositiveOrderedFace k r,
        mixedConfigurationCoarseDensity P A e
  rw [orderedConfigurationInitialBundle_edges,
    orderedConfigurationInitialBundle_projection]
  simp only [Function.id_def, Finset.image_id']
  change
    (∏ g ∈ insert ∅
        (Finset.univ.image
          (positiveOrderedFaceEdge :
            PositiveOrderedFace k r → Finset (Fin k))),
      orderedConfigurationBaseDensity P A g) =
      ∏ e : PositiveOrderedFace k r,
        mixedConfigurationCoarseDensity P A e
  rw [
    Finset.prod_insert
      (empty_not_mem_positiveOrderedFaceEdge_image k r),
    orderedConfigurationBaseDensity_empty,
    one_mul]
  rw [Finset.prod_image
    positiveOrderedFaceEdge_injective.injOn]
  simp

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace HypergraphBundle

variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}

theorem projectedEdge_nonempty
    {K : Type*} [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (_hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    (g.image B.projection).Nonempty := by
  exact Finset.image_nonempty.mpr hne

theorem projectedEdge_card_le
    {K : Type*} [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges) :
    (g.image B.projection).card ≤ r := by
  exact
    (mem_orderedConfigurationBaseEdges_iff
      (g.image B.projection)).1
      (B.projection_mem_base g hg)

noncomputable def orderedConfigurationBundleFace
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    PositiveOrderedFace k r :=
  positiveOrderedFaceOfEdge
    (g.image B.projection)
    (B.projectedEdge_nonempty hg hne)
    (B.projectedEdge_card_le hg)

noncomputable def orderedConfigurationBundleFaceTuple
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) :
    Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) → G :=
  orderedConfigurationEdgeTuple
    (g.image B.projection)
    (B.projectedEdge_nonempty hg hne)
    (B.projectedEdge_card_le hg)
    (B.projectedEdgeTuple hg y)

noncomputable def orderedConfigurationBundleDefect
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) : ℝ :=
  mixedConfigurationDefect P A
    (B.orderedConfigurationBundleFace hg hne)
    (B.orderedConfigurationBundleFaceTuple hg hne y)

noncomputable def orderedConfigurationBundleUniform
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) : ℝ :=
  mixedConfigurationUniform P A
    (B.orderedConfigurationBundleFace hg hne)
    (B.orderedConfigurationBundleFaceTuple hg hne y)

theorem orderedConfigurationBaseDensity_projectedEdge
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    orderedConfigurationBaseDensity P A
        (g.image B.projection) =
      mixedConfigurationCoarseDensity P A
        (B.orderedConfigurationBundleFace hg hne) := by
  unfold orderedConfigurationBaseDensity
  simp only [
    dite_eq_left (B.projectedEdge_nonempty hg hne),
    dite_eq_left (B.projectedEdge_card_le hg)]
  rfl

theorem pullback_orderedConfigurationBaseWeight_decompose
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) :
    B.pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A) g y =
      orderedConfigurationBaseDensity P A
          (g.image B.projection) +
        B.orderedConfigurationBundleDefect P A hg hne y +
        B.orderedConfigurationBundleUniform P A hg hne y := by
  rw [B.pullbackBaseEdgeWeight_of_mem
    (orderedConfigurationBaseWeight A) hg y]
  rw [B.orderedConfigurationBaseDensity_projectedEdge
    P A hg hne]
  unfold orderedConfigurationBaseWeight
  simp only [
    dite_eq_left (B.projectedEdge_nonempty hg hne),
    dite_eq_left (B.projectedEdge_card_le hg)]
  exact
    mixedConfigurationFaceWeight_decompose P A
      (B.orderedConfigurationBundleFace hg hne)
      (B.orderedConfigurationBundleFaceTuple hg hne y)

noncomputable def orderedConfigurationBundleLocalizedDefect
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) : ℝ :=
  B.orderedConfigurationBundleDefect P A hg hne y *
    B.strictBoundaryLocalProduct g
      (B.pullbackBaseEdgeWeight
        (orderedConfigurationBaseWeight A)) y

def HasOrderedConfigurationBundleLocalizedDefect
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (β : ℕ → ℝ) : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r)),
    B.IsClosedUnderInclusion →
    ∀ {g₀ : Finset K}, (hg₀ : g₀ ∈ B.edges) →
      (∀ g ∈ B.edges, g.card ≤ g₀.card) →
      (hne : g₀.Nonempty) →
      mean (fun y =>
        B.orderedConfigurationBundleLocalizedDefect
            P A hg₀ hne y ^ 2) ≤
        β g₀.card *
          (B.strictBoundary g₀).bundleCount
            ((B.strictBoundary g₀).pullbackBaseEdgeWeight
              (orderedConfigurationBaseWeight A))

def HasOrderedConfigurationBundleFrozenUniformity
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (τ : ℝ) : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r)),
    B.IsClosedUnderInclusion →
    ∀ {g₀ : Finset K}, (hg₀ : g₀ ∈ B.edges) →
      (∀ g ∈ B.edges, g.card ≤ g₀.card) →
      (hne : g₀.Nonempty) →
      ∀ z : EdgeComplement g₀ → G,
        |B.frozenEdgeCorrelation g₀
            (B.orderedConfigurationBundleUniform
              P A hg₀ hne)
            (B.pullbackBaseEdgeWeight
              (orderedConfigurationBaseWeight A)) z| ≤
          τ

theorem hasTaoBundleCountingStep_orderedConfiguration
    [Nonempty G]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (β : ℕ → ℝ) (τ : ℝ)
    (hβ : ∀ d, 0 ≤ β d)
    (hτ : 0 ≤ τ)
    (hlocalized :
      HasOrderedConfigurationBundleLocalizedDefect P A β)
    (hfrozen :
      HasOrderedConfigurationBundleFrozenUniformity P A τ) :
    HasTaoBundleCountingStep
      (H := orderedConfigurationBaseEdges k r)
      (orderedConfigurationBaseWeight A)
      (orderedConfigurationBaseDensity P A)
      β τ := by
  intro K _instK _decK B hclosed g₀ hg₀ hmax
  by_cases hne : g₀.Nonempty
  · let W :=
      B.pullbackBaseEdgeWeight
        (orderedConfigurationBaseWeight A)
    let p :=
      orderedConfigurationBaseDensity P A
        (g₀.image B.projection)
    let b :=
      B.orderedConfigurationBundleDefect
        P A hg₀ hne
    let c :=
      B.orderedConfigurationBundleUniform
        P A hg₀ hne
    let bLocalized :=
      B.orderedConfigurationBundleLocalizedDefect
        P A hg₀ hne
    have hdecomp :
        ∀ y, W g₀ y = p + b y + c y := by
      intro y
      simpa only [W, p, b, c] using
        B.pullback_orderedConfigurationBaseWeight_decompose
          P A hg₀ hne y
    have hcount :
        B.bundleCount W =
          p * (B.eraseEdge g₀).bundleCount W +
            B.edgeContribution g₀ b W +
            B.edgeContribution g₀ c W :=
      B.bundleCount_decompose_edge
        W hg₀ p b c hdecomp
    have herase :
        (B.eraseEdge g₀).bundleCount W =
          (B.eraseEdge g₀).bundleCount
            ((B.eraseEdge g₀).pullbackBaseEdgeWeight
              (orderedConfigurationBaseWeight A)) := by
      exact
        B.eraseEdge_bundleCount_pullback g₀
          (orderedConfigurationBaseWeight A)
    have hIdempotent :
        B.WeightsIdempotent W := by
      exact B.pullbackBaseEdgeWeight_weightsIdempotent
        (orderedConfigurationBaseWeight A)
        (orderedConfigurationBaseWeight_idempotent A)
    have hlocalizeContribution :
        B.edgeContribution g₀ b W =
          B.edgeContribution g₀ bLocalized W := by
      change B.edgeContribution g₀ b W =
        B.edgeContribution g₀
          (fun y =>
            b y * B.strictBoundaryLocalProduct g₀ W y) W
      exact B.edgeContribution_mul_strictBoundaryLocalProduct
        g₀ b W hIdempotent
    have hdefect :
        |B.edgeContribution g₀ b W| ≤
          Real.sqrt
            ((β g₀.card *
                (B.strictBoundary g₀).bundleCount
                  ((B.strictBoundary g₀).pullbackBaseEdgeWeight
                      (orderedConfigurationBaseWeight A))) *
              ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount
                  (((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight
                      (orderedConfigurationBaseWeight A))) := by
      rw [hlocalizeContribution]
      exact
        B.abs_edgeContribution_pullback_le_sqrt_boundary_mul_lowerOrder
          hclosed hg₀ hmax
          (orderedConfigurationBaseWeight A)
          (orderedConfigurationBaseWeight_unitInterval A)
          (orderedConfigurationBaseWeight_idempotent A)
          bLocalized (hβ g₀.card)
          (hlocalized K B hclosed hg₀ hmax hne)
    have huniform :
        |B.edgeContribution g₀ c W| ≤ τ := by
      exact B.abs_edgeContribution_le_of_frozen
        g₀ c W
        (hfrozen K B hclosed hg₀ hmax hne)
    rw [hcount, herase]
    calc
      |p *
              (B.eraseEdge g₀).bundleCount
                ((B.eraseEdge g₀).pullbackBaseEdgeWeight
                  (orderedConfigurationBaseWeight A)) +
            B.edgeContribution g₀ b W +
            B.edgeContribution g₀ c W -
          p *
              (B.eraseEdge g₀).bundleCount
                ((B.eraseEdge g₀).pullbackBaseEdgeWeight
                  (orderedConfigurationBaseWeight A))| =
          |B.edgeContribution g₀ b W +
            B.edgeContribution g₀ c W| := by
        congr 1
        ring
      _ ≤
          |B.edgeContribution g₀ b W| +
            |B.edgeContribution g₀ c W| :=
        abs_add_le _ _
      _ ≤
          Real.sqrt
              ((β g₀.card *
                  (B.strictBoundary g₀).bundleCount
                    ((B.strictBoundary g₀).pullbackBaseEdgeWeight
                        (orderedConfigurationBaseWeight A))) *
                ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount
                    (((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight
                        (orderedConfigurationBaseWeight A))) +
            τ :=
        add_le_add hdefect huniform
  · have hg₀empty : g₀ = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    subst g₀
    let W :=
      B.pullbackBaseEdgeWeight
        (orderedConfigurationBaseWeight A)
    have hweight :
        ∀ y, W ∅ y = 1 := by
      intro y
      dsimp only [W]
      rw [B.pullbackBaseEdgeWeight_of_mem
        (orderedConfigurationBaseWeight A) hg₀ y]
      simp only [Finset.image_empty]
      exact orderedConfigurationBaseWeight_empty A
        (B.projectedEdgeTuple hg₀ y)
    have hcount :
        B.bundleCount W =
          (B.eraseEdge ∅).bundleCount
            ((B.eraseEdge ∅).pullbackBaseEdgeWeight
              (orderedConfigurationBaseWeight A)) := by
      calc
        B.bundleCount W =
            B.edgeContribution ∅ (W ∅) W :=
          B.bundleCount_eq_edgeContribution W hg₀
        _ =
            B.edgeContribution ∅ (fun _ => 1) W := by
          apply congrArg
            (fun q => B.edgeContribution ∅ q W)
          funext y
          exact hweight y
        _ = (B.eraseEdge ∅).bundleCount W := by
          rw [B.edgeContribution_const]
          simp
        _ =
            (B.eraseEdge ∅).bundleCount
              ((B.eraseEdge ∅).pullbackBaseEdgeWeight
                (orderedConfigurationBaseWeight A)) :=
          B.eraseEdge_bundleCount_pullback ∅
            (orderedConfigurationBaseWeight A)
    rw [hcount, Finset.image_empty,
      orderedConfigurationBaseDensity_empty,
      one_mul, sub_self, abs_zero]
    exact add_nonneg (Real.sqrt_nonneg _) hτ

end HypergraphBundle

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace HypergraphBundle

variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}

theorem exists_selectedVertex_not_mem_of_mem_erase
    {J K : Type*} [DecidableEq J] [DecidableEq K]
    {H : Finset (Finset J)}
    (B : HypergraphBundle J K H)
    {g₀ g : Finset K}
    (hg : g ∈ B.edges.erase g₀)
    (hmax : ∀ f ∈ B.edges, f.card ≤ g₀.card) :
    ∃ v ∈ g₀, v ∉ g := by
  classical
  by_contra hmissing
  have hsubset : g₀ ⊆ g := by
    intro v hv
    by_contra hvg
    exact hmissing ⟨v, hv, hvg⟩
  have hgB : g ∈ B.edges :=
    Finset.mem_of_mem_erase hg
  have heq : g₀ = g :=
    Finset.eq_of_subset_of_card_le hsubset (hmax g hgB)
  exact (Finset.mem_erase.mp hg).1 heq.symm

noncomputable def orderedConfigurationBundleFaceState
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    FaceRegularityState
      (Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) →
        G) :=
  ⟨orderedBoundaryPartition
    (positiveFaceLowerLayer P.fine
      (B.orderedConfigurationBundleFace hg hne))
    (B.orderedConfigurationBundleFace hg hne).face⟩

noncomputable def orderedConfigurationBundleFaceTarget
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    (Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) →
      G) → ℝ :=
  partitionAtomIndicator
    (P.coarse.partition
      (B.orderedConfigurationBundleFace hg hne).lowerRank.succ
      (B.orderedConfigurationBundleFace hg hne).face)
    (A.atom
      (B.orderedConfigurationBundleFace hg hne).lowerRank.succ
      (B.orderedConfigurationBundleFace hg hne).face)

def HasOrderedConfigurationBundleFrozenCutRepresentation
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse) : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r)),
    B.IsClosedUnderInclusion →
    ∀ {g₀ : Finset K}, (hg₀ : g₀ ∈ B.edges) →
      (∀ g ∈ B.edges, g.card ≤ g₀.card) →
      (hne : g₀.Nonempty) →
      ∀ z : EdgeComplement g₀ → G,
        ∃ u :
            CutTestFamily G
              ((B.orderedConfigurationBundleFace
                hg₀ hne).lowerRank.1 + 1),
          IsBoundedCutTest u ∧
            B.frozenEdgeCorrelation g₀
                (B.orderedConfigurationBundleUniform
                  P A hg₀ hne)
                (B.pullbackBaseEdgeWeight
                  (orderedConfigurationBaseWeight A)) z =
              (B.orderedConfigurationBundleFaceState
                  P hg₀ hne).faceCutCorrelation
                (B.orderedConfigurationBundleFaceTarget
                  P A hg₀ hne)
                u

theorem hasOrderedConfigurationBundleFrozenUniformity_of_fullyMixed
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (τ : ℝ)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => τ))
    (hcut :
      HasOrderedConfigurationBundleFrozenCutRepresentation P A) :
    HasOrderedConfigurationBundleFrozenUniformity P A τ := by
  intro K _instK _decK B hclosed g₀ hg₀ hmax hne z
  obtain ⟨u, hu, hreindex⟩ :=
    hcut K B hclosed hg₀ hmax hne z
  rw [hreindex]
  exact
    mixedConfigurationFace_isFaceCutRegular
      P A (fun _ => τ) hregular
      (B.orderedConfigurationBundleFace hg₀ hne)
      u hu

structure IsSourceFullBundlePreliminaryOrderedRegular
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (τ : ℝ) : Prop where
  fullyMixed :
    IsFullyMixedPreliminaryOrderedRegular P (fun _ => τ)
  frozenCut :
    HasOrderedConfigurationBundleFrozenCutRepresentation P A

theorem IsSourceFullBundlePreliminaryOrderedRegular.frozenUniformity
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (τ : ℝ)
    (h : IsSourceFullBundlePreliminaryOrderedRegular P A τ) :
    HasOrderedConfigurationBundleFrozenUniformity P A τ :=
  hasOrderedConfigurationBundleFrozenUniformity_of_fullyMixed
    P A τ h.fullyMixed h.frozenCut

end HypergraphBundle

end Erdos3.FixedDensity

end

end OAI
