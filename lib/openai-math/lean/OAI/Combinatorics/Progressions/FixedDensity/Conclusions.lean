-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import OAI.Combinatorics.Progressions.FixedDensity.HypergraphBundleSourceGoodnessBridge
import OAI.Combinatorics.Progressions.FixedDensity.SourceFullBundleRemovalParameters
import OAI.Compat.Core
import OAI.Compat.BigOperators

namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace HypergraphBundle

variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}

noncomputable def frozenProjectedEdgeOrderIso
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) ≃
      {j : Fin k // j ∈ g.image B.projection} := by
  let t := g.image B.projection
  let e := B.orderedConfigurationBundleFace hg hne
  have hcard : t.card = e.lowerRank.1 + 1 := by
    have hedge :
        positiveOrderedFaceEdge e = t := by
      dsimp [e, orderedConfigurationBundleFace, t]
      exact positiveOrderedFaceEdge_ofEdge
        (g.image B.projection)
        (B.projectedEdge_nonempty hg hne)
        (B.projectedEdge_card_le hg)
    calc
      t.card = (positiveOrderedFaceEdge e).card :=
        congrArg Finset.card hedge.symm
      _ = e.rank := positiveOrderedFaceEdge_card e
      _ = e.lowerRank.1 + 1 := rfl
  exact (t.orderIsoOfFin hcard).toEquiv

noncomputable def frozenOccurrenceOrderEquiv
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) ≃
      {v : K // v ∈ g} :=
  (B.frozenProjectedEdgeOrderIso hg hne).trans
    (B.projectionEquiv hg).symm

noncomputable def frozenBundleFaceTupleEquiv
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    ({v : K // v ∈ g} → G) ≃
      (Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) →
        G) :=
  (Equiv.arrowCongr
      (B.projectionEquiv hg)
      (Equiv.refl G)).trans
    (Equiv.arrowCongr
      (B.frozenProjectedEdgeOrderIso hg hne).symm
      (Equiv.refl G))

omit [Fintype G] [DecidableEq G] in
@[simp]
theorem frozenBundleFaceTupleEquiv_apply
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) :
    B.frozenBundleFaceTupleEquiv hg hne y =
      B.orderedConfigurationBundleFaceTuple hg hne y := by
  funext i
  unfold frozenBundleFaceTupleEquiv frozenProjectedEdgeOrderIso
    orderedConfigurationBundleFaceTuple
    orderedConfigurationEdgeTuple
  rfl

omit [Fintype G] [DecidableEq G] in
@[simp]
theorem frozenBundleFaceTupleEquiv_symm_apply
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (x :
      Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) →
        G)
    (v : {v : K // v ∈ g}) :
    (B.frozenBundleFaceTupleEquiv hg hne).symm x v =
      x ((B.frozenOccurrenceOrderEquiv hg hne).symm v) := by
  rfl

noncomputable def frozenBundleMissingVertex
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ : Finset K}
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (g : Finset K) : {v : K // v ∈ g₀} :=
  if hg : g ∈ B.edges.erase g₀ then
    ⟨Classical.choose
        (B.exists_selectedVertex_not_mem_of_mem_erase hg hmax),
      (Classical.choose_spec
        (B.exists_selectedVertex_not_mem_of_mem_erase hg hmax)).1⟩
  else
    ⟨Classical.choose hne, Classical.choose_spec hne⟩

theorem frozenBundleMissingVertex_not_mem
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ g : Finset K}
    (hmax : ∀ f ∈ B.edges, f.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (hg : g ∈ B.edges.erase g₀) :
    (B.frozenBundleMissingVertex hmax hne g).1 ∉ g := by
  classical
  simp only [frozenBundleMissingVertex, dite_eq_left hg]
  exact
    (Classical.choose_spec
      (B.exists_selectedVertex_not_mem_of_mem_erase hg hmax)).2

noncomputable def frozenBundleMissingCoordinate
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (g : Finset K) :
    Fin ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1) :=
  (B.frozenOccurrenceOrderEquiv hg₀ hne).symm
    (B.frozenBundleMissingVertex hmax hne g)

theorem frozenOccurrenceOrder_missingCoordinate_not_mem
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ g : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ f ∈ B.edges, f.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (hg : g ∈ B.edges.erase g₀) :
    (B.frozenOccurrenceOrderEquiv hg₀ hne
      (B.frozenBundleMissingCoordinate hg₀ hmax hne g)).1 ∉ g := by
  unfold frozenBundleMissingCoordinate
  rw [(B.frozenOccurrenceOrderEquiv hg₀ hne).apply_symm_apply]
  exact B.frozenBundleMissingVertex_not_mem hmax hne hg

noncomputable def frozenBundleInsertedSelectedTuple
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hne : g₀.Nonempty)
    (i :
      Fin ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1))
    (a : G)
    (y :
      Fin (B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 → G) :
    {v : K // v ∈ g₀} → G :=
  (B.frozenBundleFaceTupleEquiv hg₀ hne).symm
    (Fin.insertNth i a y)

noncomputable def frozenBundleInsertedAssignment
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hne : g₀.Nonempty)
    (i :
      Fin ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1))
    (a : G)
    (y :
      Fin (B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 → G)
    (z : EdgeComplement g₀ → G) : K → G :=
  (splitEdgeEquiv g₀).symm
    (B.frozenBundleInsertedSelectedTuple hg₀ hne i a y, z)

omit [Fintype G] [DecidableEq G] in
theorem splitEdgeEquiv_symm_apply_of_mem
    {K : Type*} [DecidableEq K]
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : EdgeComplement g₀ → G)
    {v : K} (hv : v ∈ g₀) :
    (splitEdgeEquiv g₀).symm (y, z) v = y ⟨v, hv⟩ := by
  have h :=
    congrFun (edgeTuple_splitEdgeEquiv_symm g₀ y z) ⟨v, hv⟩
  exact h

omit [Fintype G] [DecidableEq G] in
theorem splitEdgeEquiv_symm_apply_of_not_mem
    {K : Type*} [DecidableEq K]
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : EdgeComplement g₀ → G)
    {v : K} (hv : v ∉ g₀) :
    (splitEdgeEquiv g₀).symm (y, z) v = z ⟨v, hv⟩ := by
  unfold splitEdgeEquiv
  convert
    Equiv.piCongrLeft_sumInr
      (fun _ : K => G) (edgeSumEquiv g₀)
      y z ⟨v, hv⟩ using 1 ;
    simp [edgeSumEquiv]

omit [Fintype G] [DecidableEq G] in

theorem edgeTuple_frozenBundleInsertedAssignment
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ g : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ f ∈ B.edges, f.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (hg : g ∈ B.edges.erase g₀)
    (a : G)
    (x :
      Fin ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1) →
        G)
    (z : EdgeComplement g₀ → G) :
    edgeTuple g
        (B.frozenBundleInsertedAssignment hg₀ hne
          (B.frozenBundleMissingCoordinate hg₀ hmax hne g)
          a
          (Fin.removeNth
            (B.frozenBundleMissingCoordinate hg₀ hmax hne g) x)
          z) =
      edgeTuple g
        ((splitEdgeEquiv g₀).symm
          ((B.frozenBundleFaceTupleEquiv hg₀ hne).symm x, z)) := by
  classical
  funext w
  unfold edgeTuple
  let i :=
    B.frozenBundleMissingCoordinate hg₀ hmax hne g
  by_cases hw₀ : w.1 ∈ g₀
  · unfold frozenBundleInsertedAssignment
    rw [splitEdgeEquiv_symm_apply_of_mem g₀ _ _ hw₀]
    rw [splitEdgeEquiv_symm_apply_of_mem g₀ _ _ hw₀]
    unfold frozenBundleInsertedSelectedTuple
    rw [B.frozenBundleFaceTupleEquiv_symm_apply]
    rw [B.frozenBundleFaceTupleEquiv_symm_apply]
    let q :=
      (B.frozenOccurrenceOrderEquiv hg₀ hne).symm
        (⟨w.1, hw₀⟩ : {v : K // v ∈ g₀})
    have hqi : q ≠ i := by
      intro h
      have hsub :
          (⟨w.1, hw₀⟩ : {v : K // v ∈ g₀}) =
            B.frozenBundleMissingVertex hmax hne g := by
        apply (B.frozenOccurrenceOrderEquiv hg₀ hne).symm.injective
        simpa only [q, i, frozenBundleMissingCoordinate] using h
      apply B.frozenBundleMissingVertex_not_mem hmax hne hg
      have hwval :
          w.1 =
            (B.frozenBundleMissingVertex hmax hne g).1 :=
        congrArg Subtype.val hsub
      rw [← hwval]
      exact w.2
    change
      Fin.insertNth i a (Fin.removeNth i x) q = x q
    rw [Fin.insertNth_removeNth]
    simp [hqi]
  · unfold frozenBundleInsertedAssignment
    rw [splitEdgeEquiv_symm_apply_of_not_mem g₀ _ _ hw₀]
    rw [splitEdgeEquiv_symm_apply_of_not_mem g₀ _ _ hw₀]

noncomputable def frozenBundleRemainderCutTest
    {K : Type*} [Fintype K] [DecidableEq K]
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (a : G)
    (z : EdgeComplement g₀ → G) :
    CutTestFamily G
      ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1) :=
  fun i y =>
    ∏ g ∈ B.edges.erase g₀,
      if _hcoord :
          B.frozenBundleMissingCoordinate hg₀ hmax hne g = i
      then
        B.pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A) g
          (edgeTuple g
            (B.frozenBundleInsertedAssignment hg₀ hne i a y z))
      else 1

theorem frozenBundleRemainderCutTest_bounded
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (a : G)
    (z : EdgeComplement g₀ → G) :
    IsBoundedCutTest
      (B.frozenBundleRemainderCutTest A hg₀ hmax hne a z) := by
  constructor
  · intro i y
    unfold frozenBundleRemainderCutTest
    apply Finset.prod_nonneg
    intro g hg
    split_ifs
    · exact
        (B.pullbackBaseEdgeWeight_unitInterval
          (orderedConfigurationBaseWeight A)
          (orderedConfigurationBaseWeight_unitInterval A)
          (Finset.mem_of_mem_erase hg) _).1
    · positivity
  · intro i y
    unfold frozenBundleRemainderCutTest
    apply Finset.prod_le_one₀
    · intro g hg
      split_ifs
      · exact
          (B.pullbackBaseEdgeWeight_unitInterval
            (orderedConfigurationBaseWeight A)
            (orderedConfigurationBaseWeight_unitInterval A)
            (Finset.mem_of_mem_erase hg) _).1
      · positivity
    · intro g hg
      split_ifs
      · exact
          (B.pullbackBaseEdgeWeight_unitInterval
            (orderedConfigurationBaseWeight A)
            (orderedConfigurationBaseWeight_unitInterval A)
            (Finset.mem_of_mem_erase hg) _).2
      · exact le_rfl

theorem cutTestProduct_frozenBundleRemainderCutTest
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (a : G)
    (z : EdgeComplement g₀ → G)
    (x :
      Fin ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1) →
        G) :
    cutTestProduct
        (B.frozenBundleRemainderCutTest A hg₀ hmax hne a z) x =
      B.edgeRemainderFiber g₀
        (B.pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A))
        ((B.frozenBundleFaceTupleEquiv hg₀ hne).symm x) z := by
  classical
  unfold cutTestProduct frozenBundleRemainderCutTest
  rw [Finset.prod_comm]
  unfold edgeRemainderFiber edgeRemainder bundleProduct
  apply Finset.prod_congr rfl
  intro g hg
  let i :=
    B.frozenBundleMissingCoordinate hg₀ hmax hne g
  calc
    (∏ q :
        Fin ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1),
        if hcoord :
            B.frozenBundleMissingCoordinate hg₀ hmax hne g = q
        then
          B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A) g
            (edgeTuple g
              (B.frozenBundleInsertedAssignment hg₀ hne q a
                (Fin.removeNth q x) z))
        else 1) =
        (if hcoord :
            B.frozenBundleMissingCoordinate hg₀ hmax hne g = i
        then
          B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A) g
            (edgeTuple g
            (B.frozenBundleInsertedAssignment hg₀ hne i a
                (Fin.removeNth i x) z))
        else 1) := by
      apply Fintype.prod_eq_single i
      intro q hqi
      have hnecoord :
          B.frozenBundleMissingCoordinate hg₀ hmax hne g ≠ q := by
        intro h
        exact hqi h.symm
      simp [hnecoord]
    _ =
        B.pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A) g
          (edgeTuple g
            (B.frozenBundleInsertedAssignment hg₀ hne i a
              (Fin.removeNth i x) z)) := by
      simp [i]
    _ =
        B.pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A) g
          (edgeTuple g
            ((splitEdgeEquiv g₀).symm
              ((B.frozenBundleFaceTupleEquiv hg₀ hne).symm x, z))) := by
      rw [B.edgeTuple_frozenBundleInsertedAssignment
        hg₀ hmax hne hg a x z]

theorem hasOrderedConfigurationBundleFrozenCutRepresentation
    [Nonempty G]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse) :
    HasOrderedConfigurationBundleFrozenCutRepresentation P A := by
  intro K _instK _decK B _hclosed g₀ hg₀ hmax hne z
  let a : G := Classical.choice inferInstance
  let u :=
    B.frozenBundleRemainderCutTest A hg₀ hmax hne a z
  refine ⟨u, ?_, ?_⟩
  · exact
      B.frozenBundleRemainderCutTest_bounded
        P A hg₀ hmax hne a z
  · unfold frozenEdgeCorrelation
    unfold FaceRegularityState.faceCutCorrelation
    apply mean_equiv
      (B.frozenBundleFaceTupleEquiv hg₀ hne)
    intro y
    rw [B.cutTestProduct_frozenBundleRemainderCutTest
      P A hg₀ hmax hne a z]
    simp only [Equiv.symm_apply_apply]
    rw [B.frozenBundleFaceTupleEquiv_apply]
    rfl

end HypergraphBundle

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem orderedConfigurationBaseDensity_ge_of_sourceFullMixedGood
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    {a t : ℝ} (ha_one : a ≤ 1)
    (hgood :
      A.IsSourceFullMixedGood P (fun _ => a) (fun _ => t ^ 2)) :
    ∀ e ∈ orderedConfigurationBaseEdges k r,
      a ≤ orderedConfigurationBaseDensity P A e := by
  intro e he
  by_cases he0 : e = ∅
  · subst e
    simpa using ha_one
  · have hene : e.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr he0
    have her : e.card ≤ r :=
      (mem_orderedConfigurationBaseEdges_iff e).1 he
    have hdensity :=
      (hgood (positiveOrderedFaceOfEdge e hene her)).1
    simpa [sourceFullMixedCoarseDensity,
      orderedConfigurationBaseDensity, hene, her] using hdensity

theorem hasTaoBundleCountingStep_orderedConfiguration_of_sourceFull
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    {a t : ℝ}
    (hgood :
      A.IsSourceFullMixedGood P (fun _ => a) (fun _ => t ^ 2))
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => t ^ 2)) :
    HasTaoBundleCountingStep
      (H := orderedConfigurationBaseEdges k r)
      (orderedConfigurationBaseWeight A)
      (orderedConfigurationBaseDensity P A)
      (fun _ => t ^ 2) (t ^ 2) := by
  apply HypergraphBundle.hasTaoBundleCountingStep_orderedConfiguration
      P A (fun _ => t ^ 2) (t ^ 2)
  · intro d
    exact sq_nonneg t
  · exact sq_nonneg t
  · exact
      HypergraphBundle.hasOrderedConfigurationBundleLocalizedDefect_of_sourceFullMixedGood
        P A (fun _ => a) (fun _ => t ^ 2) hgood
  · exact
      HypergraphBundle.hasOrderedConfigurationBundleFrozenUniformity_of_fullyMixed
        P A (t ^ 2) hregular
        (HypergraphBundle.hasOrderedConfigurationBundleFrozenCutRepresentation
          P A)

theorem abs_bundleCount_orderedConfiguration_sub_main_le_sourceFullEnvelope
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    {a t : ℝ} (ha : 0 < a) (ha_one : a ≤ 1)
    (hgood :
      A.IsSourceFullMixedGood P (fun _ => a) (fun _ => t ^ 2))
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => t ^ 2))
    {K : Type} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    (hclosed : B.IsClosedUnderInclusion) :
    |B.bundleCount
          (B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A)) -
        B.bundleMainProduct
          (orderedConfigurationBaseDensity P A)| ≤
      bundleCommonEnvelopeError a t B.order B.edges.card *
        B.bundleMainProduct
          (orderedConfigurationBaseDensity P A) := by
  have hstep :
      HasTaoBundleCountingStep
        (H := orderedConfigurationBaseEdges k r)
        (orderedConfigurationBaseWeight A)
        (orderedConfigurationBaseDensity P A)
        (fun _ => t ^ 2) (t ^ 2) :=
    hasTaoBundleCountingStep_orderedConfiguration_of_sourceFull
      P A hgood hregular
  have henvelope :
      IsBundleCountingEnvelope
        (fun _ => a) (fun _ => t ^ 2) (fun _ => a) (t ^ 2)
        (bundleCommonEnvelopeError a t) :=
    bundleCommonEnvelopeError_isEnvelope ha ha_one
  exact
    @abs_bundleCount_pullback_sub_bundleMainProduct_le_envelope
      (Fin k) G inferInstance inferInstance
      (orderedConfigurationBaseEdges k r) inferInstance
      (orderedConfigurationBaseWeight A)
      (orderedConfigurationBaseDensity P A)
      (fun _ => a) (fun _ => t ^ 2) (fun _ => a) (t ^ 2)
      (bundleCommonEnvelopeError a t)
      (orderedConfigurationBaseWeight_unitInterval A)
      (orderedConfigurationBaseWeight_idempotent A)
      (orderedConfigurationBaseWeight_empty A)
      (orderedConfigurationBaseDensity_empty P A)
      (orderedConfigurationBaseDensity_ge_of_sourceFullMixedGood
        P A ha_one hgood)
      hstep henvelope K inferInstance inferInstance B hclosed

theorem one_sub_sourceFullEnvelope_mul_densityProduct_le_fullConfigurationCount
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    {a t : ℝ} (ha : 0 < a) (ha_one : a ≤ 1)
    (hgood :
      A.IsSourceFullMixedGood P (fun _ => a) (fun _ => t ^ 2))
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => t ^ 2)) :
    (1 - bundleCommonEnvelopeError a t
          (orderedConfigurationInitialBundle k r).order
          (orderedConfigurationInitialBundle k r).edges.card) *
        (∏ e : PositiveOrderedFace k r,
          mixedConfigurationCoarseDensity P A e) ≤
      fullConfigurationCount A := by
  have hcount :=
    abs_bundleCount_orderedConfiguration_sub_main_le_sourceFullEnvelope
      P A ha ha_one hgood hregular
      (orderedConfigurationInitialBundle k r)
      (orderedConfigurationInitialBundle_closed k r)
  rw [orderedConfigurationInitialBundle_bundleCount A,
    orderedConfigurationInitialBundle_bundleMainProduct P A] at hcount
  have hlower :
      - (bundleCommonEnvelopeError a t
          (orderedConfigurationInitialBundle k r).order
          (orderedConfigurationInitialBundle k r).edges.card *
            (∏ e : PositiveOrderedFace k r,
              mixedConfigurationCoarseDensity P A e)) ≤
        fullConfigurationCount A -
          (∏ e : PositiveOrderedFace k r,
            mixedConfigurationCoarseDensity P A e) :=
    neg_le_of_abs_le hcount
  linarith

theorem fullConfigurationCount_pos_of_sourceFullEnvelope_lt_half
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    {a t : ℝ} (ha : 0 < a) (ha_one : a ≤ 1)
    (hgood :
      A.IsSourceFullMixedGood P (fun _ => a) (fun _ => t ^ 2))
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => t ^ 2))
    (herror :
      bundleCommonEnvelopeError a t
          (orderedConfigurationInitialBundle k r).order
          (orderedConfigurationInitialBundle k r).edges.card < 1 / 2) :
    0 < fullConfigurationCount A := by
  have hlower :=
    one_sub_sourceFullEnvelope_mul_densityProduct_le_fullConfigurationCount
      P A ha ha_one hgood hregular
  have hdensity :
      0 < ∏ e : PositiveOrderedFace k r,
        mixedConfigurationCoarseDensity P A e := by
    apply Finset.prod_pos
    intro e _he
    exact ha.trans_le (by
      simpa [sourceFullMixedCoarseDensity] using (hgood e).1)
  have hone :
      0 < 1 - bundleCommonEnvelopeError a t
          (orderedConfigurationInitialBundle k r).order
          (orderedConfigurationInitialBundle k r).edges.card := by
    linarith
  exact (mul_pos hone hdensity).trans_le hlower

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem orderedConfigurationInitialBundle_order_le
    (k r : ℕ) :
    (orderedConfigurationInitialBundle k r).order ≤ r := by
  unfold HypergraphBundle.order
  rw [orderedConfigurationInitialBundle_edges]
  apply Finset.sup_le
  intro e he
  exact (mem_orderedConfigurationBaseEdges_iff e).1 he

theorem SourceFullCoarseTargetSchedule.Certificate.isFullyMixedPreliminaryOrderedRegular_common
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (R : SourceFullCoarseTargetSchedule.Certificate
      k r initial initialBound F scaleFloor) :
    IsFullyMixedPreliminaryOrderedRegular
      R.regularity.toCoarseFine
      (fun _ => sourceFullCommonTolerance F R.scale) := by
  intro j e a b
  exact
    (R.regularity.mixedRegular j e a b).trans
      (R.selected_tolerance_le_common j)

theorem orderedConfigurationBaseDensity_ge_of_sourceFullMixedGood_rankwise
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (hαzero : α 0 ≤ 1)
    (hgood : A.IsSourceFullMixedGood P α β) :
    ∀ e ∈ orderedConfigurationBaseEdges k r,
      α e.card ≤ orderedConfigurationBaseDensity P A e := by
  intro e he
  by_cases he0 : e = ∅
  · subst e
    simpa using hαzero
  · have hene : e.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr he0
    have her : e.card ≤ r :=
      (mem_orderedConfigurationBaseEdges_iff e).1 he
    have hdensity :=
      (hgood (positiveOrderedFaceOfEdge e hene her)).1
    have hrank :
        (positiveOrderedFaceOfEdge e hene her).rank = e.card := by
      rw [← positiveOrderedFaceEdge_card,
        positiveOrderedFaceEdge_ofEdge]
    rw [hrank] at hdensity
    simpa [sourceFullMixedCoarseDensity,
      orderedConfigurationBaseDensity, hene, her] using hdensity

theorem hasTaoBundleCountingStep_orderedConfiguration_of_sourceFull_rankwise
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ) (τ : ℝ)
    (hβ : ∀ d, 0 ≤ β d)
    (hτ : 0 ≤ τ)
    (hgood : A.IsSourceFullMixedGood P α β)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => τ)) :
    HasTaoBundleCountingStep
      (H := orderedConfigurationBaseEdges k r)
      (orderedConfigurationBaseWeight A)
      (orderedConfigurationBaseDensity P A)
      β τ := by
  apply HypergraphBundle.hasTaoBundleCountingStep_orderedConfiguration
      P A β τ hβ hτ
  · exact
      HypergraphBundle.hasOrderedConfigurationBundleLocalizedDefect_of_sourceFullMixedGood
        P A α β hgood
  · exact
      HypergraphBundle.hasOrderedConfigurationBundleFrozenUniformity_of_fullyMixed
        P A τ hregular
        (HypergraphBundle.hasOrderedConfigurationBundleFrozenCutRepresentation
          P A)

theorem abs_bundleCount_orderedConfiguration_sub_main_le_rankwiseEnvelope
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ)
    (hαzero : α 0 ≤ 1)
    (hβ : ∀ d, 0 ≤ β d)
    (hτ : 0 ≤ τ)
    (hgood : A.IsSourceFullMixedGood P α β)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => τ))
    (henvelope : IsBundleCountingEnvelope α β μ τ E)
    {K : Type} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    (hclosed : B.IsClosedUnderInclusion) :
    |B.bundleCount
          (B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A)) -
        B.bundleMainProduct
          (orderedConfigurationBaseDensity P A)| ≤
      E B.order B.edges.card *
        B.bundleMainProduct
          (orderedConfigurationBaseDensity P A) := by
  exact
    @abs_bundleCount_pullback_sub_bundleMainProduct_le_envelope
      (Fin k) G inferInstance inferInstance
      (orderedConfigurationBaseEdges k r) inferInstance
      (orderedConfigurationBaseWeight A)
      (orderedConfigurationBaseDensity P A)
      α β μ τ E
      (orderedConfigurationBaseWeight_unitInterval A)
      (orderedConfigurationBaseWeight_idempotent A)
      (orderedConfigurationBaseWeight_empty A)
      (orderedConfigurationBaseDensity_empty P A)
      (orderedConfigurationBaseDensity_ge_of_sourceFullMixedGood_rankwise
        P A α β hαzero hgood)
      (hasTaoBundleCountingStep_orderedConfiguration_of_sourceFull_rankwise
        P A α β τ hβ hτ hgood hregular)
      henvelope K inferInstance inferInstance B hclosed

theorem one_sub_rankwiseEnvelope_mul_densityProduct_le_fullConfigurationCount
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ)
    (hαzero : α 0 ≤ 1)
    (hβ : ∀ d, 0 ≤ β d)
    (hτ : 0 ≤ τ)
    (hgood : A.IsSourceFullMixedGood P α β)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => τ))
    (henvelope : IsBundleCountingEnvelope α β μ τ E) :
    (1 - E
          (orderedConfigurationInitialBundle k r).order
          (orderedConfigurationInitialBundle k r).edges.card) *
        (∏ e : PositiveOrderedFace k r,
          mixedConfigurationCoarseDensity P A e) ≤
      fullConfigurationCount A := by
  have hcount :=
    abs_bundleCount_orderedConfiguration_sub_main_le_rankwiseEnvelope
      P A α β μ τ E hαzero hβ hτ hgood hregular henvelope
      (orderedConfigurationInitialBundle k r)
      (orderedConfigurationInitialBundle_closed k r)
  rw [orderedConfigurationInitialBundle_bundleCount A,
    orderedConfigurationInitialBundle_bundleMainProduct P A] at hcount
  have hlower :
      - (E
          (orderedConfigurationInitialBundle k r).order
          (orderedConfigurationInitialBundle k r).edges.card *
            (∏ e : PositiveOrderedFace k r,
              mixedConfigurationCoarseDensity P A e)) ≤
        fullConfigurationCount A -
          (∏ e : PositiveOrderedFace k r,
            mixedConfigurationCoarseDensity P A e) :=
    neg_le_of_abs_le hcount
  linarith

theorem half_rankwiseDensityProduct_le_fullConfigurationCount
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ)
    (hα : ∀ d, 0 < α d)
    (hαone : ∀ d, α d ≤ 1)
    (hβ : ∀ d, 0 ≤ β d)
    (hτ : 0 ≤ τ)
    (hgood : A.IsSourceFullMixedGood P α β)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => τ))
    (henvelope : IsBundleCountingEnvelope α β μ τ E)
    (herror :
      E
          (orderedConfigurationInitialBundle k r).order
          (orderedConfigurationInitialBundle k r).edges.card <
        1 / 2) :
    (1 / 2 : ℝ) *
        (∏ e : PositiveOrderedFace k r, α e.rank) ≤
      fullConfigurationCount A := by
  have hlower :=
    one_sub_rankwiseEnvelope_mul_densityProduct_le_fullConfigurationCount
      P A α β μ τ E (hαone 0) hβ hτ hgood hregular henvelope
  have hfloorProduct_nonneg :
      0 ≤ ∏ e : PositiveOrderedFace k r, α e.rank := by
    exact Finset.prod_nonneg fun e _ => (hα e.rank).le
  have hdensityProduct :
      (∏ e : PositiveOrderedFace k r, α e.rank) ≤
        ∏ e : PositiveOrderedFace k r,
          mixedConfigurationCoarseDensity P A e := by
    apply Finset.prod_le_prod₀
    · intro e _he
      exact (hα e.rank).le
    · intro e _he
      simpa [sourceFullMixedCoarseDensity] using (hgood e).1
  have hone :
      (1 / 2 : ℝ) ≤
        1 - E
          (orderedConfigurationInitialBundle k r).order
          (orderedConfigurationInitialBundle k r).edges.card := by
    linarith
  have hone_nonneg :
      0 ≤
        1 - E
          (orderedConfigurationInitialBundle k r).order
          (orderedConfigurationInitialBundle k r).edges.card := by
    linarith
  calc
    (1 / 2 : ℝ) *
          (∏ e : PositiveOrderedFace k r, α e.rank) ≤
        (1 - E
            (orderedConfigurationInitialBundle k r).order
            (orderedConfigurationInitialBundle k r).edges.card) *
          (∏ e : PositiveOrderedFace k r, α e.rank) :=
      mul_le_mul_of_nonneg_right hone hfloorProduct_nonneg
    _ ≤
        (1 - E
            (orderedConfigurationInitialBundle k r).order
            (orderedConfigurationInitialBundle k r).edges.card) *
          (∏ e : PositiveOrderedFace k r,
            mixedConfigurationCoarseDensity P A e) := by
      exact mul_le_mul_of_nonneg_left hdensityProduct hone_nonneg
    _ ≤ fullConfigurationCount A :=
      hlower

theorem half_rankwiseDensityProduct_le_fullConfigurationCount_of_rankBound
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ)
    (hα : ∀ d, 0 < α d)
    (hαone : ∀ d, α d ≤ 1)
    (hβ : ∀ d, 0 ≤ β d)
    (hτ : 0 ≤ τ)
    (hgood : A.IsSourceFullMixedGood P α β)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => τ))
    (henvelope : IsBundleCountingEnvelope α β μ τ E)
    (herror :
      E r (orderedConfigurationInitialBundle k r).edges.card <
        1 / 2) :
    (1 / 2 : ℝ) *
        (∏ e : PositiveOrderedFace k r, α e.rank) ≤
      fullConfigurationCount A := by
  apply
    half_rankwiseDensityProduct_le_fullConfigurationCount
      P A α β μ τ E hα hαone hβ hτ hgood hregular henvelope
  exact
    (henvelope.error_mono_order
      (orderedConfigurationInitialBundle_order_le k r)).trans_lt
      herror

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

noncomputable def sourceBundleRemovalHorizon (k r : ℕ) : ℕ :=
  bundleReverseDoublingHorizon r
    (orderedConfigurationInitialBundle k r).edges.card 0

noncomputable def sourceBundleRemovalDensityBudget
    (ε : ℝ) (r : ℕ) : ℝ :=
  min ε 1 /
    (4 * (Fintype.card (OrderedPositiveSubface r) + 1 : ℕ) : ℕ)

noncomputable def sourceBundleRemovalStep (k r : ℕ) : ℝ :=
  1 /
    (4 * (r * sourceBundleRemovalHorizon k r + 1 : ℕ) : ℕ)

noncomputable def sourceBundleRemovalKappa (k r : ℕ) : ℝ :=
  sourceBundleRemovalStep k r / 8

theorem sourceBundleRemovalDensityBudget_pos
    {ε : ℝ} (hε : 0 < ε) (r : ℕ) :
    0 < sourceBundleRemovalDensityBudget ε r := by
  unfold sourceBundleRemovalDensityBudget
  positivity

theorem sourceBundleRemovalDensityBudget_le_one
    {ε : ℝ} (hε : 0 < ε) (r : ℕ) :
    sourceBundleRemovalDensityBudget ε r ≤ 1 := by
  unfold sourceBundleRemovalDensityBudget
  have hmin : min ε 1 ≤ 1 := min_le_right _ _
  have hden : (1 : ℝ) ≤
      (4 * (Fintype.card (OrderedPositiveSubface r) + 1 : ℕ) : ℕ) := by
    push_cast
    have hcard :
        (0 : ℝ) ≤ Fintype.card (OrderedPositiveSubface r) := by
      positivity
    nlinarith
  exact (div_le_self (le_of_lt (lt_min hε zero_lt_one)) hden).trans hmin

theorem card_mul_two_sourceBundleRemovalDensityBudget_le
    {ε : ℝ} (hε : 0 < ε) (r : ℕ) :
    (Fintype.card (OrderedPositiveSubface r) : ℝ) *
        (sourceBundleRemovalDensityBudget ε r +
          sourceBundleRemovalDensityBudget ε r) ≤ ε := by
  let s := Fintype.card (OrderedPositiveSubface r)
  let x : ℝ := min ε 1
  have hx : 0 < x := lt_min hε zero_lt_one
  have hden : (0 : ℝ) < (4 * (s + 1 : ℕ) : ℕ) := by
    positivity
  have hs : (0 : ℝ) ≤ s := by positivity
  calc
    (Fintype.card (OrderedPositiveSubface r) : ℝ) *
          (sourceBundleRemovalDensityBudget ε r +
            sourceBundleRemovalDensityBudget ε r) =
        ((2 * (s : ℝ)) * x) / (4 * (s + 1 : ℕ) : ℕ) := by
      simp only [sourceBundleRemovalDensityBudget, s, x]
      ring
    _ ≤ x := by
      apply (div_le_iff₀ hden).2
      push_cast
      nlinarith
    _ ≤ ε := min_le_left _ _

theorem sourceBundleRemovalStep_pos (k r : ℕ) :
    0 < sourceBundleRemovalStep k r := by
  unfold sourceBundleRemovalStep
  positivity

theorem sourceBundleRemovalStep_le_one (k r : ℕ) :
    sourceBundleRemovalStep k r ≤ 1 := by
  unfold sourceBundleRemovalStep
  apply (div_le_one (by positivity)).2
  push_cast
  have hr : (0 : ℝ) ≤ r := by positivity
  have hH : (0 : ℝ) ≤ sourceBundleRemovalHorizon k r := by
    positivity
  nlinarith [mul_nonneg hr hH]

theorem sourceBundleRemovalKappa_pos (k r : ℕ) :
    0 < sourceBundleRemovalKappa k r := by
  unfold sourceBundleRemovalKappa
  exact div_pos (sourceBundleRemovalStep_pos k r) (by norm_num)

theorem sourceBundleRemovalKappa_le_one (k r : ℕ) :
    sourceBundleRemovalKappa k r ≤ 1 := by
  unfold sourceBundleRemovalKappa
  have hstep := sourceBundleRemovalStep_le_one k r
  nlinarith [sourceBundleRemovalStep_pos k r]

theorem four_mul_sourceBundleRemovalKappa_le_step (k r : ℕ) :
    4 * sourceBundleRemovalKappa k r ≤
      sourceBundleRemovalStep k r := by
  unfold sourceBundleRemovalKappa
  nlinarith [sourceBundleRemovalStep_pos k r]

theorem sourceBundleRemovalKappa_sq_le_half_step (k r : ℕ) :
    sourceBundleRemovalKappa k r ^ 2 ≤
      sourceBundleRemovalStep k r / 2 := by
  unfold sourceBundleRemovalKappa
  have hpos := sourceBundleRemovalStep_pos k r
  have hone := sourceBundleRemovalStep_le_one k r
  nlinarith [sq_nonneg (sourceBundleRemovalStep k r)]

theorem sourceBundleRemovalStep_total_le_quarter (k r : ℕ) :
    (r : ℝ) * (sourceBundleRemovalHorizon k r : ℝ) *
        sourceBundleRemovalStep k r ≤ 1 / 4 := by
  let p := r * sourceBundleRemovalHorizon k r
  have hden : (0 : ℝ) < (4 * (p + 1 : ℕ) : ℕ) := by
    positivity
  rw [show
    (r : ℝ) * (sourceBundleRemovalHorizon k r : ℝ) *
          sourceBundleRemovalStep k r =
        (p : ℝ) / (4 * (p + 1 : ℕ) : ℕ) by
      simp only [sourceBundleRemovalStep, p]
      push_cast
      ring]
  apply (div_le_iff₀ hden).2
  push_cast
  have hp : (0 : ℝ) ≤ p := by positivity
  nlinarith

theorem sourceBundleRemovalStep_total_le_one (k r : ℕ) :
    (r : ℝ) * (sourceBundleRemovalHorizon k r : ℝ) *
        sourceBundleRemovalStep k r ≤ 1 :=
  (sourceBundleRemovalStep_total_le_quarter k r).trans (by norm_num)

theorem sourceBundleRemovalStep_total_lt_half (k r : ℕ) :
    (r : ℝ) * (sourceBundleRemovalHorizon k r : ℝ) *
        sourceBundleRemovalStep k r < 1 / 2 :=
  (sourceBundleRemovalStep_total_le_quarter k r).trans_lt (by norm_num)

noncomputable def sourceBundleRemovalCountThreshold
    (k r ceiling : ℕ) (δ : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    sourceBundleDensity δ ceiling ^
      Fintype.card (PositiveOrderedFace k r)

theorem sourceBundleRemovalCountThreshold_pos
    {δ : ℝ} (hδ : 0 < δ) (k r ceiling : ℕ) :
    0 < sourceBundleRemovalCountThreshold k r ceiling δ := by
  unfold sourceBundleRemovalCountThreshold
  exact mul_pos (by norm_num)
    (pow_pos (sourceBundleDensity_pos hδ ceiling) _)

theorem hasUniformOrderedPatternRemoval_sourceFull
    (k n : ℕ) (hrank : n + 1 ≤ k) :
    HasUniformOrderedPatternRemoval k (n + 1) := by
  intro ε hε
  let r : ℕ := n + 1
  let edgeBound : ℕ :=
    (orderedConfigurationInitialBundle k r).edges.card
  let N : ℕ := sourceBundleRemovalHorizon k r
  let δ : ℝ := sourceBundleRemovalDensityBudget ε r
  let step : ℝ := sourceBundleRemovalStep k r
  let κ : ℝ := sourceBundleRemovalKappa k r
  have hδ : 0 < δ := by
    exact sourceBundleRemovalDensityBudget_pos hε r
  have hδ_one : δ ≤ 1 := by
    exact sourceBundleRemovalDensityBudget_le_one hε r
  have hstep : 0 < step := by
    exact sourceBundleRemovalStep_pos k r
  have hκ : 0 < κ := by
    exact sourceBundleRemovalKappa_pos k r
  have hκ_one : κ ≤ 1 := by
    exact sourceBundleRemovalKappa_le_one k r
  have hκ_step : 4 * κ ≤ step := by
    exact four_mul_sourceBundleRemovalKappa_le_step k r
  have hκ_sq : κ ^ 2 ≤ step / 2 := by
    exact sourceBundleRemovalKappa_sq_le_half_step k r
  obtain ⟨Q, hQ⟩ :=
    exists_sourceBundleRemovalGrowthCoefficient
      hδ hδ_one hκ hκ_one N
  let F : NatGrowthFunction := sourceBundleRemovalGrowth Q N
  let initialBound : Fin (r + 1) → ℕ := fun _ => 2
  let S : SourceFullCoarseTargetSchedule.Bounded
      k r initialBound F 0 :=
    Classical.choice
      (SourceFullCoarseTargetSchedule.bounded_nonempty
        k r initialBound F 0)
  let c : ℝ :=
    sourceBundleRemovalCountThreshold k r S.ceiling δ
  have hc : 0 < c := by
    exact sourceBundleRemovalCountThreshold_pos hδ k r S.ceiling
  refine ⟨c, hc, ?_⟩
  intro G _instFintype _instDecidableEq _instNonempty H hcount
  let initial : OrderedPartitionComplex G k r :=
    orderedPatternInitialComplex H
  obtain ⟨Cbounded⟩ :=
    S.certificate_nonempty initial (by
      intro q e
      exact complexity_orderedPatternInitialComplex_le_two H q e)
  let C := Cbounded.toSourceFull
  let P : OrderedCoarseFineComplex G k r :=
    C.regularity.toCoarseFine
  let α : ℕ → ℝ := sourceBundleRankwiseDensity δ C.scale
  let β : ℕ → ℝ := sourceBundleRankwiseDefect δ κ N C.scale
  let μ : ℕ → ℝ := bundleRankwiseDensityFloor α
  let τ : ℝ := sourceFullCommonTolerance F C.scale
  let E : ℕ → ℕ → ℝ :=
    bundleRankwiseEnvelopeError α β μ τ
  let D : OrderedPattern.DeletionFamily (G := G) k r :=
    P.sourceFullBadBaseDeletionFamily α β
  have hα : ∀ d, 0 < α d := by
    intro d
    exact sourceBundleRankwiseDensity_pos hδ C.scale d
  have hα_one : ∀ d, α d ≤ 1 := by
    intro d
    exact sourceBundleRankwiseDensity_le_one hδ.le hδ_one C.scale d
  have hβ : ∀ d, 0 ≤ β d := by
    intro d
    exact sourceBundleRankwiseDefect_nonneg δ κ N C.scale d
  have hβ_pos : ∀ d, 0 < β d := by
    intro d
    unfold β sourceBundleRankwiseDefect
    exact sq_pos_of_pos
      (sourceBundleDefectScale_pos hδ hκ N _)
  have hτ : 0 ≤ τ := by
    exact (sourceFullCommonTolerance_pos F C.scale).le
  have hscale : Antitone C.scale := C.scale_antitone
  have henvelopeRaw :=
    sourceBundleRankwiseEnvelope_and_error_lt_half
      (r := r) (edgeBound := edgeBound) (Q := Q)
      hδ hδ_one hκ hstep.le hκ_step hκ_sq
      (by
        simpa [step, N, edgeBound, sourceBundleRemovalHorizon] using
          sourceBundleRemovalStep_total_le_one k r)
      (by
        simpa [step, N, edgeBound, sourceBundleRemovalHorizon] using
          sourceBundleRemovalStep_total_lt_half k r)
      (by simpa [N, edgeBound, sourceBundleRemovalHorizon] using hQ)
      C.scale hscale
  have henvelope : IsBundleCountingEnvelope α β μ τ E := by
    simpa [α, β, μ, τ, E, F, N, edgeBound,
      sourceBundleRemovalHorizon] using henvelopeRaw.1
  have herror : E r edgeBound < 1 / 2 := by
    simpa [α, β, μ, τ, E, F, N, edgeBound,
      sourceBundleRemovalHorizon] using henvelopeRaw.2
  have hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => τ) := by
    simpa [P, τ] using
      C.isFullyMixedPreliminaryOrderedRegular_common
  have hthreshold :
      c ≤ (1 / 2 : ℝ) *
        (∏ e : PositiveOrderedFace k r, α e.rank) := by
    have hfloor : 0 ≤ sourceBundleDensity δ S.ceiling :=
      (sourceBundleDensity_pos hδ S.ceiling).le
    have hpoint : ∀ e : PositiveOrderedFace k r,
        sourceBundleDensity δ S.ceiling ≤ α e.rank := by
      intro e
      unfold α sourceBundleRankwiseDensity
      apply sourceBundleDensity_antitone hδ.le
      exact
        (hscale (Fin.zero_le _)).trans
          Cbounded.scale_zero_le_ceiling
    have hprod :
        sourceBundleDensity δ S.ceiling ^
            Fintype.card (PositiveOrderedFace k r) ≤
          ∏ e : PositiveOrderedFace k r, α e.rank := by
      calc
        sourceBundleDensity δ S.ceiling ^
              Fintype.card (PositiveOrderedFace k r) =
            ∏ _e : PositiveOrderedFace k r,
              sourceBundleDensity δ S.ceiling := by simp
        _ ≤ ∏ e : PositiveOrderedFace k r, α e.rank := by
          apply Finset.prod_le_prod₀
          · intro e _he
            exact hfloor
          · intro e _he
            exact hpoint e
    simpa [c, sourceBundleRemovalCountThreshold] using
      (mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have hgoodCount :
      ∀ A : ClosedOrderedAtomConfiguration G k r P.coarse,
        A.IsSourceFullMixedGood P α β →
          c ≤ fullConfigurationCount A := by
    intro A hgood
    exact hthreshold.trans
      (half_rankwiseDensityProduct_le_fullConfigurationCount_of_rankBound
        P A α β μ τ E hα hα_one hβ hτ hgood hregular
        henvelope (by simpa [edgeBound] using herror))
  have hinitial :
      P.coarse.Refines (orderedPatternInitialComplex H) := by
    simpa [P, initial,
      CoarseTargetOrderedComplexRegularityCertificate.toCoarseFine] using
        C.regularity.coarse_refines_initial
  have hcover : H.IsCover D := by
    exact
      sourceFullBadBaseDeletionFamily_isCover_of_sourceFullMixedGood_count
        (by simpa [r] using hrank) H P hinitial α β c hcount hgoodCount
  refine ⟨D, hcover, ?_⟩
  intro e
  have hbase :=
    P.faceDeletionDensity_sourceFullBadBaseDeletionFamily_le
      α β (fun j => (hα (j + 1)).le) (fun j => hβ_pos (j + 1)) e
  calc
    OrderedPattern.faceDeletionDensity D e ≤
        ∑ q : OrderedPositiveSubface r,
          ((FacePartition.complexity
              (P.coarse.partition q.1.succ (q.2.trans e)) : ℝ) *
                α (q.1.1 + 1) +
            P.coarseUpperFaceAtomEnergyGap q.1 (q.2.trans e) /
                β (q.1.1 + 1)) := by
      simpa [D] using hbase
    _ ≤ ∑ _q : OrderedPositiveSubface r, (δ + δ) := by
      apply Finset.sum_le_sum
      intro q _hq
      have hd : q.1.1 + 1 ≤ r := by omega
      have hselected :
          sourceBundleSelectedScale C.scale (q.1.1 + 1) =
            C.scale q.1.succ := by
        calc
          sourceBundleSelectedScale C.scale (q.1.1 + 1) =
              C.scale
                ⟨q.1.1 + 1, Nat.lt_succ_iff.mpr hd⟩ :=
            sourceBundleSelectedScale_of_le C.scale hd
          _ = C.scale q.1.succ := by
            apply congrArg C.scale
            exact Fin.ext rfl
      have hcomplexity :
          FacePartition.complexity
              (P.coarse.partition q.1.succ (q.2.trans e)) ≤
            C.scale q.1.succ := by
        simpa [P,
          CoarseTargetOrderedComplexRegularityCertificate.toCoarseFine] using
          C.coarse_complexity q.1.succ (q.2.trans e)
      have hlow :
          (FacePartition.complexity
              (P.coarse.partition q.1.succ (q.2.trans e)) : ℝ) *
                α (q.1.1 + 1) ≤ δ := by
        calc
          (FacePartition.complexity
                (P.coarse.partition q.1.succ (q.2.trans e)) : ℝ) *
                  α (q.1.1 + 1) ≤
              (C.scale q.1.succ : ℝ) * α (q.1.1 + 1) :=
            mul_le_mul_of_nonneg_right
              (Nat.cast_le.mpr hcomplexity) (hα _).le
          _ = (C.scale q.1.succ : ℝ) *
                sourceBundleDensity δ (C.scale q.1.succ) := by
            simp [α, sourceBundleRankwiseDensity, hselected]
          _ ≤ δ := mul_sourceBundleDensity_le hδ.le _
      have hfaceLayer :
          P.coarseUpperFaceAtomEnergyGap q.1 (q.2.trans e) ≤
            P.coarseUpperLayerAtomEnergyGap q.1 := by
        rw [P.coarseUpperLayerAtomEnergyGap_eq_sum_face q.1]
        exact Finset.single_le_sum
          (fun f _ => P.coarseUpperFaceAtomEnergyGap_nonneg q.1 f)
          (Finset.mem_univ (q.2.trans e))
      have hlayer :
          P.coarseUpperLayerAtomEnergyGap q.1 ≤
            sourceFullRankGap F C.scale q.1 := by
        simpa [P] using C.rank_gap_le q.1
      have hdefect :
          P.coarseUpperFaceAtomEnergyGap q.1 (q.2.trans e) /
                β (q.1.1 + 1) ≤ δ := by
        calc
          P.coarseUpperFaceAtomEnergyGap q.1 (q.2.trans e) /
                β (q.1.1 + 1) ≤
              sourceFullRankGap F C.scale q.1 /
                β (q.1.1 + 1) :=
            div_le_div_of_nonneg_right
              (hfaceLayer.trans hlayer) (hβ _)
          _ =
              (1 /
                  (sourceBundleRemovalGrowth Q N
                    (C.scale q.1.succ) : ℝ) ^ 2) /
                sourceBundleDefectScale δ κ N
                    (C.scale q.1.succ) ^ 2 := by
            simp [F, sourceFullRankGap, β,
              sourceBundleRankwiseDefect, hselected]
          _ ≤ δ :=
            sourceFullRankGap_div_sourceBundleDefectScale_sq_le
              hδ hκ hQ (C.scale q.1.succ)
      exact add_le_add hlow hdefect
    _ = (Fintype.card (OrderedPositiveSubface r) : ℝ) *
          (δ + δ) := by
      simp [mul_add]
    _ ≤ ε := by
      simpa [δ, r] using
        card_mul_two_sourceBundleRemovalDensityBudget_le hε (n + 1)

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

theorem szemeredi (k : ℕ) (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ HasUniformDenseAPCount k δ c := by
  refine
    exists_uniformDenseAPCount_of_orderedRemoval_of_two_le
      k hk ?_ hδ
  have hrank : k - 1 = (k - 2) + 1 := by omega
  rw [hrank]
  exact hasUniformOrderedPatternRemoval_sourceFull
    k (k - 2) (by omega)

end Erdos3.FixedDensity

end

end OAI
