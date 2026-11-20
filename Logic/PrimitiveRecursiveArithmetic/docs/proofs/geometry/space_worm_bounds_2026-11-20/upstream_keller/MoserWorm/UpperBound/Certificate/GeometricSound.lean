import MoserWorm.UpperBound.ContactOrder

/-!
# From accepted certificates to actual universal coverage

The contact model is constructed from the finite normalized witness.
`ContactOrder` transports finite-label families and complements to the real
checker API. All contact, support, rank, and prefix facts are instantiated.
-/

noncomputable section

namespace MoserWorm.UpperBound.Certificate

open Set

/-- Construct every field of the real certificate contact model from the
actual normalized witness and the accepted normal table. -/
theorem contactModel_exists {K : Set Plane} (W : NormalizedWitness K)
    (T : LabelTables) (hT : labelsOK T = true) :
    Nonempty (ContactModel T (convexHull ℝ W.vertices) (natExt W.path.vertex) W.path.edges) := by
  obtain ⟨p, q, hp, hq, hprefix⟩ := W.certificate_contactPrefixes T hT
  refine ⟨{
    rank := W.contactRankNat T
    p := p
    q := q
    rank_le := W.contactRankNat_le T
    contacts := W.certificate_contactData T
    floor_order := ?_
    p_le := hp
    q_le := hq
    prefixes := hprefix }⟩
  have h0 : 0 < T.nLab := by unfold LabelTables.nLab; omega
  have h1 : 1 < T.nLab := by unfold LabelTables.nLab; omega
  rw [W.contact_natExt T ⟨0, h0⟩, W.contact_natExt T ⟨1, h1⟩]
  change (W.polygon.vertex (W.contactVertex T ⟨0, h0⟩)).re ≤
    (W.polygon.vertex (W.contactVertex T ⟨1, h1⟩)).re
  rw [W.contactVertex_minus, W.contactVertex_plus, W.polygon.base_zero]
  exact W.polygon.tip_re.le

/-- Accepted certificates have an actual checked normal table. -/
theorem checkCert_labels (c : Cert) (hc : checkCert c = true) :
    ∃ T : LabelTables, buildLabels c.specs.toList = some T ∧ labelsOK T = true := by
  cases hT : buildLabels c.specs.toList with
  | none => simp [checkCert, hT] at hc
  | some T => exact ⟨T, rfl, (checkCert_extract c hc T hT).2.2.1⟩

/-- The concrete quadrilateral has the unit segment needed by the finite
witness reduction. Its long diagonal and convexity are proved in `Shape`. -/
theorem Kquad_containsUnitSegment : ContainsUnitSegment Kquad := by
  obtain ⟨ha, hb, hab⟩ := Kquad_long_chord
  exact containsUnitSegment_of_dist_ge_one convex_Kquad ha hb hab.le

/-- Kernel acceptance implies universal coverage of actual continuous unit
arcs. All compactness, finite-witness, normalization, contact, prefix, and
length inputs are constructed internally. The only parameter is the accepted
certificate; no geometric model or order hypothesis remains. -/
theorem checkCert_universalCover (c : Cert) (hc : checkCert c = true) :
    IsUniversalCover Kquad := by
  intro γ hγ
  by_contra hmiss
  obtain ⟨W⟩ := normalized_witness_exists isCompact_Kquad convex_Kquad
    Kquad_containsUnitSegment hγ hmiss
  obtain ⟨T, hT, hOK⟩ := checkCert_labels c hc
  obtain ⟨model⟩ := contactModel_exists W T hOK
  have hC : IsCompact (convexHull ℝ W.vertices) := W.finite.isCompact_convexHull ℝ
  have hne : (convexHull ℝ W.vertices).Nonempty :=
    ⟨W.path.vertex 0, subset_convexHull ℝ _ (W.path.range_eq.subset (mem_range_self 0))⟩
  exact W.uncovered (checkCert_contact_cover c hc T hT hC hne
    (natExt W.path.vertex) W.path.edges model W.length_le)

theorem checkCert_convexUniversalCover (c : Cert) (hc : checkCert c = true) :
    IsConvexUniversalCover Kquad := ⟨convex_Kquad, checkCert_universalCover c hc⟩

/-- Universal coverage and the exact area, conditional only on kernel
acceptance of the supplied certificate. -/
theorem checkCert_upper_bound (c : Cert) (hc : checkCert c = true) :
    IsConvexUniversalCover Kquad ∧
      MeasureTheory.volume Kquad = ENNReal.ofReal (areaK : ℝ) :=
  ⟨checkCert_convexUniversalCover c hc, volume_Kquad⟩

theorem checkCert_optimalArea_upper_bound (c : Cert) (hc : checkCert c = true) :
    optimalArea ≤ ENNReal.ofReal (areaK : ℝ) := by
  rw [← volume_Kquad]
  exact optimalArea_le (checkCert_convexUniversalCover c hc)

end MoserWorm.UpperBound.Certificate
