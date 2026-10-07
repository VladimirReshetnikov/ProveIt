import OAI.Combinatorics.Progressions.Estimates.PreparedDetectedCanonicalNativeSource
import OAI.Combinatorics.Progressions.Probability.AllocatedFullBoxPositiveLaw

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

private theorem preparedResource_nonneg
    (K : PreparedModularCanonicalDetectorResourceConstants) {P : ℝ} (hP : 0 ≤ P) :
    (preparedModularCanonicalDetectorResources K P).Bounds
      ((P + Classical.choose (exists_preparedModularCanonicalDetector_resource_budget K)) ^
        Classical.choose (exists_preparedModularCanonicalDetector_resource_budget K)) :=
  ((Classical.choose_spec (exists_preparedModularCanonicalDetector_resource_budget K)).2 P hP).1

private theorem prepared_slicedGridGeometryLog_mono
    {D v w t D' v' w' t' : ℝ} (hD : 0 ≤ D) (hv : 0 ≤ v) (hw : 0 ≤ w) (ht : 0 ≤ t)
    (hDD : D ≤ D') (hvv : v ≤ v') (hww : w ≤ w') (htt : t ≤ t') :
    slicedGridGeometryLog D v w t ≤ slicedGridGeometryLog D' v' w' t' := by
  have hD' : 0 ≤ D' := hD.trans hDD
  unfold slicedGridGeometryLog
  gcongr

private theorem prepared_affineAmbientPrimitiveBudget_mono
    {base Q base' Q' : ℝ} (hb : 0 ≤ base) (hQ : 0 ≤ Q)
    (hbb : base ≤ base') (hQQ : Q ≤ Q') :
    affineAmbientPrimitiveBudget base Q ≤ affineAmbientPrimitiveBudget base' Q' := by
  have hb' : 0 ≤ base' := hb.trans hbb
  have hQ' : 0 ≤ Q' := hQ.trans hQQ
  dsimp only [affineAmbientPrimitiveBudget, affineAmbientMassLog]
  gcongr

theorem preparedModularCanonicalDetector_ideal_site_bound
    (K : PreparedModularCanonicalDetectorResourceConstants) {P : ℝ} (hP : 0 ≤ P)
    {outputs : ℕ} (hout : (outputs : ℝ) ≤ P) {sumlog : ℝ}
    (hsum : sumlog ∈ Set.Icc 0 (preparedModularCanonicalDetectorResources K P).sumlog) :
    idealSiteLogBudget outputs 1 sumlog ∈
      Set.Icc 0 (preparedModularCanonicalDetectorResources K P).idealQ := by
  let r := preparedModularCanonicalDetectorResources K P
  have hprofile : (probabilityProfileLipschitz : ℝ) ≤ comparisonProfileBound :=
    (Nat.le_ceil _).trans (by unfold comparisonProfileBound; push_cast; linarith)
  refine ⟨(idealSiteLogBudget_bounds outputs 1 hsum.1).1, ?_⟩
  change idealSiteLogBudget outputs 1 sumlog ≤
    1 + P * r.sumlog + (P + comparisonProfileBound + (P + 1) * r.sumlog) + r.sumlog + 1
  unfold idealSiteLogBudget affineProfileLogBound
  push_cast
  have hs0 := hsum.1
  have hs1 := hsum.2
  gcongr

theorem preparedModularCanonicalDetector_ambient_bound
    (K : PreparedModularCanonicalDetectorResourceConstants) {P : ℝ} (hP : 0 ≤ P)
    {outputs : ℕ} (hout : (outputs : ℝ) ≤ P)
    {box Prho volume normalizer mask target base : ℝ}
    (hbox : box ∈ Set.Icc 0 (preparedModularCanonicalDetectorResources K P).Pbox)
    (hPrho : Prho ∈ Set.Icc 0 P)
    (hvolume : volume ∈ Set.Icc 0 (preparedModularCanonicalDetectorResources K P).Vlog)
    (hnormalizer : normalizer ∈ Set.Icc 0 (preparedModularCanonicalDetectorResources K P).Nlog)
    (hmask : mask ∈ Set.Icc 0 (preparedModularCanonicalDetectorResources K P).Q)
    (htarget : target ∈ Set.Icc 0 P)
    (hbase : base ∈ Set.Icc 0 (preparedModularCanonicalDetectorResources K P).baseAmbient) :
    let site := idealSiteLogBudget outputs 1 (box + Prho + volume + normalizer + mask + target)
    site ∈ Set.Icc 0 (preparedModularCanonicalDetectorResources K P).idealQ ∧
    affineAmbientPrimitiveBudget base site ∈
      Set.Icc 0 (preparedModularCanonicalDetectorResources K P).ambient := by
  intro site
  have hsum : box + Prho + volume + normalizer + mask + target ∈
      Set.Icc 0 (preparedModularCanonicalDetectorResources K P).sumlog := by
    constructor
    · linarith only [hbox.1, hPrho.1, hvolume.1, hnormalizer.1, hmask.1, htarget.1]
    · exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hbox.2 hPrho.2)
        hvolume.2) hnormalizer.2) hmask.2) htarget.2
  have hsite := preparedModularCanonicalDetector_ideal_site_bound K hP hout hsum
  refine ⟨hsite, ⟨?_, ?_⟩⟩
  · have hb := hbase.1
    have hq := hsite.1
    dsimp only [affineAmbientPrimitiveBudget, affineAmbientMassLog]
    positivity
  · exact prepared_affineAmbientPrimitiveBudget_mono hbase.1 hsite.1 hbase.2 hsite.2

theorem preparedModularCanonicalDetector_grid_bound
    (K : PreparedModularCanonicalDetectorResourceConstants) {P pDetect qlog : ℝ}
    (hP : 0 ≤ P) (hp : pDetect ∈ Set.Icc 0 P)
    (hq : qlog ∈ Set.Icc 0 (preparedModularCanonicalDetectorResources K P).Q) :
    let r := preparedModularCanonicalDetectorResources K P
    let tg := 1 + qlog + (pDetect + 1) + 1
    let pg := (K.Cgrid : ℝ) + 2 * qlog + (pDetect + 1) + 4
    slicedGridGeometryLog r.Dg r.v (pDetect + 1) tg + pg ∈ Set.Icc 0 r.gridlog := by
  intro r tg pg
  have h := preparedResource_nonneg K hP
  have ht : tg ∈ Set.Icc 0 r.tq := by
    change 0 ≤ 1 + qlog + (pDetect + 1) + 1 ∧
      1 + qlog + (pDetect + 1) + 1 ≤ 1 + r.Q + (P + 1) + 1
    constructor <;> linarith only [hq.1, hq.2, hp.1, hp.2]
  have hg : pg ∈ Set.Icc 0 r.pq := by
    change 0 ≤ (K.Cgrid : ℝ) + 2 * qlog + (pDetect + 1) + 4 ∧
      (K.Cgrid : ℝ) + 2 * qlog + (pDetect + 1) + 4 ≤ K.Cgrid + 2 * r.Q + (P + 1) + 4
    constructor <;> linarith only [hq.1, hq.2, hp.1, hp.2, Nat.cast_nonneg (α := ℝ) K.Cgrid]
  have hw : 0 ≤ pDetect + 1 := by linarith only [hp.1]
  constructor
  · have hD := h.Dg.1
    have hv := h.v.1
    have ht0 := ht.1
    have hg0 := hg.1
    unfold slicedGridGeometryLog
    positivity
  · exact add_le_add
      (prepared_slicedGridGeometryLog_mono h.Dg.1 h.v.1 hw ht.1 le_rfl le_rfl
        (by change pDetect + 1 ≤ P + 1; linarith only [hp.2]) ht.2) hg.2

theorem preparedModularCanonicalDetector_grid_resource_width_bound
    (K : PreparedModularCanonicalDetectorResourceConstants) {P pDetect qlog : ℝ}
    (hP : 0 ≤ P) (hp : pDetect ∈ Set.Icc 0 P)
    (hq : qlog ∈ Set.Icc 0 (preparedModularCanonicalDetectorResources K P).Q) :
    let r := preparedModularCanonicalDetectorResources K P
    let tg := 1 + qlog + (pDetect + 1) + 1
    let pg := (K.Cgrid : ℝ) + 2 * qlog + (pDetect + 1) + 4
    slicedGridGeometryLog r.Dg r.v r.w tg + pg ∈ Set.Icc 0 r.gridlog := by
  intro r tg pg
  have h := preparedResource_nonneg K hP
  have ht : tg ∈ Set.Icc 0 r.tq := by
    change 0 ≤ 1 + qlog + (pDetect + 1) + 1 ∧
      1 + qlog + (pDetect + 1) + 1 ≤ 1 + r.Q + (P + 1) + 1
    constructor <;> linarith only [hq.1, hq.2, hp.1, hp.2]
  have hg : pg ∈ Set.Icc 0 r.pq := by
    change 0 ≤ (K.Cgrid : ℝ) + 2 * qlog + (pDetect + 1) + 4 ∧
      (K.Cgrid : ℝ) + 2 * qlog + (pDetect + 1) + 4 ≤ K.Cgrid + 2 * r.Q + (P + 1) + 4
    constructor <;> linarith only [hq.1, hq.2, hp.1, hp.2, Nat.cast_nonneg (α := ℝ) K.Cgrid]
  have hw : 0 ≤ r.w := h.w.1
  constructor
  · have hD := h.Dg.1
    have hv := h.v.1
    have ht0 := ht.1
    have hg0 := hg.1
    unfold slicedGridGeometryLog
    positivity
  · exact add_le_add
      (prepared_slicedGridGeometryLog_mono h.Dg.1 h.v.1 hw ht.1 le_rfl le_rfl le_rfl ht.2) hg.2

theorem preparedModularCanonicalDetector_native_inputs
    (K : PreparedModularCanonicalDetectorResourceConstants) {P : ℝ} (hP : 0 ≤ P) :
    let r := preparedModularCanonicalDetectorResources K P
    r.Dg ∈ Set.Icc 0 r.Pnative ∧ r.gridlog ∈ Set.Icc 0 r.Pnative ∧
    r.v ∈ Set.Icc 0 r.Pnative ∧ r.Fpref ∈ Set.Icc 0 r.Pnative ∧
    r.Banalytic ∈ Set.Icc 0 r.Pnative ∧ P ≤ r.Pnative ∧
    ∀ a ∈ Set.Icc (0 : ℝ) P, a ∈ Set.Icc 0 r.Pnative := by
  intro r
  have h := preparedResource_nonneg K hP
  have hD := h.Dg.1
  have hg := h.gridlog.1
  have hv := h.v.1
  have hf := h.Fpref.1
  have hb := h.Banalytic.1
  have heq : r.Pnative = r.Dg + r.gridlog + r.v + r.Fpref + 6 * P + r.Banalytic := rfl
  have hpv : P ≤ r.v := by change P ≤ P + 8; linarith
  have hPnative : P ≤ r.Pnative := by linarith only [heq, hpv, hD, hg, hf, hb, hP]
  refine ⟨⟨hD, ?_⟩, ⟨hg, ?_⟩, ⟨hv, ?_⟩, ⟨hf, ?_⟩, ⟨hb, ?_⟩, hPnative, ?_⟩
  all_goals first | linarith only [heq, hD, hg, hv, hf, hb, hP] |
    exact fun a ha => ⟨ha.1, ha.2.trans hPnative⟩

theorem preparedModularCanonicalDetector_final_error_bound
    (K : PreparedModularCanonicalDetectorResourceConstants) {P u pModel : ℝ}
    (hu : u ≤ P) (hpModel : pModel ≤ P) :
    u + 2 * pModel + (preparedModularCanonicalDetectorResources K P).nativeBudget + 30 ≤
      (preparedModularCanonicalDetectorResources K P).E := by
  let r := preparedModularCanonicalDetectorResources K P
  have hE : r.E = 3 * P + r.nativeBudget + 30 := rfl
  change u + 2 * pModel + r.nativeBudget + 30 ≤ r.E
  rw [hE]
  linarith only [hu, hpModel]

theorem preparedModularCanonicalDetector_native_budget_mono
    (K : PreparedModularCanonicalDetectorResourceConstants) {P native : ℝ}
    (hn : native ∈ Set.Icc 0 (preparedModularCanonicalDetectorResources K P).Pnative) :
    ((native + K.Cnative) ^ K.Cnative + K.Anorm) ^ K.Anorm ≤
      (preparedModularCanonicalDetectorResources K P).nativeBudget := by
  change ((native + K.Cnative) ^ K.Cnative + K.Anorm) ^ K.Anorm ≤
    (((preparedModularCanonicalDetectorResources K P).Pnative + K.Cnative) ^ K.Cnative +
      K.Anorm) ^ K.Anorm
  have hn0 := hn.1
  have hn1 := hn.2
  gcongr

theorem preparedModularCanonicalDetector_required_bounds
    (K : PreparedModularCanonicalDetectorResourceConstants) {P : ℝ} (hP : 0 ≤ P) :
    let r := preparedModularCanonicalDetectorResources K P
    (r.Psample + K.Apert) ^ K.Apert ≤ r.required ∧
    (r.Pmass + K.AmassWindow) ^ K.AmassWindow ≤ r.required ∧
    (r.Pproj + K.Aproj) ^ K.Aproj ≤ r.required ∧
    (r.Pside + K.Aside) ^ K.Aside ≤ r.required ∧
    (r.full + r.E + K.Amarginal) ^ K.Amarginal ≤ r.required := by
  intro r
  have h := preparedResource_nonneg K hP
  have hs := h.Psample.1
  have hm := h.Pmass.1
  have hp := h.Pproj.1
  have hside := h.Pside.1
  have hf := h.full.1
  have he := h.E.1
  have h1 : 0 ≤ (r.Psample + K.Apert) ^ K.Apert := by positivity
  have h2 : 0 ≤ (r.Pmass + K.AmassWindow) ^ K.AmassWindow := by positivity
  have h3 : 0 ≤ (r.Pproj + K.Aproj) ^ K.Aproj := by positivity
  have h4 : 0 ≤ (r.Pside + K.Aside) ^ K.Aside := by positivity
  have h5 : 0 ≤ (r.full + r.E + K.Amarginal) ^ K.Amarginal := by positivity
  have hsum : r.required = (r.Psample + K.Apert) ^ K.Apert +
      (r.Pmass + K.AmassWindow) ^ K.AmassWindow + (r.Pproj + K.Aproj) ^ K.Aproj +
      (r.Pside + K.Aside) ^ K.Aside + (r.full + r.E + K.Amarginal) ^ K.Amarginal := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith only [hsum, h1, h2, h3, h4, h5]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

theorem preparedModularCanonicalDetector_positive_bounds
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {Pmaster D : ℝ} (hMaster : 0 ≤ Pmaster)
    (hd : AllocatedComparisonDimensions (G := G) B (Fin 1)
      (fun j : Fin m => (boundedBooleanJetRows (Fin 1) (j.val + 1) : Type)) D)
    (hD : D ≤ Pmaster) {nX : ℕ} (hnX : (nX : ℝ) ≤ Pmaster)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp Pmaster)
    (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp Pmaster)
    (hLP : (S.value : ℝ) ≤ Real.exp Pmaster)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp Pmaster)
    (hVP : ∀ j, (V j : ℝ) ≤ Real.exp Pmaster)
    (p : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : Fin nX → ℕ) (hs : ∀ d, 0 < stride d)
    (hsP : ∀ d, (stride d : ℝ) ≤ Real.exp Pmaster)
    {τ ξ : ℝ} (hτ : 0 < τ) (hτP : τ⁻¹ ≤ Real.exp Pmaster)
    (hτhalf : τ ≤ 1 / 2) (hτdim : (nX : ℝ) * τ ≤ 1 / 2)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hξP : ξ⁻¹ ≤ Real.exp Pmaster)
    (N : Fin nX → ℕ) {rank : ℝ}
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
    (hCells : cells.Nonempty) :
    let r := preparedModularCanonicalDetectorResources (preparedModularCanonicalDetectorConstants m) Pmaster
    (∀ d, Real.exp r.required ≤ (N d : ℝ)) → Real.exp r.required ≤ rank →
    let W := allocatedPhysicalRootBudget B U basis S (fun _ => 0)
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let density := allocatedJointBaseDensity B U basis hb o hR hσ S (Fin nX) p hm
    let Z := selectedJointDensityMass bases stride cells widths density
    ∃ (_hN : ∀ x, 0 < N x) (_hbases : bases.Nonempty) (_hbox : (integerBox N).Nonempty)
      (_hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z),
    ∃ _hnormalizer : |Z - 1| ≤ Real.exp (-r.E) ∧
      Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2,
    ∀ x, 2 * spatialTrimMargin τ N x ≤ N x := by
  intro r hSize hRank W widths bases density Z
  let K := preparedModularCanonicalDetectorConstants m
  have hproj : r.Pproj = 4 * (Pmaster + 8) ^ 2 := rfl
  have hPproj : Pmaster ≤ r.Pproj := by
    nlinarith only [hproj, hMaster, sq_nonneg Pmaster]
  have h2Pproj : 2 * Pmaster ≤ r.Pproj := by
    nlinarith only [hproj, hMaster, sq_nonneg Pmaster]
  have hframeProj : (2 * Pmaster + 1) * Pmaster ≤ r.Pproj := by
    nlinarith only [hproj, hMaster, sq_nonneg Pmaster]
  have hExp := Real.exp_le_exp.mpr hPproj
  have hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ 2 * Pmaster :=
    (preparedModularDetector_variable_count B
      (fun j : Fin m => boundedBooleanJetRows (Fin 1) (j.val + 1)) hd).trans (by linarith only [hD])
  have hframe : (Fintype.card (Option (LayerSamplerVariables G I n B) × Fin nX) : ℝ) ≤ r.Pproj := by
    rw [Fintype.card_prod, Fintype.card_option, Fintype.card_fin, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    exact (mul_le_mul (add_le_add_left hvars 1) hnX (Nat.cast_nonneg _) (by positivity)).trans
      (by simpa only [add_comm] using hframeProj)
  obtain ⟨hI, hn⟩ := preparedModularDetector_layer_axes B
    (fun j : Fin m => boundedBooleanJetRows (Fin 1) (j.val + 1)) hd
  have hJ (j : Fin m) : (Fintype.card (J j) : ℝ) ≤ r.Pproj :=
    (Nat.cast_le.mpr (allocatedAmbientDimension_le_axes U basis o j)).trans
      (hd.axes.trans (hD.trans hPproj))
  have hW := allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)
  have hWproj : W ≤ Real.exp r.Pproj :=
    (preparedModularDetector_physical_root B
      (fun j : Fin m => boundedBooleanJetRows (Fin 1) (j.val + 1)) U basis S hd hD hLP).trans
        (Real.exp_le_exp.mpr (by nlinarith only [hproj, hMaster, sq_nonneg Pmaster]))
  have bounds := ((Classical.choose_spec
    (exists_preparedModularCanonicalDetector_resource_budget K)).2 Pmaster hMaster).1
  have hRequired := (preparedModularCanonicalDetector_required_bounds K hMaster).2.2.2.2
  have hFull : (max r.Pproj r.E + K.Amarginal) ^ K.Amarginal ≤ r.required := by
    apply le_trans _ hRequired
    apply pow_le_pow_left₀
      (add_nonneg (le_max_of_le_left bounds.Pproj.1) (Nat.cast_nonneg _))
    exact add_le_add
      (max_le (le_add_of_nonneg_right bounds.E.1) (le_add_of_nonneg_left bounds.full.1)) le_rfl
  exact allocated_fullBox_positive_law_at_model_budget m B U basis S hb o μ ν hR hσ hσ1
    C V hC hV Cinv hCinv hchart hsmall
    (P := r.Pproj) (E := r.E) (hMaster.trans hPproj) (hd.degree.trans (hD.trans hPproj))
    (hvars.trans h2Pproj) (by simpa only [Fintype.card_fin] using hnX.trans hPproj) hframe
    (fun j => (hRP j).trans hExp) (fun j => (hσP j).trans hExp)
    (fun j => (hd.coefficients j).trans (hD.trans hPproj))
    (fun j => (hI j).trans (hD.trans hPproj)) (fun j => (hn j).trans (hD.trans hPproj)) hJ
    ((hd.profile.trans (hD.trans hPproj)).trans (by linarith [Real.add_one_le_exp r.Pproj]))
    (hLP.trans hExp) (fun j => (hCP j).trans hExp) (fun j => (hVP j).trans hExp)
    p hp hm stride hs (fun d => (hsP d).trans hExp) hW hWproj le_rfl
    hτ (hτP.trans hExp) hτhalf (by simpa only [Fintype.card_fin] using hτdim)
    hξ hξ1 (hξP.trans hExp) N
    (fun d => (Real.exp_le_exp.mpr hFull).trans (hSize d)) hrank
    ((Real.exp_le_exp.mpr hFull).trans hRank) cells hCells

end Erdos3.VectorPolynomial

end

end OAI
