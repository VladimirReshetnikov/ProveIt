import OAI.Combinatorics.Progressions.Estimates.AllocatedCanonicalSliceConstructedFiniteSource
import OAI.Combinatorics.Progressions.Estimates.AllocatedCanonicalUniformCoarseSource

namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uG uI uB uJ

open Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {s nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin (s + 1)) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin (s + 1))))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin (s + 1))))

variable {T : Type*} [Fintype T] (a : T → ℂ)
variable (f : T → Finset (Fin (s + 1)) → (LayerSamplerAxis I n → ℝ) → ℂ)
local notation "LongSpace" => ((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle))
local notation "GridSpace" => ((Σ j, J j) → UnitAddCircle)

variable (p : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

variable (spatialModulus : ℕ) [NeZero spatialModulus] (stride N : (Fin nX) → ℕ)
local notation "refined" => residueRefinedPeriod spatialModulus stride
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod refined)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod spatialModulus stride)) → PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1))
  (allocatedPrincipalSides B U b S))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod spatialModulus stride)) {M : ℕ} (hM : 0 < M) (selection : Fin (s + 1) ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable {W τ ξ mesh : ℝ} (hW : 0 ≤ W) (base : (Fin nX) → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
local notation "window" => spatialWindow (α := Fin (s + 1)) (trimmedSpatialRootScale τ N stride) 4
local notation "widths" => narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
local notation "reconstruct" => allocatedWholeResidueReconstruction B U b S (Fin nX) spatialModulus stride wholeReference x base label
local notation "volume" => ∏ z, ∏ i, physicalSpatialOutputScale (Fin (s + 1))
  (trimmedSpatialRootScale τ N stride z) (trimmedSpatialSlopeScale W τ N stride z) S.value i
local notation "terms" => ((Fin nX) → SpatialSiteLabel (Fin (s + 1)) spatialModulus 4 mesh)
local notation "twist" => allocatedRecenteredSpatialTwist (τ := τ) B U b S (Fin nX) spatialModulus stride wholeReference x N mesh base label

variable [∀ i, NeZero (N i)]
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (wholeReference label)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (wholeReference label)
local notation "windowMask" => (fun acell : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride =>
  physicalResidueWindowSiteMask root dirs base
    (boundedColumnResidueRepresentative stride acell) stride (trimmedSpatialRootScale τ N stride) 4)
attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem AllocatedModelPhysicalExpansionIdentity.exists_uniform_canonical_normalized_native_model_of_positive_source
    (g : (Finset (Fin (s + 1)) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
      T → (∀ a, (e a).Term) → Finset (Fin (s + 1)) → LongSpace × GridSpace → ℂ)
    (hidentity : AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm g)
    {L : ℝ≥0} (hg : ∀ label i k site, LipschitzWith L (g label i k site))
    (hgb : ∀ label i k site z, ‖g label i k site z‖ ≤ 1)
    {Nt V Cc Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {Lg : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a))
    (Vmax : ℝ≥0) (hVmax : ∀ a, V a ≤ Vmax)
    (hstride : ∀ z, 0 < stride z)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hV : ∀ z, 0 < widths z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z)
    (signal : ((Fin nX) → ℤ) → ℂ)
    (hsignal : ∀ u ∈ integerBox N, ‖signal u‖ ≤ 1)
    (hzero : ∀ u, u ∉ integerBox N → signal u = 0)
    (hτ : 0 < τ)
    {pGain Emodel Espatial Pvolume : ℝ}
    (hpGain : 0 ≤ pGain) (hEmodel : 0 ≤ Emodel) (hEspatial : 0 ≤ Espatial)
    (hPvolume : 0 ≤ Pvolume)
    (hdim : (nX : ℝ) ≤ pGain + 8 + Emodel + Espatial + Pvolume)
    (hmass : (∑ label : Finset (Fin (s + 1)) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i, ∑ k,
      ‖((2 : ℂ) ^ Fintype.card (Finset (Fin (s + 1))) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) *
        coverSiteCoefficient e k‖) ≤ Real.exp Emodel)
    (hpositive : Real.exp (-(pGain + 8)) ≤ (allocatedRecenteredFiniteModelSource (τ := τ) (ξ := ξ) (mesh := mesh)
      B U b S x y₀ q d period r hr hb o bW e a f p hm spatialModulus stride N wholeReference label
      hM selection hx hW base cells (integerSelfSiteTest (s + 1) signal)).re)
    {pGeometry Ecoarse analytic : ℝ}
    (hpGeometry : 0 ≤ pGeometry) (hEcoarse : 0 ≤ Ecoarse) (hanalytic : 0 ≤ analytic)
    (hGGeometry : (Fintype.card G : ℝ) ≤ pGeometry)
    (hXGeometry : (nX : ℝ) ≤ pGeometry) (hdimGeometry : ((s + 2 : ℕ) : ℝ) ≤ pGeometry)
    (hMGeometry : (M : ℝ) ≤ Real.exp pGeometry)
    (hWGeometry : W ≤ Real.exp pGeometry * S.value)
    (hvolumeLog : allocatedAmbientNormalizationLog (s + 1) (nX : ℝ) pGeometry pGeometry pGeometry ≤ Pvolume)
    (hcanonical : spatialModulus = kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hx m))
    (hspatialLog : coarseSpatialPartitionLog (allocatedEarlyCoarseInput m (s + 1) (pGeometry + Ecoarse)) ≤ Espatial)
    (hmeshEarly : mesh = allocatedEarlyRecenteredMesh (Fin nX) selection M spatialModulus pGeometry Ecoarse)
    (hstrideGeometry : ∀ i, (stride i : ℝ) ≤ Real.exp pGeometry)
    (hτGeometry : 1 / τ ≤ Real.exp pGeometry)
    (hLanalytic : ((L * (period * Vmax ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a}) : ℝ≥0) : ℝ) ≤ Real.exp analytic)
    {Bbudget : ℝ} (hBbudget : 0 ≤ Bbudget)
    (hGeometryBudget : pGeometry ≤ Bbudget) (hCoarseBudget : Ecoarse ≤ Bbudget)
    (hAnalyticBudget : analytic ≤ Bbudget) (hGainBudget : pGain ≤ Bbudget)
    (hMassBudget : Emodel ≤ Bbudget) (hSpatialBudget : Espatial ≤ Bbudget)
    (hVolumeBudget : Pvolume ≤ Bbudget)
    (hCoverBudget : (period : ℝ) * (Vmax : ℝ) ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} ≤ Real.exp Bbudget) :
    let Anorm := Classical.choose (exists_allocatedRecenteredFactor_normalization.{uG,uI,uB,uJ,0,uJ} m (s + 1))
    let Anative := Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s)
    let A := Classical.choose (exists_normalizedNative_uniform_budget m Anorm Anative)
    let budget := (Bbudget + A) ^ A
    ∃ twistData : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
      (Real.exp budget) (Real.exp budget) ⟨Real.exp budget, Real.exp_nonneg _⟩,
      ∃ Fnative : integerBox N → ℂ,
        Nonempty (NativeSampleModel (fun _ : Fin nX => 1) s budget
          (fun u : integerBox N => u.val) Fnative) ∧
        Real.exp (-budget) ≤
          ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) (integerBox_nonempty N)).correlation
            (fun u => signal u.val) (fun u => star (twistData.eval N p u.val) * Fnative u)‖ := by
  intro Anorm Anative A budget
  have hnumeric := (Classical.choose_spec (exists_normalizedNative_uniform_budget m Anorm Anative)).2
    hBbudget ⟨hpGeometry, hGeometryBudget⟩ ⟨hEcoarse, hCoarseBudget⟩ ⟨hanalytic, hAnalyticBudget⟩
    ⟨hpGain, hGainBudget⟩ ⟨hEmodel, hMassBudget⟩ ⟨hEspatial, hSpatialBudget⟩ ⟨hPvolume, hVolumeBudget⟩
    (le_refl Bbudget) (hXGeometry.trans hGeometryBudget)
  have hvolume := (physicalAmbientVolume_log_bound (s + 1) N stride hW
    (by exact_mod_cast Nat.succ_le_of_lt S.positive : (1 : ℝ) ≤ S.value)
    hpGeometry hpGeometry hpGeometry hWGeometry
    (by simp only [Fintype.card_fin]; exact le_rfl : (Fintype.card (Fin nX) : ℝ) ≤ nX)
    (fun i => Nat.pos_of_ne_zero (NeZero.ne (N i))) hstride hτ hstrideGeometry hτGeometry).2
  have hvolumeRatio : (integerBoxCubeCount N (s + 1) : ℝ) / volume ≤ Real.exp Pvolume :=
    hvolume.trans (Real.exp_le_exp.mpr hvolumeLog)
  have hmodulusGeometry : spatialModulus ≤ M ^ (m + 1) := by
    rw [hcanonical]
    exact kernelPeriodCandidate_le _ _
  have hperiod : integerScalarLattice (Unit ⊕ Fin (s + 1)) (spatialModulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection) := by
    rw [hcanonical]
    exact (goodKernelUniformCandidate_spec.{0,uG,0} selection x hx m).1 _
  have hpartition := allocatedEarlyRecenteredMesh_partition_budget m (Fin nX) selection
    hpGeometry hEcoarse hGGeometry (by simpa using hXGeometry) hM hMGeometry hmodulusGeometry
  rw [← hmeshEarly] at hpartition
  have hmargin : 3 + 2 * mesh ≤ 4 := by linarith only [hpartition.2.1]
  have hspatial := hpartition.2.2.2.trans (Real.exp_le_exp.mpr hspatialLog)
  have hgain := slicedSource_selected_gain_exp (δ := Real.exp (-(pGain + 8)))
    (Cmodel := Real.exp Emodel) (Cspatial := Real.exp Espatial) le_rfl
    (Real.exp_pos _) (Real.exp_pos _) le_rfl le_rfl
  obtain ⟨cover, hcover, hcoverBound, F, hF, hFb, cell, t, hψ, Vnative, hVnative, hcorrelation⟩ :=
    hidentity.exists_native_source B U b S x y₀ q d period r hr hb o bW e a f p hm
      spatialModulus stride N wholeReference label hM selection hx hW base cells g hg hgb he Vmax hVmax
      hstride hpartition.1 hmargin hbudget hperiod hV hZ signal hsignal hzero hτ
      (show 0 ≤ pGain + 8 + Emodel + Espatial by positivity) hPvolume hdim hvolumeRatio
      (Real.exp_pos _) (Real.exp_pos _) (Real.exp_pos _) hmass hspatial hpositive hgain
  have hN (i) : 0 < N i := Nat.pos_of_ne_zero (NeZero.ne (N i))
  obtain ⟨hperiodPos, hperiodBound, mask, H, hmask, hH, hLip, hfactor⟩ :=
    (Classical.choose_spec (exists_allocatedRecenteredFactor_normalization.{uG,uI,uB,uJ,0,uJ} m (s + 1))).2
      B U b S selection hpGeometry hEcoarse hanalytic hGGeometry
      (by simpa only [Fintype.card_fin] using hXGeometry) hdimGeometry hM hMGeometry hmodulusGeometry
      ⟨mesh, hpartition.1.le⟩ hmeshEarly stride N hN hstride hstrideGeometry hτ hτGeometry
      wholeReference x base label cell.val t ∅ (F ∅) (hF ∅) (hFb ∅) hLanalytic
  let twistData : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
      (Real.exp (((m + 1 : ℕ) : ℝ) * pGeometry + Fintype.card (Fin nX) * pGeometry))
      (period * (Vmax : ℝ) ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a})
      ⟨Real.exp ((pGeometry + Ecoarse + analytic + Anorm) ^ Anorm), Real.exp_nonneg _⟩ := {
    modulus := residueRefinedPeriod spatialModulus stride
    modulus_pos := hperiodPos
    modulus_bound := hperiodBound
    cover := cover
    cover_pos := hcover
    cover_bound := hcoverBound
    mask := mask
    mask_bound := hmask
    smooth := H
    smooth_bound := hH
    smooth_lipschitz := hLip }
  have heq (u : (Fin nX) → ℤ) :
      twist cell.val t ∅ u * F ∅ (physicalGridFactorInput cover p (fun i => (u i : ℝ))) =
        twistData.eval N p u := hfactor u _
  let Vnormalized : NativeSampleCorrelation (fun _ : Fin nX => 1) s
      ((pGain + 8 + Emodel + Espatial + Pvolume + 2) ^ Anative)
      (integerBox N) id (fun u => signal u * twistData.eval N p u) :=
    { Vnative with correlation := by simpa only [heq] using Vnative.correlation }
  obtain ⟨Fnative, hmodel, hcorr⟩ := nativeCorrelation_restrict_model
    (integerBox N) (integerBox_nonempty N) (fun _ : Fin nX => 1) s _ id
    signal (twistData.eval N p) Vnormalized hVnative
  apply normalized_native_detection_mono N p (fun u : integerBox N => u.val)
    (FiniteProbabilityWeights.uniformFinset (integerBox N) (integerBox_nonempty N))
    (fun u => signal u.val) s ?_ ?_ ?_ hnumeric.2.2.2 ⟨twistData, Fnative, hmodel, hcorr⟩
  · apply Real.exp_le_exp.mpr
    simpa only [Fintype.card_fin] using hnumeric.1
  · exact hCoverBudget.trans (Real.exp_le_exp.mpr hnumeric.2.1)
  · exact Real.exp_le_exp.mpr hnumeric.2.2.1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uG uI uB uJ

open Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {s nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin (s + 1)) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin (s + 1))))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

local notation "LongSpace" => ((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle))
local notation "GridSpace" => ((Σ j, J j) → UnitAddCircle)

variable (p : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

variable (spatialModulus : ℕ) [NeZero spatialModulus] (stride N : (Fin nX) → ℕ)
local notation "refined" => residueRefinedPeriod spatialModulus stride
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod refined)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod spatialModulus stride)) → PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1))
  (allocatedPrincipalSides B U b S))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod spatialModulus stride)) {M : ℕ} (hM : 0 < M) (selection : Fin (s + 1) ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable {W τ ξ mesh : ℝ} (hW : 0 ≤ W) (base : (Fin nX) → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
local notation "window" => spatialWindow (α := Fin (s + 1)) (trimmedSpatialRootScale τ N stride) 4
local notation "widths" => narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
local notation "reconstruct" => allocatedWholeResidueReconstruction B U b S (Fin nX) spatialModulus stride wholeReference x base label
local notation "volume" => ∏ z, ∏ i, physicalSpatialOutputScale (Fin (s + 1))
  (trimmedSpatialRootScale τ N stride z) (trimmedSpatialSlopeScale W τ N stride z) S.value i
local notation "terms" => ((Fin nX) → SpatialSiteLabel (Fin (s + 1)) spatialModulus 4 mesh)
local notation "twist" => allocatedRecenteredSpatialTwist (τ := τ) B U b S (Fin nX) spatialModulus stride wholeReference x N mesh base label

variable [∀ i, NeZero (N i)]
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (wholeReference label)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (wholeReference label)
local notation "windowMask" => (fun acell : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride =>
  physicalResidueWindowSiteMask root dirs base
    (boundedColumnResidueRepresentative stride acell) stride (trimmedSpatialRootScale τ N stride) 4)
attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_allocatedCanonical_finite_source_native
    (signal : ((Fin nX) → ℤ) → ℂ)
    (hsignal : ∀ u ∈ integerBox N, ‖signal u‖ ≤ 1)
    (hzero : ∀ u, u ∉ integerBox N → signal u = 0)
    (hstride : ∀ z, 0 < stride z) (hτ : 0 < τ) (hξ : 0 < ξ)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hZmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z)
    {P D pgrid v Fmodel Prho Pk target Banalytic pGeometry Ecoarse pGain : ℝ}
    (hP : 0 ≤ P) (hD : D ∈ Icc 0 P) (hgrid : pgrid ∈ Icc 0 P) (hv : v ∈ Icc 0 P)
    (hFmodel : Fmodel ∈ Icc 0 P) (hPrho : Prho ∈ Icc 0 P) (hPk : Pk ∈ Icc 0 P)
    (htarget : target ∈ Icc 0 P) (hBanalytic : Banalytic ∈ Icc 0 P)
    (hGeometry : pGeometry ∈ Icc 0 P) (hEcoarse : Ecoarse ∈ Icc 0 P)
    (hpGain : pGain ∈ Icc 0 P)
    (hGGeometry : (Fintype.card G : ℝ) ≤ pGeometry)
    (hXGeometry : (nX : ℝ) ≤ pGeometry) (hdimGeometry : ((s + 2 : ℕ) : ℝ) ≤ pGeometry)
    (hMGeometry : (M : ℝ) ≤ Real.exp pGeometry)
    (hWGeometry : W ≤ Real.exp pGeometry * S.value)
    (hcanonical : spatialModulus = kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hx m))
    (hmeshEarly : mesh = allocatedEarlyRecenteredMesh (Fin nX) selection M spatialModulus pGeometry Ecoarse)
    (hstrideGeometry : ∀ i, (stride i : ℝ) ≤ Real.exp pGeometry)
    (hτGeometry : 1 / τ ≤ Real.exp pGeometry)
    {gain Z Pproj coarseTarget lossTarget Op Hgrid : ℝ}
    (hgain : Real.exp (-pGain) / 2 ≤ gain) (hZ : 1 / 2 ≤ Z)
    (hPproj : pGain + 32 ≤ Pproj) (hcoarseTarget : pGain + 32 ≤ coarseTarget)
    (hEcoarseGain : pGain + 32 ≤ Ecoarse) (hlossTarget : pGain + 32 ≤ lossTarget) :
    let Amass := Classical.choose (exists_allocatedAffineModelMass_budget m (s + 1))
    let Aanalytic := Classical.choose (exists_allocatedAffineAnalytic_budget m (s + 1))
    let Emodel := (D + pgrid + v + Fmodel + Prho + Pk + target + Amass) ^ Amass
    let analytic := (D + pgrid + v + Fmodel + Prho + Pk + target + Banalytic + Aanalytic) ^ Aanalytic
    let Vgrid : ℝ≥0 := ⟨Real.exp Op, Real.exp_nonneg _⟩
    (∃ e : {a // grid a} → ScalarSiteExpansion.{0,0} (Finset (Fin (s + 1))),
      (∀ z, (e z).Bounds (Real.exp Op) (Real.exp Op) (Real.exp Op) Vgrid (Real.exp Hgrid)) ∧
      ∃ k : ℕ, ∃ (a : (Finset (Fin (s + 1)) × LayerSamplerAxis I n → Fin k) → ℂ)
        (f : (Finset (Fin (s + 1)) × LayerSamplerAxis I n → Fin k) →
          Finset (Fin (s + 1)) → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ label : Finset (Fin (s + 1)) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)),
          ∑ i, ∑ kg, ‖((2 : ℂ) ^ Fintype.card (Finset (Fin (s + 1))) *
            allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) *
            coverSiteCoefficient e kg‖) ≤ Real.exp Emodel ∧
        (∃ Lanalytic : ℝ≥0,
          ((Lanalytic * ((period : ℝ≥0) * Vgrid ^ Fintype.card {a // grid a}) : ℝ≥0) : ℝ) ≤
            Real.exp analytic ∧
          (period : ℝ) * (Real.exp Op) ^ Fintype.card {a // grid a} ≤ Real.exp analytic ∧
          ∃ analyticFactor : (Finset (Fin (s + 1)) → ((∀ j, Fin (n j) → ZMod period) ×
              (∀ j, E j → ZMod period))) →
              (Finset (Fin (s + 1)) × LayerSamplerAxis I n → Fin k) → (∀ z, (e z).Term) →
              Finset (Fin (s + 1)) → LongSpace × GridSpace → ℂ,
            (∀ label i kg site, LipschitzWith Lanalytic (analyticFactor label i kg site)) ∧
            (∀ label i kg site z, ‖analyticFactor label i kg site z‖ ≤ 1) ∧
            AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm analyticFactor) ∧
        Z * (gain - Real.exp (-Pproj) - Real.exp (-coarseTarget)) -
          Real.exp (-Ecoarse) - Real.exp (-lossTarget) ≤
          (∑ z : cells × window, (selectedResidueCellWeight stride cells widths z.1 : ℂ) *
            allocatedRecenteredResidueWeight (τ := τ) B U b S (Fin nX) spatialModulus stride wholeReference x hM selection hx
              N hW mesh base cells (physicalCubeSiteTest (integerSelfSiteTest (s + 1) signal)) label z.1 z.2.val *
            (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f
              (physicalCubeRowSample U d rows p hm (reconstruct z.1.val z.2.val)) *
            allocatedFullGridChartModel B U b S rowSets d hb o bW e
              (physicalCubeRowSample U d rows p hm (reconstruct z.1.val z.2.val)))).re) →
    let C := Classical.choose (exists_canonicalSlicedNative_input_budget m (s + 1) Amass Aanalytic)
    let Bbudget := (P + C) ^ C
    let Anorm := Classical.choose (exists_allocatedRecenteredFactor_normalization.{uG,uI,uB,uJ,0,uJ} m (s + 1))
    let Anative := Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s)
    let A := Classical.choose (exists_normalizedNative_uniform_budget m Anorm Anative)
    let budget := (Bbudget + A) ^ A
    ∃ twistData : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
      (Real.exp budget) (Real.exp budget) ⟨Real.exp budget, Real.exp_nonneg _⟩,
      ∃ Fnative : integerBox N → ℂ,
        Nonempty (NativeSampleModel (fun _ : Fin nX => 1) s budget
          (fun u : integerBox N => u.val) Fnative) ∧
        Real.exp (-budget) ≤
          ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) (integerBox_nonempty N)).correlation
            (fun u => signal u.val) (fun u => star (twistData.eval N p u.val) * Fnative u)‖ := by
  intro Amass Aanalytic Emodel analytic Vgrid hconstructed C Bbudget Anorm Anative A budget
  let Espatial := coarseSpatialPartitionLog (allocatedEarlyCoarseInput m (s + 1) (pGeometry + Ecoarse))
  let Pvolume := (nX : ℝ) + allocatedAmbientNormalizationLog (s + 1) (nX : ℝ) pGeometry pGeometry pGeometry
  obtain ⟨hPB, hmassB, hanalyticB, hspatialB, hvolumeB, hvolumeLog, hdim⟩ :=
    (Classical.choose_spec (exists_canonicalSlicedNative_input_budget m (s + 1) Amass Aanalytic)).2
      hP hD hgrid hv hFmodel hPrho hPk htarget hBanalytic hGeometry hEcoarse hpGain
      (hXGeometry.trans hGeometry.2)
  obtain ⟨e, he, k, a, f, hmass, hphysical, hsource⟩ := hconstructed
  obtain ⟨Lanalytic, hLanalytic, hCover, analyticFactor, hLip, hbounded, hidentity⟩ := hphysical
  have hpositive : Real.exp (-(pGain + 8)) ≤ (allocatedRecenteredFiniteModelSource (τ := τ) (ξ := ξ) (mesh := mesh)
      B U b S x y₀ q d period r hr hb o bW e a f p hm spatialModulus stride N wholeReference label
      hM selection hx hW base cells (integerSelfSiteTest (s + 1) signal)).re :=
    canonicalSlicedSource_transfer_exp hgain hZ hPproj hcoarseTarget hEcoarseGain hlossTarget hsource
  have hN (i) : 0 < N i := Nat.pos_of_ne_zero (NeZero.ne (N i))
  have hwidths : ∀ z, 0 < widths z := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
  exact hidentity.exists_uniform_canonical_normalized_native_model_of_positive_source
    B U b S x y₀ q d period r hr hb o bW e a f p hm
    spatialModulus stride N wholeReference label hM selection hx hW base cells
    analyticFactor hLip hbounded he Vgrid (fun _ => le_rfl)
    hstride hbudget hwidths hZmass signal hsignal hzero hτ
    hpGain.1 hmassB.1 hspatialB.1 hvolumeB.1 hdim hmass hpositive
    hGeometry.1 hEcoarse.1 hanalyticB.1 hGGeometry hXGeometry hdimGeometry hMGeometry hWGeometry
    hvolumeLog hcanonical (le_refl Espatial) hmeshEarly hstrideGeometry hτGeometry hLanalytic
    (hP.trans hPB) (hGeometry.2.trans hPB) (hEcoarse.2.trans hPB) hanalyticB.2 (hpGain.2.trans hPB)
    hmassB.2 hspatialB.2 hvolumeB.2 (hCover.trans (Real.exp_le_exp.mpr hanalyticB.2))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uG uI uB uJ uQ uX₀
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {s nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin (s + 1))))
variable (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (selection : Fin (s + 1) ↪ G)
variable (hgood : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
variable {X₀ : Type uX₀} [Fintype X₀] (stride₀ : X₀ → ℕ)
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => selectedRows
local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => degree (Subtype.val a))
local notation "L" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)
local notation "positiveLengths" => (fun j : Tuple => allocatedPrincipalSides_pos B U basis S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

variable (Q : Fin m → Type uQ) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "source" => allocatedCoefficientSource B U basis hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U basis hR hσ S
local notation "reference" => allocatedLongJetReference B U basis S jetRows
variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ)
variable (hcanonical : modulus = canonicalSlicedModulus (M := Mk) selection stride₀ m x)
variable (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := (Fin (s + 1))) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))
local notation "H" => (fun j : Tuple => H₀ (embed j))
local notation "step" => (fun j : Tuple => step₀ (embed j))
local notation "c" => (fun j : Tuple => c₀ (embed j))
local notation "hsubset" => (fun j : Tuple => hsubset₀ (embed j))
local notation "residue" => (fun j : Tuple => r₀ (embed j))
local notation "GridTuples" => PrincipalAxisTuples (α := (Fin (s + 1))) grid (allocatedPrincipalSides B U basis S)
local notation "wholeLaw" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell grid
local notation "wholeRoot" y => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y
local notation "wholeDirs" y => allocatedPhysicalCubeDirections B U basis S x y
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
local notation "jetHaar" => Measure.pi (fun j =>
  @Measure.pi (selectedRows j) _ (fullBooleanRowSetFintype (s + 1) (Fin.val j + 1)) _
    (fun _ : selectedRows j => ν j))
local notation "density" => allocatedCoefficientDensity B U basis hb o hR hσ S
local notation "cover" => quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d

variable [CompactSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (s + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

include bW hcanonical μrows hR hσ hMk hgood hP hMkP hRP hRi hσi hcount in

theorem exists_allocatedCanonicalSlice_constructed_native_source
    {D target Pk Prho F Qstride : ℝ}
    (hdimensions : AllocatedComparisonDimensions (G := G) B (Fin (s + 1)) selectedRows D)
    (hPk : 0 ≤ Pk) (hMkPk : (Mk : ℝ) ≤ Real.exp Pk)
    (hPrho : 0 ≤ Prho) (htarget : 0 ≤ target) (hF : 0 ≤ F) (hQstride : 0 ≤ Qstride)
    (hstride₀ : ∀ i, 0 < stride₀ i) (hstrideBound : ∀ i, (stride₀ i : ℝ) ≤ Real.exp Qstride)
    (hlength : Real.exp (allocatedAffineLengthLog m D P Prho Pk target F (((m + 1 : ℕ) : ℝ) * Pk + Fintype.card X₀ * Qstride)) ≤ S.value)
    (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U basis S) →
  EuclideanJetLayers U selectedRows → ℝ)
    (hgm : ∀ y, Measurable (g y)) (hg0 : ∀ y z, 0 ≤ g y z)
    (hgi : ∀ y, Integrable (g y) jetHaar)
    (hglaw : ∀ y, (realDensityMeasure μ (fun z => density (cover z))).map
  (euclideanCoefficientJetMap U (wholeRoot y) (wholeDirs y) rows) = realDensityMeasure jetHaar (g y))
    {δ η : ℝ} (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0) (t : ℝ) (htone : t ≤ 1)
    (hs : AllocatedAffineCoveredComparison.{uJ, uQ, _, _, _, _, _} (G := G) B rows δ η ρ t htone)
    (hρ : 0 < ρ grid) (hρ1 : ρ grid ≤ 1)
    (hσsmall : ∀ j, σ j ≤ t)
    (hstep : ∀ j : Tuple, 0 < step j)
    (hδ : 0 < δ) (hδF : δ⁻¹ ≤ Real.exp F)
    (hdense : ∀ j : Tuple, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (hq : Fintype.card (Fin (s + 1)) ≤ m + 1)
    (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U basis S))
    (hy₀ : 0 < (wholeLaw).weight y₀)
    (T : Fin m → ℝ) (hT : ∀ j, partitionedIdealRadius (Fin (s + 1)) m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card (Fin (s + 1)) * ((Fintype.card (Fin (s + 1)) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4)
    (hρlog : (ρ grid : ℝ)⁻¹ ≤ Real.exp Prho)
    (hη0 : 0 ≤ η)
    (hηsmall : η ≤ Real.exp (-(target + 1 + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 4)))
    (period : ℕ) [NeZero period]
    (hperiodCanonical : period = kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hgood m))
    (hdiv : period ∣ d) (siteRadius : ℝ≥0) (hrone : 1 ≤ siteRadius)
    (hsitebudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin (s + 1))) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (siteRadius : ℝ) * R j)))) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (hradius : ∀ j, (rowSets j).card * T j ≤ (siteRadius : ℝ))
    {Pbox Vlog Nlog Mlog baseAmbient : ℝ}
    (hPbox : 0 ≤ Pbox) (hVlog : 0 ≤ Vlog) (hNlog : 0 ≤ Nlog) (hMlog : 0 ≤ Mlog)
    (hbox : 2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp Pbox)
    (hvolume : allocatedFullGridNaturalVolume B U basis S rowSets ≤ Real.exp Vlog)
    (hnormalizer : ‖((allocatedProductIdealNormalizer B U basis S rowSets : ℝ) : ℂ)⁻¹‖ ≤ Real.exp Nlog)
    (hmask : (layerKernelIndexBound m Mk : ℝ) ^ Fintype.card (LayerSamplerAxis I n) *
      coefficientDeckPeriodCap selectedRows Q period ≤ Real.exp Mlog)
    (hbaseAmbient : 0 ≤ baseAmbient)
    (hvbase : Vlog ≤ baseAmbient) (hnbase : Nlog ≤ baseAmbient) (hmbase : Mlog ≤ baseAmbient)
    (hsites : (Fintype.card (Finset (Fin (s + 1))) : ℝ) ≤ baseAmbient)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ baseAmbient)
    (hlabels : (Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, Q j → ZMod period)) : ℝ) ≤ Real.exp baseAmbient)
    (hKbase : (K : ℝ) ≤ Real.exp baseAmbient)
    (hcoords : ((∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp baseAmbient)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp baseAmbient)
    (hdbase : (d : ℝ) ≤ Real.exp baseAmbient) (hpbase : (period : ℝ) ≤ Real.exp baseAmbient)
    (hrowsAmbient : ((∑ j : Fin m, ((rowSets j).card : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp baseAmbient)
    (houtputs : (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1) : ℝ) ≤ baseAmbient)
    (hheight : (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp baseAmbient)
    (Qgrid : ℝ≥0) (hQgrid : ∀ a : {a // allocatedGridAxis (I := I) U basis S.value a},
      8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
        (allocatedGridIntegerAxis B U basis S a).1 (allocatedGridIntegerAxis B U basis S a).2) : ℝ) + 1) ≤ Qgrid)
    {δg : ℝ} (hδg : 0 < δg)
    (hdenseg : ∀ tg, δg * allocatedPrincipalSides B U basis S tg ≤ (H₀ tg : ℝ))
    (Tg : ℕ) (hQTg : (((Fintype.card (Fin (s + 1)) + 1) * modulus : ℕ) : ℝ) / δg ≤ Tg)
    (hstepAll : ∀ tg, 0 < step₀ tg)
    (Ag : ℝ≥0) (hAg : LipschitzWith Ag Real.smoothTransition) (Pg : ℝ) (hPg : 1 ≤ Pg)
    (hcP : scalarCubePrimitiveEnvelope Empty Ag 16 (128 * probabilityProfileLipschitz) 1 ≤ Pg)
    (hsP : scalarCubePrimitiveEnvelope (Fin (s + 1)) Ag 1 0 modulus ≤ Pg)
    (hstrideGrid : ∀ tg, ((step₀ tg * modulus : ℕ) : ℝ) ≤ Pg)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    {Dg vg wg tg pg : ℝ}
    (hDg : 0 ≤ Dg) (hvg : 0 ≤ vg) (hwg : 0 ≤ wg) (htg : 0 ≤ tg) (hpg : 0 ≤ pg)
    (hcube : (Fintype.card (Fin (s + 1)) : ℝ) ≤ Dg) (hdegree : ∀ j : Fin m, ((j.val + 1 : ℕ) : ℝ) ≤ Dg)
    (hrowsD : ∀ j : Fin m, ((boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card : ℝ) ≤ Dg)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ Dg)
    (hblocks : ∀ j i, (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ Dg)
    (hRv : ∀ j, R j ≤ Real.exp vg) (hRiGrid : ∀ j, (R j)⁻¹ ≤ Real.exp vg)
    (hδw : δg⁻¹ ≤ Real.exp wg) (hTg : (Tg : ℝ) ≤ Real.exp tg)
    (hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp vg)
    (hPp₀ : Pg ≤ Real.exp pg) (haxesGrid : (Fintype.card {a // grid a} : ℝ) ≤ Dg)
    (hfullAxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ Dg)
    (hfullOutputs : (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1) : ℝ) ≤ Dg)
    (hambientCount : ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ Dg)
    (hprofileBudget : (probabilityProfileLipschitz : ℝ) ≤ Dg)
    {Banalytic : ℝ} (hBanalytic : 0 ≤ Banalytic) (hDanalytic : Dg ≤ Banalytic)
    (hcutoffAnalytic : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Banalytic)
    (hcoordAnalytic : ((K * ∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp Banalytic)
    (hgridAnalytic : (Qgrid : ℝ) ≤ Real.exp Banalytic)
    {Pnum : ℝ} (hPnum : 0 ≤ Pnum)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ Pnum) (hn : ∀ j, (n j : ℝ) ≤ Pnum)
    (hcoeffEarly : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pnum)
    (hRiEarly : ∀ j, (R j)⁻¹ ≤ Real.exp Pnum)
    (hVEarly : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Real.exp Pnum)
    {gain Z Pproj coarseTarget Ecoarse pGain : ℝ}
    :
    let ambientQ := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1)) (Fintype.card (Fin (s + 1)))
      (Pbox + Prho + Vlog + Nlog + Mlog + target)
    let ambientBudget := affineAmbientPrimitiveBudget baseAmbient ambientQ
    ∀ (spatialModulus : ℕ) [NeZero spatialModulus] (stride N : (Fin nX) → ℕ) [∀ i, NeZero (N i)],
    spatialModulus = period →
    let refined := residueRefinedPeriod spatialModulus stride
    modulus = refined →
    let labels := PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod refined
    let wholeReference : labels → PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1))
        (allocatedPrincipalSides B U basis S) := fun _ => y₀

    ∀ {W τ ξn mesh : ℝ} (hW : 0 ≤ W) (base : (Fin nX) → ℤ)
      (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
      (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
      (_hp : ∀ j, DegreeLE (1 : (Fin nX) → ℕ) (j.val + 1) (poly j))
      (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
      (signal : ((Fin nX) → ℤ) → ℂ),
    (∀ u ∈ integerBox N, ‖signal u‖ ≤ 1) →
    (∀ u, u ∉ integerBox N → signal u = 0) →
    let test := physicalCubeSiteTest (integerSelfSiteTest (s + 1) signal)
    let point := physicalCubeRowSample U d rows poly hmem
    let κ := Z * (gain - Real.exp (-Pproj) - Real.exp (-coarseTarget)) - Real.exp (-Ecoarse)
    ∀ {lossTarget Pphysical Dphysical Psample Rrank Sstride εsample ηsample : ℝ},
    (∀ i, 0 < stride i) → (∀ i, 0 < N i) → 0 < τ → 0 < mesh →
    allocatedPhysicalRootBudget B U basis S (fun _ => 0) ≤ W →
    κ ≤ ((wholeLaw).complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξn)
      B U basis S (Fin nX) spatialModulus stride wholeReference x hMk selection hgood N hW mesh base cells point test
      (fun y z => (g y z : ℂ)))).re →
    0 ≤ Psample → (Fintype.card (Fin nX) : ℝ) ≤ Psample →
    (Fintype.card (Option (Fin (s + 1)) × (Fin nX)) : ℝ) ≤ Psample →
    (d : ℝ) ≤ Real.exp Psample →
    0 ≤ Sstride → Sstride ≤ Real.exp Psample → 0 < εsample →
    1 / τ ≤ Real.exp Psample → 1 / εsample ≤ Real.exp Psample →
    (∀ i, (stride i : ℝ) ≤ Sstride) →
    let A := Classical.choose (exists_translated_physical_jet_l1_perturbation.{0,uJ,0} m (s + 1))
    (∀ i, Real.exp ((Psample + A) ^ A) ≤ (N i : ℝ)) →
    (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
    Real.exp ((Psample + A) ^ A) ≤ Rrank →
    ∀ (actual : (JetAmbientIndex selectedRows J → UnitAddCircle) → ℂ)
      (La Ca : ℝ≥0),
    LipschitzWith La actual → (∀ z, ‖actual z‖ ≤ Ca) →
    0 < ηsample → (Fintype.card (CoefficientAmbientIndex (Fin (s + 1)) J) : ℝ) ≤ Psample →
    (La : ℝ) ≤ Real.exp Psample → (Ca : ℝ) ≤ Real.exp Psample →
    ambientBudget ≤ Psample →
    ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin (s + 1)) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp Psample →
    ηsample⁻¹ ≤ Real.exp Psample →
    (∀ y, ((wholeLaw).mean (fun v => g v y) : ℂ) = actual (coveredJetAmbientTorus U 1 y)) →
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξn N
    (∀ z, 0 < V z) → (0 < ∑' z, selectedResidueSmoothWeight stride cells V z) →
    ∀ {ρphysical : ℝ}, ξn ≤ 1 →
    (∀ t, 8 * (1 + W) * (stride t : ℝ) * ρphysical ≤ (ξn * τ) * (N t : ℝ)) →
    8 * (probabilityProfileLipschitz : ℝ) ≤ ρphysical →
    2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U basis S (fun _ => 0))) ≤ ρphysical →
    0 ≤ Pphysical → (Mk : ℝ) ≤ Real.exp Pphysical →
    (spatialModulus : ℝ) ≤ Real.exp (Pphysical ^ 2) →
    (((s + 1) + 1 : ℕ) : ℝ) ≤ Pphysical → (Fintype.card G : ℝ) ≤ Pphysical →
    (Fintype.card (Fin nX) : ℝ) ≤ Pphysical → Dphysical ≤ Real.exp Pphysical →
    W ≤ Dphysical * S.value →
    lossTarget + coefficientErrorSpatialLog Pphysical + 8 ≤ target →
    ηsample ≤ Real.exp (-target) → εsample ≤ Real.exp (-target) →
    let Amass := Classical.choose (exists_allocatedAffineModelMass_budget m (s + 1))
    let Aanalytic := Classical.choose (exists_allocatedAffineAnalytic_budget m (s + 1))
    let Fmodel := (m * (2 : ℝ) ^ Fintype.card (Fin (s + 1))) * (Pnum + 8) * (1 + 4 * Pnum) +
      Fintype.card (LayerSamplerAxis I n) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (selectedRows j) * ((m + 1 : ℕ) * Pk))
    let p := slicedGridGeometryLog Dg vg wg tg + pg
    ∀ {Pnative : ℝ}, 0 ≤ Pnative →
    Dg ∈ Set.Icc 0 Pnative → p ∈ Set.Icc 0 Pnative → vg ∈ Set.Icc 0 Pnative →
    Fmodel ∈ Set.Icc 0 Pnative → Prho ∈ Set.Icc 0 Pnative → Pk ∈ Set.Icc 0 Pnative →
    target ∈ Set.Icc 0 Pnative → Banalytic ∈ Set.Icc 0 Pnative →
    Pphysical ∈ Set.Icc 0 Pnative → Ecoarse ∈ Set.Icc 0 Pnative → pGain ∈ Set.Icc 0 Pnative →
    0 < ξn →
    mesh = allocatedEarlyRecenteredMesh (Fin nX) selection Mk spatialModulus Pphysical Ecoarse →
    (∀ i, (stride i : ℝ) ≤ Real.exp Pphysical) →
    1 / τ ≤ Real.exp Pphysical →
    Real.exp (-pGain) / 2 ≤ gain → 1 / 2 ≤ Z →
    pGain + 32 ≤ Pproj → pGain + 32 ≤ coarseTarget →
    pGain + 32 ≤ Ecoarse → pGain + 32 ≤ lossTarget →
    let C := Classical.choose (exists_canonicalSlicedNative_input_budget m (s + 1) Amass Aanalytic)
    let Bbudget := (Pnative + C) ^ C
    let Anorm := Classical.choose (exists_allocatedRecenteredFactor_normalization.{uG,uI,uB,uJ,0,uJ} m (s + 1))
    let Anative := Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s)
    let A := Classical.choose (exists_normalizedNative_uniform_budget m Anorm Anative)
    let budget := (Bbudget + A) ^ A
    ∃ twistData : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
      (Real.exp budget) (Real.exp budget) ⟨Real.exp budget, Real.exp_nonneg _⟩,
      ∃ Fnative : integerBox N → ℂ,
        Nonempty (NativeSampleModel (fun _ : Fin nX => 1) s budget
          (fun u : integerBox N => u.val) Fnative) ∧
        Real.exp (-budget) ≤
          ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) (integerBox_nonempty N)).correlation
            (fun u => signal u.val) (fun u => star (twistData.eval N poly u.val) * Fnative u)‖ := by
  intro ambientQ ambientBudget spatialModulus _ stride N _ hspatialCanonical refined hmodulusRefined labels wholeReference
    W τ ξn mesh hW base cells poly hp hmem signal hsignal hzero test point κ
    lossTarget Pphysical Dphysical Psample Rrank Sstride εsample ηsample
    hstridepos hN hτ hmesh hrootbudget hpositive
    hPs hX hframe hdP hSstride hSstrideP hεsample hτP hεsampleP hstride A hsize hrank hRrank
    actual La Ca hLa hCa hηsample hamb hLaP hCaP hAmbientP hjet hηsampleP hactual
    V hV hZ ρphysical hξn1 hsizePhysical hρ8 hρshift
    hPphysical hMkPhysical hPeriodPhysical hDimPhysical hGPhysical hXPhysical hDPhysical hWL
    hprecision hηprecision hεprecision
    Amass Aanalytic Fmodel p
    Pnative hPnative hDnative hpNative hvNative hFnative hPrhoNative hPkNative htargetNative
    hBanalyticNative hphysicalNative hEcoarseNative hpGainNative hξn hmeshEarly hstrideGeometry hτGeometry
    hgain hZhalf hPproj hcoarseTarget hEcoarseGain hlossTarget
    Cbudget Bbudget Anorm Anative Abudget budget
  let r := principalResidueLabel refined y₀
  have hsignalAll (u) : ‖signal u‖ ≤ 1 := by
    by_cases hu : u ∈ integerBox N
    · exact hsignal u hu
    · simp only [hzero u hu, norm_zero, zero_le_one]
  have htest (v) : ‖test v‖ ≤ 1 :=
    physicalCubeSiteTest_norm_le _ (integerSelfSiteTest_norm_le (s + 1) signal hsignalAll) v
  have hconstructor := exists_allocatedCanonicalSlice_constructed_finite_source (dim := s + 1) (X := Fin nX)
      B U basis hR hσ S x hMk selection hgood stride₀ hP hMkP hRP hRi hσi hcount
      Q hb o bW d H₀ step₀ c₀ hH₀ hsubset₀ modulus hcanonical r₀ hcell ν μ μrows
      hdimensions hPk hMkPk hPrho htarget hF hQstride hstride₀ hstrideBound hlength
      g hgm hg0 hgi hglaw ρ t htone hs hρ hρ1 hσsmall hstep hδ hδF hdense hq
      y₀ hy₀ T hT hsource C hC hchart hbudget hρlog hη0 hηsmall
      period hperiodCanonical hdiv siteRadius hrone hsitebudget Cforward hforward K hK hradius
      hPbox hVlog hNlog hMlog hbox hvolume hnormalizer hmask hbaseAmbient hvbase hnbase hmbase
      hsites haxes hlabels hKbase hcoords hcutoff hdbase hpbase hrowsAmbient houtputs hheight
      Qgrid hQgrid hδg hdenseg Tg hQTg hstepAll Ag hAg Pg hPg hcP hsP hstrideGrid hBa hBi
      hDg hvg hwg htg hpg hcube hdegree hrowsD htail hblocks hRv hRiGrid hδw hTg hcoeff
      hPp₀ haxesGrid hfullAxes hfullOutputs hambientCount hprofileBudget
      hBanalytic hDanalytic hcutoffAnalytic hcoordAnalytic hgridAnalytic
      hPnum hI hn hcoeffEarly hRiEarly hVEarly
  have hconstructor := hconstructor spatialModulus stride N hspatialCanonical hmodulusRefined hW base cells poly hp hmem test
      (lossTarget := lossTarget) (Pphysical := Pphysical) (Dphysical := Dphysical)
      (Psample := Psample) (Rrank := Rrank) (Sstride := Sstride) (εsample := εsample) (ηsample := ηsample)
      hstridepos hN hτ hmesh hrootbudget htest hpositive
  have hconstructor := hconstructor hPs hX hframe hdP hSstride hSstrideP hεsample hτP hεsampleP hstride hsize hrank hRrank
      actual La Ca hLa hCa hηsample hamb hLaP hCaP hAmbientP hjet hηsampleP hactual
  have hconstructed := hconstructor hV hZ hξn1 hsizePhysical hρ8 hρshift hPphysical hMkPhysical hPeriodPhysical hDimPhysical
      hGPhysical hXPhysical hDPhysical hWL hprecision hηprecision hεprecision
  have hWGeometry : W ≤ Real.exp Pphysical * S.value :=
    hWL.trans (mul_le_mul_of_nonneg_right hDPhysical (Nat.cast_nonneg _))
  let Dout := (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1) : ℝ)
  let Eg := Dout * Prho + (target + Fmodel) + 1
  let LgridLog := fun j : Fin m => fun e : ℝ => slicedGridSiteLog j.val (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ((j.val + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) Dg p e
  let Cp := ∑ j, (LgridLog j 0 + Dg * (vg + 1))
  let Eg' := uniformProductAccuracyLog Dg Cp Eg + Dg * (vg + 1) + 1
  let Op := ∑ j, (siteExponentialOutputLog (Fintype.card (Finset (Fin (s + 1)))) (LgridLog j Eg') + (Dg + 1) * (vg + 1))
  refine exists_allocatedCanonical_finite_source_native (s := s) (nX := nX) (E := Q)
    (Op := Op) (Hgrid := slicedGridGeometryLog Dg vg wg tg + (Dg + vg + 8))
    B U basis S x y₀ modulus d period siteRadius (zero_lt_one.trans_le hrone) hb o bW
    poly hmem spatialModulus stride N wholeReference r hMk selection hgood hW base cells
    signal hsignal hzero hstridepos hτ hξn hrootbudget hZ
    hPnative hDnative hpNative hvNative hFnative hPrhoNative hPkNative htargetNative
    hBanalyticNative hphysicalNative hEcoarseNative hpGainNative
    hGPhysical (by simpa only [Fintype.card_fin] using hXPhysical) hDimPhysical hMkPhysical
    hWGeometry (hspatialCanonical.trans hperiodCanonical) hmeshEarly hstrideGeometry hτGeometry
    hgain hZhalf hPproj hcoarseTarget hEcoarseGain hlossTarget ?_
  obtain ⟨e, he, k, a, f, hmass, hphysical, hfinite⟩ := hconstructed
  refine ⟨e, ?_, k, a, f, ?_, ?_, ?_⟩
  · with_reducible simpa only [Op, Eg', Cp, LgridLog, p, Eg, Dout, Fmodel, Amass, Aanalytic,
      ← Nat.card_eq_fintype_card] using he
  · simp only [p, Fmodel, ← Nat.card_eq_fintype_card] at hmass ⊢
    with_reducible convert hmass using 1
    with_reducible congr 2
    funext label
    with_reducible congr 2
    funext i
    with_reducible congr 2
    all_goals exact Subsingleton.elim _ _
  · with_reducible simpa only [Op, Eg', Cp, LgridLog, p, Eg, Dout, Fmodel, Amass, Aanalytic,
      ← Nat.card_eq_fintype_card] using hphysical
  · with_reducible exact hfinite

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uG uI uB uJ uQ
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {s nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin (s + 1))))
variable (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (selection : Fin (s + 1) ↪ G)
variable (hgood : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
variable (period : ℕ) [NeZero period] (stride N : Fin nX → ℕ) [∀ i, NeZero (N i)]
variable (hperiodCanonical : period = kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hgood m))
variable (modulus : ℕ) (hmodulusRefined : modulus = residueRefinedPeriod period stride)
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => selectedRows
local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => degree (Subtype.val a))
local notation "L" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)
local notation "positiveLengths" => (fun j : Tuple => allocatedPrincipalSides_pos B U basis S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

variable (Q : Fin m → Type uQ) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "source" => allocatedCoefficientSource B U basis hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U basis hR hσ S
local notation "reference" => allocatedLongJetReference B U basis S jetRows
variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := (Fin (s + 1))) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))
local notation "H" => (fun j : Tuple => H₀ (embed j))
local notation "step" => (fun j : Tuple => step₀ (embed j))
local notation "c" => (fun j : Tuple => c₀ (embed j))
local notation "hsubset" => (fun j : Tuple => hsubset₀ (embed j))
local notation "residue" => (fun j : Tuple => r₀ (embed j))
local notation "GridTuples" => PrincipalAxisTuples (α := (Fin (s + 1))) grid (allocatedPrincipalSides B U basis S)
local notation "wholeLaw" => containedSupportedProgressionLaw (α := Fin (s + 1)) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell
local notation "gridLaw" => containedSupportedProgressionAxisLaw (α := Fin (s + 1)) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell grid
local notation "wholeRoot" y => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y
local notation "wholeDirs" y => allocatedPhysicalCubeDirections B U basis S x y

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
local notation "jetHaar" => Measure.pi (fun j =>
  @Measure.pi (selectedRows j) _ (fullBooleanRowSetFintype (s + 1) (Fin.val j + 1)) _
    (fun _ : selectedRows j => ν j))
local notation "density" => allocatedCoefficientDensity B U basis hb o hR hσ S

variable [CompactSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (s + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

variable [MeasurableSpace (SiteTorus (Finset (Fin (s + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (s + 1))) U)]

include ν μ hb o bW hperiodCanonical hmodulusRefined μrows hR hσ hMk hgood hP hMkP hRP hRi hσi hcount in

theorem exists_allocatedCanonicalSlice_projected_native_source
    {D target Pk Prho F Qstride : ℝ}
    (hdimensions : AllocatedComparisonDimensions (G := G) B (Fin (s + 1)) selectedRows D)
    (hPk : 0 ≤ Pk) (hMkPk : (Mk : ℝ) ≤ Real.exp Pk)
    (hPrho : 0 ≤ Prho) (htarget : 0 ≤ target) (hF : 0 ≤ F) (hQstride : 0 ≤ Qstride)
    (hstride : ∀ i, 0 < stride i) (hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (hlength : Real.exp (allocatedAffineLengthLog m D P Prho Pk target F (((m + 1 : ℕ) : ℝ) * Pk + Fintype.card (Fin nX) * Qstride)) ≤ S.value)
    {δ η : ℝ} (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0) (t : ℝ) (htone : t ≤ 1)
    (hs : AllocatedAffineCoveredComparison.{uJ, uQ, _, _, _, _, _} (G := G) B rows δ η ρ t htone)
    (hρ : 0 < ρ grid) (hρ1 : ρ grid ≤ 1)
    (hσsmall : ∀ j, σ j ≤ t)
    (hstep : ∀ j : Tuple, 0 < step j)
    (hδ : 0 < δ) (hδF : δ⁻¹ ≤ Real.exp F)
    (hdense : ∀ j : Tuple, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (hq : Fintype.card (Fin (s + 1)) ≤ m + 1)
    (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U basis S))
    (hy₀ : 0 < (wholeLaw).weight y₀)
    (T : Fin m → ℝ) (hT : ∀ j, partitionedIdealRadius (Fin (s + 1)) m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card (Fin (s + 1)) * ((Fintype.card (Fin (s + 1)) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4)
    (hρlog : (ρ grid : ℝ)⁻¹ ≤ Real.exp Prho)
    (hη0 : 0 ≤ η)
    (hηsmall : η ≤ Real.exp (-(target + 1 + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 4)))
    (siteRadius : ℝ≥0) (hrone : 1 ≤ siteRadius)
    (hsitebudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin (s + 1))) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (siteRadius : ℝ) * R j)))) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (hradius : ∀ j, (rowSets j).card * T j ≤ (siteRadius : ℝ))
    {Pbox Vlog Nlog Mlog baseAmbient : ℝ}
    (hPbox : 0 ≤ Pbox) (hVlog : 0 ≤ Vlog) (hNlog : 0 ≤ Nlog) (hMlog : 0 ≤ Mlog)
    (hbox : 2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp Pbox)
    (hvolume : allocatedFullGridNaturalVolume B U basis S rowSets ≤ Real.exp Vlog)
    (hnormalizer : ‖((allocatedProductIdealNormalizer B U basis S rowSets : ℝ) : ℂ)⁻¹‖ ≤ Real.exp Nlog)
    (hmask : (layerKernelIndexBound m Mk : ℝ) ^ Fintype.card (LayerSamplerAxis I n) *
      coefficientDeckPeriodCap selectedRows Q period ≤ Real.exp Mlog)
    (hbaseAmbient : 0 ≤ baseAmbient)
    (hvbase : Vlog ≤ baseAmbient) (hnbase : Nlog ≤ baseAmbient) (hmbase : Mlog ≤ baseAmbient)
    (hsites : (Fintype.card (Finset (Fin (s + 1))) : ℝ) ≤ baseAmbient)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ baseAmbient)
    (hlabels : (Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, Q j → ZMod period)) : ℝ) ≤ Real.exp baseAmbient)
    (hKbase : (K : ℝ) ≤ Real.exp baseAmbient)
    (hcoords : ((∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp baseAmbient)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp baseAmbient)
    (hpbase : (period : ℝ) ≤ Real.exp baseAmbient)
    (hrowsAmbient : ((∑ j : Fin m, ((rowSets j).card : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp baseAmbient)
    (houtputs : (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1) : ℝ) ≤ baseAmbient)
    (hheight : (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp baseAmbient)
    (Qgrid : ℝ≥0) (hQgrid : ∀ a : {a // allocatedGridAxis (I := I) U basis S.value a},
      8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
        (allocatedGridIntegerAxis B U basis S a).1 (allocatedGridIntegerAxis B U basis S a).2) : ℝ) + 1) ≤ Qgrid)
    {δg : ℝ} (hδg : 0 < δg)
    (hdenseg : ∀ tg, δg * allocatedPrincipalSides B U basis S tg ≤ (H₀ tg : ℝ))
    (Tg : ℕ) (hQTg : (((Fintype.card (Fin (s + 1)) + 1) * modulus : ℕ) : ℝ) / δg ≤ Tg)
    (hstepAll : ∀ tg, 0 < step₀ tg)
    (Ag : ℝ≥0) (hAg : LipschitzWith Ag Real.smoothTransition) (Pg : ℝ) (hPg : 1 ≤ Pg)
    (hcP : scalarCubePrimitiveEnvelope Empty Ag 16 (128 * probabilityProfileLipschitz) 1 ≤ Pg)
    (hsP : scalarCubePrimitiveEnvelope (Fin (s + 1)) Ag 1 0 modulus ≤ Pg)
    (hstrideGrid : ∀ tg, ((step₀ tg * modulus : ℕ) : ℝ) ≤ Pg)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    {Dg vg wg tg pg : ℝ}
    (hDg : 0 ≤ Dg) (hvg : 0 ≤ vg) (hwg : 0 ≤ wg) (htg : 0 ≤ tg) (hpg : 0 ≤ pg)
    (hcube : (Fintype.card (Fin (s + 1)) : ℝ) ≤ Dg) (hdegree : ∀ j : Fin m, ((j.val + 1 : ℕ) : ℝ) ≤ Dg)
    (hrowsD : ∀ j : Fin m, ((boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card : ℝ) ≤ Dg)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ Dg)
    (hblocks : ∀ j i, (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ Dg)
    (hRv : ∀ j, R j ≤ Real.exp vg) (hRiGrid : ∀ j, (R j)⁻¹ ≤ Real.exp vg)
    (hδw : δg⁻¹ ≤ Real.exp wg) (hTg : (Tg : ℝ) ≤ Real.exp tg)
    (hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp vg)
    (hPp₀ : Pg ≤ Real.exp pg) (haxesGrid : (Fintype.card {a // grid a} : ℝ) ≤ Dg)
    (hfullAxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ Dg)
    (hfullOutputs : (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1) : ℝ) ≤ Dg)
    (hambientCount : ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ Dg)
    (hprofileBudget : (probabilityProfileLipschitz : ℝ) ≤ Dg)
    {Banalytic : ℝ} (hBanalytic : 0 ≤ Banalytic) (hDanalytic : Dg ≤ Banalytic)
    (hcutoffAnalytic : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Banalytic)
    (hcoordAnalytic : ((K * ∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp Banalytic)
    (hgridAnalytic : (Qgrid : ℝ) ≤ Real.exp Banalytic)
    {Pnum : ℝ} (hPnum : 0 ≤ Pnum)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ Pnum) (hn : ∀ j, (n j : ℝ) ≤ Pnum)
    (hcoeffEarly : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pnum)
    (hRiEarly : ∀ j, (R j)⁻¹ ≤ Real.exp Pnum)
    (hVEarly : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Real.exp Pnum)
    {gain Pproj coarseTarget Ecoarse pGain : ℝ}
    :
    let ambientQ := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1)) (Fintype.card (Fin (s + 1)))
      (Pbox + Prho + Vlog + Nlog + Mlog + target)
    let ambientBudget := affineAmbientPrimitiveBudget baseAmbient ambientQ
    ∀ {W τ ξn : ℝ} (hW : 0 ≤ W)
      (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
      (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
      (_hp : ∀ j, DegreeLE (1 : (Fin nX) → ℕ) (j.val + 1) (poly j))
      (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
      (signal : ((Fin nX) → ℤ) → ℂ),
    (∀ u ∈ integerBox N, ‖signal u‖ ≤ 1) →
    (∀ u, u ∉ integerBox N → signal u = 0) →
    ∀ {lossTarget Pphysical Dphysical Psample Rrank Sstride εsample ηsample : ℝ},
    (∀ i, 0 < stride i) → (∀ i, 0 < N i) → ∀ (hτ : 0 < τ),
    allocatedPhysicalRootBudget B U basis S (fun _ => 0) ≤ W →
    0 ≤ Psample → (Fintype.card (Fin nX) : ℝ) ≤ Psample →
    (Fintype.card (Option (Fin (s + 1)) × (Fin nX)) : ℝ) ≤ Psample →
    0 ≤ Sstride → Sstride ≤ Real.exp Psample → 0 < εsample →
    1 / τ ≤ Real.exp Psample → 1 / εsample ≤ Real.exp Psample →
    (∀ i, (stride i : ℝ) ≤ Sstride) →
    let A := Classical.choose (exists_translated_physical_jet_l1_perturbation.{0,uJ,0} m (s + 1))
    (∀ i, Real.exp ((Psample + A) ^ A) ≤ (N i : ℝ)) →
    (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
    Real.exp ((Psample + A) ^ A) ≤ Rrank →
    0 < ηsample → (Fintype.card (CoefficientAmbientIndex (Fin (s + 1)) J) : ℝ) ≤ Psample →
    ambientBudget ≤ Psample →
    ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin (s + 1)) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp Psample →
    ηsample⁻¹ ≤ Real.exp Psample →
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξn N
    (∀ z, 0 < V z) → ∀ (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z),
    ∀ {ρphysical : ℝ}, ξn ≤ 1 →
    (∀ t, 8 * (1 + W) * (stride t : ℝ) * ρphysical ≤ (ξn * τ) * (N t : ℝ)) →
    8 * (probabilityProfileLipschitz : ℝ) ≤ ρphysical →
    2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U basis S (fun _ => 0))) ≤ ρphysical →
    0 ≤ Pphysical → (Mk : ℝ) ≤ Real.exp Pphysical →
    (period : ℝ) ≤ Real.exp (Pphysical ^ 2) →
    (((s + 1) + 1 : ℕ) : ℝ) ≤ Pphysical → (Fintype.card G : ℝ) ≤ Pphysical →
    (Fintype.card (Fin nX) : ℝ) ≤ Pphysical → Dphysical ≤ Real.exp Pphysical →
    W ≤ Dphysical * S.value →
    lossTarget + coefficientErrorSpatialLog Pphysical + 8 ≤ target →
    ηsample ≤ Real.exp (-target) → εsample ≤ Real.exp (-target) →
    let Amass := Classical.choose (exists_allocatedAffineModelMass_budget m (s + 1))
    let Aanalytic := Classical.choose (exists_allocatedAffineAnalytic_budget m (s + 1))
    let Fmodel := (m * (2 : ℝ) ^ Fintype.card (Fin (s + 1))) * (Pnum + 8) * (1 + 4 * Pnum) +
      Fintype.card (LayerSamplerAxis I n) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (selectedRows j) * ((m + 1 : ℕ) * Pk))
    let p := slicedGridGeometryLog Dg vg wg tg + pg
    ∀ {Pnative : ℝ}, 0 ≤ Pnative →
    Dg ∈ Set.Icc 0 Pnative → p ∈ Set.Icc 0 Pnative → vg ∈ Set.Icc 0 Pnative →
    Fmodel ∈ Set.Icc 0 Pnative → Prho ∈ Set.Icc 0 Pnative → Pk ∈ Set.Icc 0 Pnative →
    target ∈ Set.Icc 0 Pnative → Banalytic ∈ Set.Icc 0 Pnative →
    Pphysical ∈ Set.Icc 0 Pnative → Ecoarse ∈ Set.Icc 0 Pnative → pGain ∈ Set.Icc 0 Pnative →
    ∀ (hξn : 0 < ξn),
    (∀ i, (stride i : ℝ) ≤ Real.exp Pphysical) →
    1 / τ ≤ Real.exp Pphysical →
    Real.exp (-pGain) / 2 ≤ gain →
    pGain + 32 ≤ Pproj → pGain + 32 ≤ coarseTarget →
    pGain + 32 ≤ Ecoarse → pGain + 32 ≤ lossTarget →
    ∀ (Cproj Vproj : Fin m → ℝ≥0),
    let Acover := Classical.choose (exists_allocated_canonical_constructed_projection.{0,uG,uI,uB,uJ} m (s + 1))
    let coverLog := (Pproj + ((s + 1) + 2 : ℕ) + Acover) ^ Acover
    let Asample := Classical.choose (exists_allocatedCanonicalProjection_composed_budget m (s + 1) Acover)
    let Pmass := (Pproj + Asample) ^ Asample
    coverLog ≤ baseAmbient → coverLog ≤ Psample → Pmass ≤ Psample →
    (∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ Cproj j * ‖z‖) →
    (∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vproj j) →
    (∀ j, σ j ≤ 1) →
    (∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) →
    (Fintype.card (Fin nX) : ℝ) ≤ Pmass →
    (Fintype.card (Option (Fin (s + 1)) × Fin nX) : ℝ) ≤ Pmass →
    (∀ i, (stride i : ℝ) ≤ Real.exp Pmass) → 1 / τ ≤ Real.exp Pmass →
    let AmassWindow := Classical.choose (exists_translated_physical_jet_density_window_mass.{0,uJ,0,max uG uI uB} m (s + 1))
    (∀ i, Real.exp ((Pmass + AmassWindow) ^ AmassWindow) ≤ (N i : ℝ)) →
    Real.exp ((Pmass + AmassWindow) ^ AmassWindow) ≤ Rrank →
    (Fintype.card (CoefficientAmbientIndex (Fin (s + 1)) J) : ℝ) ≤ Pmass →
    ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin (s + 1)) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp Pmass →
    ∀ {C₀ δspatial fineMesh : ℝ},
    0 < ρphysical → 1 ≤ C₀ → (S.value : ℝ) ≤ C₀ → W ≤ C₀ →
    anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρphysical →
    0 ≤ δspatial →
    Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
      (2 * allocatedPhysicalEntryBudget B U basis S (fun _ => 0)) ≤ δspatial * ρphysical →
    0 < fineMesh →
    Real.exp Pmass * (24 * (probabilityProfileLipschitz : ℝ) *
      Fintype.card (Option (LayerSamplerVariables G I n B) × Fin nX) / ρphysical) ≤ normalizedSpatialShare coarseTarget / 2 →
    allocatedTupleSpatialError (Fintype.card (Fin nX)) selection
      (PrincipalTupleIndex B (layerSamplerDegree I n)) Mk period C₀ ρphysical ξn W δspatial fineMesh *
      coarseReferenceMassConstant (s + 1) (Fin nX) W S.value ≤ normalizedSpatialShare coarseTarget / 2 →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp Pphysical →
    W ≤ Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ) →
    fineMesh ≤ allocatedEarlyRecenteredMesh (Fin nX) selection Mk period Pphysical Ecoarse →
    1 ≤ Pproj → (m : ℝ) ≤ Pproj →
    (Fintype.card G : ℝ) ≤ Pproj → (S.value : ℝ) ≤ Real.exp Pproj →
    ((m + 1 : ℕ) : ℝ) * Pk ≤ Pproj →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pproj → W ≤ Real.exp Pproj →
    (∀ j, (R j)⁻¹ ≤ Real.exp Pproj) → (∀ j, (σ j)⁻¹ ≤ Real.exp Pproj) →
    (∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pproj) →
    (∀ j, (Fintype.card (I j) : ℝ) ≤ Pproj) → (∀ j, (n j : ℝ) ≤ Pproj) →
    (∀ j, (Fintype.card (J j) : ℝ) ≤ Pproj) →
    (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pproj →
    (∀ j, (Cproj j : ℝ) ≤ Real.exp Pproj) → (∀ j, (Vproj j : ℝ) ≤ Real.exp Pproj) →
    (Fintype.card (Fin nX) : ℝ) ≤ Pproj →
    (Fintype.card (Option (LayerSamplerVariables G I n B) × Fin nX) : ℝ) ≤ Pproj →
    (∀ i, (stride i : ℝ) ≤ Real.exp Pproj) → τ⁻¹ ≤ Real.exp Pproj → ξn⁻¹ ≤ Real.exp Pproj →
    let Aproj := Classical.choose (Classical.choose_spec
      (exists_allocated_canonical_constructed_projection.{0,uG,uI,uB,uJ} m (s + 1)))
    (∀ i, Real.exp ((Pproj + Aproj) ^ Aproj) ≤ (N i : ℝ)) →
    Real.exp ((Pproj + Aproj) ^ Aproj) ≤ Rrank →
    cells.Nonempty → ∀ (bases : Finset (Fin nX → ℤ)), bases.Nonempty →
    gain ≤ ((wholeLaw).complexMean (fun y => allocatedSlicedTupleValue B U basis hb o hR hσ S
      (Fin nX) poly hmem N (fun i => Nat.pos_of_ne_zero (NeZero.ne (N i))) hW
      hτ hξn stride cells hZ bases x y signal)).re →
    let C := Classical.choose (exists_canonicalSlicedNative_input_budget m (s + 1) Amass Aanalytic)
    let Bbudget := (Pnative + C) ^ C
    let Anorm := Classical.choose (exists_allocatedRecenteredFactor_normalization.{uG,uI,uB,uJ,0,uJ} m (s + 1))
    let Anative := Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s)
    let A := Classical.choose (exists_normalizedNative_uniform_budget m Anorm Anative)
    let budget := (Bbudget + A) ^ A
    ∃ twistData : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
      (Real.exp budget) (Real.exp budget) ⟨Real.exp budget, Real.exp_nonneg _⟩,
      ∃ Fnative : integerBox N → ℂ,
        Nonempty (NativeSampleModel (fun _ : Fin nX => 1) s budget
          (fun u : integerBox N => u.val) Fnative) ∧
        Real.exp (-budget) ≤
          ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) (integerBox_nonempty N)).correlation
            (fun u => signal u.val) (fun u => star (twistData.eval N poly u.val) * Fnative u)‖ := by
  intro ambientQ ambientBudget W τ ξn hW cells poly hp hmem signal hsignal hzero
    lossTarget Pphysical Dphysical Psample Rrank Sstride εsample ηsample
    hstridepos hN hτ hrootbudget hPs hX hframe hSstride hSstrideP hεsample hτP hεsampleP hstrideBoundSample
    A hsize hrank hRrank hηsample hamb hAmbientP hjet hηsampleP V hV hZ
    ρphysical hξn1 hsizePhysical hρ8 hρshift
    hPphysical hMkPhysical hPeriodPhysical hDimPhysical hGPhysical hXPhysical hDPhysical hWL
    hprecision hηprecision hεprecision Amass Aanalytic Fmodel p
    Pnative hPnative hDnative hpNative hvNative hFnative hPrhoNative hPkNative htargetNative
    hBanalyticNative hphysicalNative hEcoarseNative hpGainNative hξn hstrideGeometry hτGeometry
    hgain hPprojGain hcoarseTarget hEcoarseGain hlossTarget
    Cproj Vproj Acover coverLog Asample Pmass hcoverAmbient hcoverSample hmassSample
    hCactual hVactual hσ1 hsmall hXmass hframeMass hstrideMass hτMass
    AmassWindow hsizeMass hRrankMass hambMass hjetMass
    C₀ δspatial fineMesh hρphysical hC₀ hLC hWC hmeshThreshold hδspatial hρmove hfineMesh
    hboundary hsite hvars hWscale hmeshCoarse hPproj hmProj hGproj hLproj hperiodP
    hKproj hWproj hRproj hσproj hcountProj hIproj hnProj hJproj hProfileProj hCproj hVproj
    hXproj hFrameProj hStrideProj hτProj hξProj Aproj hSizeProj hRankProj hCells bases hbases hdetected
    Cbudget Bbudget Anorm Anative Abudget budget
  subst modulus
  let modulus := residueRefinedPeriod period stride
  let law := containedSupportedProgressionLaw (α := Fin (s + 1)) B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S)
    hH₀ hsubset₀ modulus r₀ hcell
  have hsignalAll (u) : ‖signal u‖ ≤ 1 := by
    by_cases hu : u ∈ integerBox N
    · exact hsignal u hu
    · simp only [hzero u hu, norm_zero, zero_le_one]
  with_reducible
    have hcoarse := exists_allocatedCanonicalSlice_uniform_projected_coarse_source
      (dim := s + 1) (m := m) (G := G) (I := I) (n := n) (J := J)
      (Pproj := Pproj) (Pk := Pk) (Rrank := Rrank) (target := coarseTarget)
      (κ := gain) (p := Pphysical) (E := Ecoarse)
      (B := B) (U := U) (b := basis) (S := S) (hb := hb) (o := o)
      (hR := hR) (hσ := hσ) (Cproj := Cproj) (Vproj := Vproj)
      (X := Fin nX) («modulus» := period) (q := stride)
      («H» := H₀) («step» := step₀) («c» := c₀) (hH := hH₀) («hsubset» := hsubset₀)
      (label₀ := r₀) (hcell := hcell) (y₀ := y₀) (hy₀ := hy₀)
      (x := x) (hM := hMk) (selection := selection) (hx := hgood) (hcanonical := hperiodCanonical)
      (N := N) (hW := hW) (mesh := fineMesh) (cells := cells)
      (poly := poly) (hp := hp) (hm := hmem) (signal := signal) (hsignal := hsignalAll)
      (hN := hN) (hq := hstridepos) (hτ := hτ) (hρ := hρphysical)
      (hbudget := hrootbudget) (hC₀ := hC₀) (hLC := hLC) (hWC := hWC)
      (hξ := hξn) (hξ1 := hξn1) (hsize := hsizePhysical) (hmesh := hmeshThreshold)
      (hρ8 := hρ8) (hδ := hδspatial) (hρshift := hρshift) (hρmove := hρmove)
      (hmeshpos := hfineMesh) (hmass := hZ) (μ := μrows) (ν := ν) (μcoeff := μ)
      hGproj hLproj hMkPk hperiodP hCactual hVactual hσ1 C hC hchart hsmall
  have hcoarse := hcoarse hXmass hframeMass hstrideMass hτMass hsizeMass hrank hRrankMass hambMass hjetMass
  have hcoarse := hcoarse hboundary hsite hPphysical hEcoarseNative.1 hGPhysical hXPhysical hDimPhysical hMkPhysical
    hvars hWscale hmeshCoarse
  have hcoarse := hcoarse hPproj hmProj hKproj hWproj hRproj hσproj hcountProj
    hIproj hnProj hJproj hProfileProj hCproj hVproj hXproj hFrameProj hStrideProj hτProj hξProj
    hSizeProj hRankProj hCells bases hbases hdetected
  obtain ⟨d, hdiv, hdpos, hdBound, g, hgc, hgb, hgi, _hgMass, hglaw, hactualFamily,
    base, _hbase, hZmass, hpositive⟩ := hcoarse
  have : NeZero d := ⟨hdpos.ne'⟩
  obtain ⟨actual, hLa, hCa, hactualComplex⟩ := hactualFamily law
  have hactual (z) : (law.mean (fun y => g y z) : ℂ) =
      actual (coveredJetAmbientTorus U 1 z) := by
    simpa only [FiniteProbabilityWeights.complexMean_ofReal] using hactualComplex z
  have hcanonicalRefined : modulus = canonicalSlicedModulus (M := Mk) selection stride m x := by
    dsimp only [modulus]
    rw [canonicalSlicedModulus_good selection stride m x hgood, hperiodCanonical]
  have hdbase : (d : ℝ) ≤ Real.exp baseAmbient :=
    hdBound.trans (Real.exp_le_exp.mpr hcoverAmbient)
  have hdP : (d : ℝ) ≤ Real.exp Psample :=
    hdBound.trans (Real.exp_le_exp.mpr hcoverSample)
  have hactualP : Real.exp Pmass ≤ Real.exp Psample := Real.exp_le_exp.mpr hmassSample
  have hmesh : 0 < allocatedEarlyRecenteredMesh (Fin nX) selection Mk period Pphysical Ecoarse :=
    hfineMesh.trans_le hmeshCoarse
  have hconstructor := exists_allocatedCanonicalSlice_constructed_native_source
      (s := s) (nX := nX) (gain := gain) (Pproj := Pproj)
      (coarseTarget := coarseTarget) (Ecoarse := Ecoarse) (pGain := pGain)
      (Z := selectedJointDensityMass bases stride cells V
        (allocatedJointBaseDensity B U basis hb o hR hσ S (Fin nX) poly hmem))
      B U basis hR hσ S x hMk selection hgood stride hP hMkP hRP hRi hσi hcount
      Q hb o bW d H₀ step₀ c₀ hH₀ hsubset₀ modulus hcanonicalRefined r₀ hcell ν μ μrows
      hdimensions hPk hMkPk hPrho htarget hF hQstride hstride hstrideBound hlength
      g (fun y => (hgc y).measurable) (fun y z => (hgb y z).1) hgi hglaw
      ρ t htone hs hρ hρ1 hσsmall hstep hδ hδF hdense hq
      y₀ hy₀ T hT hsource C hC hchart hbudget hρlog hη0 hηsmall
      period hperiodCanonical hdiv siteRadius hrone hsitebudget Cforward hforward K hK hradius
      hPbox hVlog hNlog hMlog hbox hvolume hnormalizer hmask hbaseAmbient hvbase hnbase hmbase
      hsites haxes hlabels hKbase hcoords hcutoff hdbase hpbase hrowsAmbient houtputs hheight
      Qgrid hQgrid hδg hdenseg Tg hQTg hstepAll Ag hAg Pg hPg hcP hsP hstrideGrid hBa hBi
      hDg hvg hwg htg hpg hcube hdegree hrowsD htail hblocks hRv hRiGrid hδw hTg hcoeff
      hPp₀ haxesGrid hfullAxes hfullOutputs hambientCount hprofileBudget
      hBanalytic hDanalytic hcutoffAnalytic hcoordAnalytic hgridAnalytic
      hPnum hI hn hcoeffEarly hRiEarly hVEarly
  have hconstructor := hconstructor period stride N rfl rfl hW base cells poly hp hmem signal hsignal hzero
      (lossTarget := lossTarget) (Pphysical := Pphysical) (Dphysical := Dphysical)
      (Psample := Psample) (Rrank := Rrank) (Sstride := Sstride) (εsample := εsample) (ηsample := ηsample)
      hstridepos hN hτ hmesh hrootbudget hpositive
  have hconstructor := hconstructor hPs hX hframe hdP hSstride hSstrideP hεsample hτP hεsampleP hstrideBoundSample
      hsize hrank hRrank actual ⟨Real.exp Pmass, Real.exp_nonneg _⟩ ⟨Real.exp Pmass, Real.exp_nonneg _⟩
      hLa hCa hηsample hamb hactualP hactualP hAmbientP hjet hηsampleP hactual
  exact hconstructor hV hZ hξn1 hsizePhysical hρ8 hρshift hPphysical hMkPhysical hPeriodPhysical hDimPhysical
      hGPhysical hXPhysical hDPhysical hWL hprecision hηprecision hεprecision
      hPnative hDnative hpNative hvNative hFnative hPrhoNative hPkNative htargetNative
      hBanalyticNative hphysicalNative hEcoarseNative hpGainNative hξn rfl hstrideGeometry hτGeometry
      hgain hZmass.1 hPprojGain hcoarseTarget hEcoarseGain hlossTarget

end Erdos3.VectorPolynomial

end

end OAI
