import OAI.Combinatorics.Progressions.Estimates.AllocatedWholeProfileEnvelope

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type uG} [Fintype G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

variable (q : ℕ) [NeZero q]

theorem allocatedWholeProfile_recentered_mass :
  ∀ {K : ℕ}, AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim K (rowTypes) (rows) → ∀
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type uQ} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d]
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

    (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset (Fin dim) // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
    (CM Cf : ℝ≥0) (_hCM : 1 ≤ (CM : ℝ)) (_hfb : ∀ v, |f v| ≤ Cf)
    (_hmask : ∀ y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
      (allocatedPrincipalSides B U b S), ∀ j z, 0 ≤ allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ CM)
    (_hperiod : ∀ j, integerScalarLattice (rowTypes j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    {X : Type uX} [Fintype X] [DecidableEq X]
    {P₀ : ℝ} (_hP : 0 ≤ P₀) (_hn : (Fintype.card X : ℝ) ≤ P₀)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P₀)
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hmp : ∀ j e, coefficients (p j) e ∈ U j)
    (stride : X → ℕ) (_hs : ∀ x, 0 < stride x)
    {R₁ S₀ ρ ε : ℝ} (_hS : 0 ≤ S₀) (_hSP : S₀ ≤ Real.exp P₀) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P₀) (_hεP : 1 / ε ≤ Real.exp P₀)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (N : X → ℕ) (_hsize : ∀ x, Real.exp ((P₀ + K) ^ K) ≤ (N x : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) R₁ (U j) (p j))
    (_hR : Real.exp ((P₀ + K) ^ K) ≤ R₁)
    {δFourier LFourier : ℝ} (_hδFourier : 0 < δFourier) (_hLFourier : 0 ≤ LFourier)
    (_hamb : (Fintype.card (JetAmbientIndex (rowTypes) J) : ℝ) ≤ LFourier)
    (_hδL : δFourier⁻¹ ≤ Real.exp LFourier),
    let A := Real.toNNReal (coefficientDeckPeriodCap (rowTypes) Q q) *
      CM ^ Fintype.card (LayerSamplerAxis I n) * Cf
    (allocatedErrorKernelLip B U b S (O := rowTypes) 1 A C V : ℝ) ≤ Real.exp LFourier →
    Real.exp ((2 * LFourier + 2) ^ 4) ≤ Real.exp P₀ →
    Real.exp (2 * LFourier * (2 * LFourier + 2) ^ 4) *
      allocatedErrorKernelCap B U b S (O := rowTypes) 1 A V ≤ Real.exp P₀ →
    let mass := A *
      (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, (rowTypes) a.1)
    ∀ (W : ℝ) (_hW : 0 ≤ W) (ξ : ℝ), 0 < ξ →
    let H := trimmedSpatialRootScale ρ N stride
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let point := physicalCubeRowSample (O := rowTypes) U d (rows) p hmp
    let profile := fun y z => (allocatedWholeMaskedCoveredProfile (O := rowTypes)
      B U b hR hσ S x (rows) hb o bW d y q f z : ℂ)
    let factor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / (S.value : ℝ)) ^ dim) ^ Fintype.card X
    ∀ (reference : (PrincipalTupleIndex B (layerSamplerDegree I n) →
        Option (Fin dim) → ZMod (residueRefinedPeriod q stride)) →
        PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
      (base : X → ℤ)
      (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)),
    let V₀ := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W ρ ξ N
    (0 < ∑' z, selectedResidueSmoothWeight stride cells V₀ z) →
    (∀ t, Fintype.card (Option (LayerSamplerVariables G I n B)) *
      allocatedPhysicalEntryBudget B U b S (fun _ => 0) ≤ H t) →
    (∀ t, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H t) →
    law.mean (allocatedRecenteredProfileMass (W := W) (τ := ρ) (ξ := ξ)
      B U b S X q stride reference x N base cells point profile) ≤
      factor * (mass + 2 * δFourier + ε) := by
  intro K hSampling x hb o Q _ bW d _ _ f CM Cf hCM hfb hmask hperiod C V hC hV
    X _ _ P₀ hP₀ hn hdim _ _ _ μ _ _ ν _ _ p hp hmp stride hs R₁ S₀ ρ ε
    hS hSP hρ hε hρP hεP hstride N hsize₁ hrank hR₁
    δFourier LFourier hδFourier hLFourier hamb hδL A hLip hfreqP hcoeffP
    mass W hW ξ hξ H law point profile factor reference base cells V₀ hZ₀ hrows hscale
  let T := trimmedSpatialSlopeScale W ρ N stride
  have hprevious := allocatedWholeProfile_reference_envelope_mass B U b hR hσ S q (K := K) hSampling
  have henv := @hprevious x hb o Q _ bW d _ _ f CM Cf hCM hfb hmask hperiod C V hC hV
    X _ _ P₀ hP₀ hn hdim _ _ _ μ _ _ ν _ _ p hp hmp stride hs R₁ S₀ ρ ε
    hS hSP hρ hε hρP hεP hstride N hsize₁ hrank hR₁
    δFourier LFourier hδFourier hLFourier hamb hδL hLip hfreqP hcoeffP
  have hN (t : X) : 0 < N t := Nat.cast_pos.mp ((Real.exp_pos _).trans_le (hsize₁ t))
  have hscales (t : X) : 0 < H t ∧ 0 < T t := trimmedSpatial_scales_pos hW hρ N stride t (hN t) (hs t)
  let volumeOut := ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (H t) (T t) S.value i
  have hA : 0 < volumeOut := Finset.prod_pos (fun t _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos (Fin dim) (hscales t).1 (hscales t).2 (Nat.cast_pos.mpr S.positive) i))
  have hfactor : 0 ≤ factor := mul_nonneg
    (pow_nonneg (div_nonneg (by norm_num) smoothProbabilityProfile_pos_zero.le) _)
    (pow_nonneg (pow_nonneg (div_nonneg (by linarith) (Nat.cast_nonneg S.value)) _) _)
  have hV₀ : ∀ z, 0 < V₀ z := narrowTrimmedSpatialWidths_pos hW hρ hξ N hN
  have hcell (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
      (a : cells) :
      (∑ v ∈ spatialWindow H 4, ‖profile y (point
        (allocatedWholeResidueReconstruction B U b S X q stride reference x base
          (principalResidueLabel (residueRefinedPeriod q stride) y) a.val v))‖) / volumeOut ≤
        factor * (mass + 2 * δFourier + ε) := by
    let y₀ := reference (principalResidueLabel (residueRefinedPeriod q stride) y)
    let root := allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y₀
    let dirs := allocatedPhysicalCubeDirections B U b S x y₀
    let cell := columnResiduePattern stride (standardPhysicalCubeFrame
      (physicalCubeRootDifferences root dirs 0 (boundedColumnResidueRepresentative stride a.val)))
    have sampled := henv base cell y
    have hraw := physicalReconstruction_sum_le_sampled_mass stride hs root dirs a.val H
      (fun t => (hscales t).1)
      (fun t i => (allocatedPhysicalCube_coefficient_row_sum B U b S (fun _ => 0) x y₀ i).trans (hrows t))
      hscale (fun v => |allocatedWholeMaskedCoveredProfile (O := rowTypes)
        B U b hR hσ S x (rows) hb o bW d y q f (point (translatePhysicalCube base v))|)
      (fun _ => abs_nonneg _) sampled.1
    rw [referenceJetEnvelope_anisotropic_volume stride hs H T (Nat.cast_pos.mpr S.positive).ne'
      (trimmedSpatial_scale_ratio hW N stride)] at hraw
    have hbig := hraw.trans (mul_le_mul_of_nonneg_left sampled.2 (mul_nonneg hfactor hA.le))
    have hrec (v) : allocatedWholeResidueReconstruction B U b S X q stride reference x base
        (principalResidueLabel (residueRefinedPeriod q stride) y) a.val v =
        translatePhysicalCube base (physicalResidueReconstruction root dirs 0
          (boundedColumnResidueRepresentative stride a.val) stride v) :=
      physicalResidueReconstruction_translate _ _ _ _ _ _
    have hsum : (∑ v ∈ spatialWindow H 4, ‖profile y (point
        (allocatedWholeResidueReconstruction B U b S X q stride reference x base
          (principalResidueLabel (residueRefinedPeriod q stride) y) a.val v))‖) ≤
        (factor * volumeOut) * (mass + 2 * δFourier + ε) := by
      simpa only [hrec, profile, Complex.norm_real, Real.norm_eq_abs] using hbig
    calc
      _ ≤ ((factor * volumeOut) * (mass + 2 * δFourier + ε)) / volumeOut :=
        div_le_div_of_nonneg_right hsum hA.le
      _ = _ := by field_simp [hA.ne']
  have hlocal (y) : allocatedRecenteredProfileMass (W := W) (τ := ρ) (ξ := ξ)
      B U b S X q stride reference x N base cells point profile y ≤ factor * (mass + 2 * δFourier + ε) := by
    change (∑ a : cells, selectedResidueCellWeight stride cells V₀ a *
      ((∑ v ∈ spatialWindow H 4, ‖profile y (point
        (allocatedWholeResidueReconstruction B U b S X q stride reference x base
          (principalResidueLabel (residueRefinedPeriod q stride) y) a.val v))‖) / volumeOut)) ≤ _
    calc
      _ ≤ ∑ a : cells, selectedResidueCellWeight stride cells V₀ a * (factor * (mass + 2 * δFourier + ε)) :=
        Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hcell y a)
          (selectedResidueCellWeight_nonneg stride cells V₀ a))
      _ = _ := by rw [← Finset.sum_mul, selectedResidueCellWeight_sum stride cells V₀ hV₀ hZ₀, one_mul]
  exact (law.mean_mono hlocal).trans_eq (law.mean_const _)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type uG} [Fintype G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

variable (q : ℕ) [NeZero q]

theorem allocatedWholeProfile_recentered_primitive_mass
    {p₁ w v : ℝ} (hp₁ : 0 ≤ p₁) (hw : 0 ≤ w) (hv : 0 ≤ v) (hp₁four : 4 ≤ p₁)
    (hdimSmall : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p₁)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p₁) (hn₁ : ∀ j, (n j : ℝ) ≤ p₁)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p₁)
    (M₀ : ℕ) (hqM : q ≤ M₀ ^ (m + 1)) (hM₀ : (M₀ : ℝ) ≤ Real.exp p₁)
    (hS₁ : (S.value : ℝ) ≤ Real.exp p₁) :
  ∀ {K : ℕ}, AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim K (rowTypes) (rows) → ∀
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type uQ} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d]
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

    (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset (Fin dim) // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
    (CM Cf : ℝ≥0) (_hCM : 1 ≤ (CM : ℝ)) (_hfb : ∀ v, |f v| ≤ Cf)
    (_hCMexp : (CM : ℝ) ≤ Real.exp w) (_hCfexp : (Cf : ℝ) ≤ Real.exp v)
    (_hmask : ∀ y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
      (allocatedPrincipalSides B U b S), ∀ j z, 0 ≤ allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ CM)
    (_hperiod : ∀ j, integerScalarLattice (rowTypes j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hCexp : ∀ j, (C j : ℝ) ≤ Real.exp p₁) (_hVexp : ∀ j, (V j : ℝ) ≤ Real.exp p₁)
    {X : Type uX} [Fintype X] [DecidableEq X]
    {P₀ : ℝ} (_hP : 0 ≤ P₀) (_hn : (Fintype.card X : ℝ) ≤ P₀)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P₀)
    (_hbudget : allocatedSiteErrorFourierOutput m p₁ w v ≤ P₀)
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hmp : ∀ j e, coefficients (p j) e ∈ U j)
    (stride : X → ℕ) (_hs : ∀ x, 0 < stride x)
    {R₁ S₀ ρ : ℝ} (_hS : 0 ≤ S₀) (_hSP : S₀ ≤ Real.exp P₀) (_hρ : 0 < ρ)
    (_hρP : 1 / ρ ≤ Real.exp P₀)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (N : X → ℕ) (_hsize : ∀ x, Real.exp ((P₀ + K) ^ K) ≤ (N x : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) R₁ (U j) (p j))
    (_hR : Real.exp ((P₀ + K) ^ K) ≤ R₁),
    ∀ (W : ℝ) (_hW : 0 ≤ W) (ξ : ℝ), 0 < ξ →
    let H := trimmedSpatialRootScale ρ N stride
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let point := physicalCubeRowSample (O := rowTypes) U d (rows) p hmp
    let profile := fun y z => (allocatedWholeMaskedCoveredProfile (O := rowTypes)
      B U b hR hσ S x (rows) hb o bW d y q f z : ℂ)
    let factor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / (S.value : ℝ)) ^ dim) ^ Fintype.card X
    ∀ (reference : (PrincipalTupleIndex B (layerSamplerDegree I n) →
        Option (Fin dim) → ZMod (residueRefinedPeriod q stride)) →
        PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
      (base : X → ℤ)
      (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)),
    let V₀ := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W ρ ξ N
    (0 < ∑' z, selectedResidueSmoothWeight stride cells V₀ z) →
    (∀ t, Fintype.card (Option (LayerSamplerVariables G I n B)) *
      allocatedPhysicalEntryBudget B U b S (fun _ => 0) ≤ H t) →
    (∀ t, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H t) →
    law.mean (allocatedRecenteredProfileMass (W := W) (τ := ρ) (ξ := ξ)
      B U b S X q stride reference x N base cells point profile) ≤
      factor * Real.exp (allocatedSiteSpatialMassLog (allocatedComparisonDimension m p₁) w v + 1) := by
  intro K hSampling x hb o Q _ bW d _ _ f CM Cf hCM hfb hCMexp hCfexp hmask hperiod C V hC hV
    hCexp hVexp X _ _ P₀ hP₀ hn hdim hbudget _ _ _ μ _ _ ν _ _ p hp hmp stride hs R₁ S₀ ρ
    hS hSP hρ hρP hstride N hsize₁ hrank hR₁ W hW ξ hξ H law point profile factor
    reference base cells V₀ hZ₀ hrows hscale
  have hquarter : (1 / 4 : ℝ)⁻¹ ≤ Real.exp p₁ := by
    norm_num
    linarith [Real.add_one_le_exp p₁]
  have hrowdim : Fintype.card (Fin dim) ≤ m + 1 := by
    simpa only [Fintype.card_fin] using hdimSmall
  obtain ⟨hLF, hpP, hamb, hδL, hLip, hfreq, hcoeff⟩ :=
    allocatedSiteErrorPrimitive_fourier_budget B U b S (rows) hrowdim
      (fun _ => Subtype.val_injective) hb bW M₀ q hqM 1 CM Cf C V
      hp₁ hw hv hvars hI hn₁ hJ (le_refl _) hM₀ hS₁ hCexp hVexp hCMexp hCfexp hquarter
  have heP := Real.exp_le_exp.mpr hbudget
  have hquarterP : 1 / (1 / 4 : ℝ) ≤ Real.exp P₀ := by
    simpa only [one_div] using hquarter.trans (Real.exp_le_exp.mpr (hpP.trans hbudget))
  have hprevious := allocatedWholeProfile_recentered_mass B U b hR hσ S q (K := K) hSampling
  have hbound := @hprevious x hb o Q _ bW d _ _ f CM Cf hCM hfb hmask hperiod C V hC hV
    X _ _ P₀ hP₀ hn hdim _ _ _ μ _ _ ν _ _ p hp hmp stride hs R₁ S₀ ρ (1 / 4)
    hS hSP hρ (by norm_num) hρP hquarterP hstride N hsize₁ hrank hR₁
    (1 / 4) (allocatedSiteErrorFourierInput m p₁ w v) (by norm_num) hLF hamb hδL
    hLip (hfreq.trans heP) (hcoeff.trans heP) W hW ξ hξ reference base cells hZ₀ hrows hscale
  have hmass := allocatedSiteSpatialMass_primitive_bound B U b (rows) hrowdim
    (fun _ => Subtype.val_injective) hb bW M₀ q hqM CM Cf C hp₁ hw hvars hI hn₁ hJ hM₀ hCexp hCMexp hCfexp
  let L := allocatedSiteSpatialMassLog (allocatedComparisonDimension m p₁) w v
  have hL : 0 ≤ L := allocatedSiteSpatialMassLog_nonneg (allocatedComparisonDimension_bounds m hp₁).1 hw hv
  have hOne : 1 ≤ Real.exp L := Real.one_le_exp hL
  have htotal :
      ((Real.toNNReal (coefficientDeckPeriodCap (rowTypes) Q q) *
        CM ^ Fintype.card (LayerSamplerAxis I n) * Cf : ℝ≥0) : ℝ) *
        (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
          Fintype.card (Σ a : LayerSamplerAxis I n, (rowTypes) a.1) +
        2 * (1 / 4 : ℝ) + 1 / 4 ≤ Real.exp (L + 1) := by
    rw [Real.exp_add]
    nlinarith [Real.add_one_le_exp (1 : ℝ)]
  have hfactor : 0 ≤ factor := mul_nonneg
    (pow_nonneg (div_nonneg (by norm_num) smoothProbabilityProfile_pos_zero.le) _)
    (pow_nonneg (pow_nonneg (div_nonneg (by linarith) (Nat.cast_nonneg S.value)) _) _)
  exact hbound.trans (mul_le_mul_of_nonneg_left htotal hfactor)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type uG} [Fintype G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

variable (q : ℕ) [NeZero q]

theorem allocatedWholeProfile_recentered_separated_mass
    {pAccuracy pSampling w v : ℝ} (hpAccuracy : 0 ≤ pAccuracy)
    (hAccuracySampling : pAccuracy ≤ pSampling) (hw : 0 ≤ w) (hv : 0 ≤ v) (hpAccuracyfour : 4 ≤ pAccuracy)
    (hdimSmall : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pAccuracy)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ pAccuracy) (hn₁ : ∀ j, (n j : ℝ) ≤ pAccuracy)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ pAccuracy)
    (M₀ : ℕ) (hqM : q ≤ M₀ ^ (m + 1)) (hM₀ : (M₀ : ℝ) ≤ Real.exp pAccuracy)
    (hS₁ : (S.value : ℝ) ≤ Real.exp pSampling) :
  ∀ {K : ℕ}, AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim K (rowTypes) (rows) → ∀
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type uQ} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d]
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

    (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset (Fin dim) // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
    (CM Cf : ℝ≥0) (_hCM : 1 ≤ (CM : ℝ)) (_hfb : ∀ v, |f v| ≤ Cf)
    (_hCMexp : (CM : ℝ) ≤ Real.exp w) (_hCfexp : (Cf : ℝ) ≤ Real.exp v)
    (_hmask : ∀ y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
      (allocatedPrincipalSides B U b S), ∀ j z, 0 ≤ allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ CM)
    (_hperiod : ∀ j, integerScalarLattice (rowTypes j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hCexp : ∀ j, (C j : ℝ) ≤ Real.exp pAccuracy) (_hVexp : ∀ j, (V j : ℝ) ≤ Real.exp pAccuracy)
    {X : Type uX} [Fintype X] [DecidableEq X]
    {P₀ : ℝ} (_hP : 0 ≤ P₀) (_hn : (Fintype.card X : ℝ) ≤ P₀)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P₀)
    (_hbudget : allocatedSiteErrorFourierOutput m pSampling w v ≤ P₀)
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hmp : ∀ j e, coefficients (p j) e ∈ U j)
    (stride : X → ℕ) (_hs : ∀ x, 0 < stride x)
    {R₁ S₀ ρ : ℝ} (_hS : 0 ≤ S₀) (_hSP : S₀ ≤ Real.exp P₀) (_hρ : 0 < ρ)
    (_hρP : 1 / ρ ≤ Real.exp P₀)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (N : X → ℕ) (_hsize : ∀ x, Real.exp ((P₀ + K) ^ K) ≤ (N x : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) R₁ (U j) (p j))
    (_hR : Real.exp ((P₀ + K) ^ K) ≤ R₁),
    ∀ (W : ℝ) (_hW : 0 ≤ W) (ξ : ℝ), 0 < ξ →
    let H := trimmedSpatialRootScale ρ N stride
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let point := physicalCubeRowSample (O := rowTypes) U d (rows) p hmp
    let profile := fun y z => (allocatedWholeMaskedCoveredProfile (O := rowTypes)
      B U b hR hσ S x (rows) hb o bW d y q f z : ℂ)
    let factor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / (S.value : ℝ)) ^ dim) ^ Fintype.card X
    ∀ (reference : (PrincipalTupleIndex B (layerSamplerDegree I n) →
        Option (Fin dim) → ZMod (residueRefinedPeriod q stride)) →
        PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
      (base : X → ℤ)
      (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)),
    let V₀ := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W ρ ξ N
    (0 < ∑' z, selectedResidueSmoothWeight stride cells V₀ z) →
    (∀ t, Fintype.card (Option (LayerSamplerVariables G I n B)) *
      allocatedPhysicalEntryBudget B U b S (fun _ => 0) ≤ H t) →
    (∀ t, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H t) →
    law.mean (allocatedRecenteredProfileMass (W := W) (τ := ρ) (ξ := ξ)
      B U b S X q stride reference x N base cells point profile) ≤
      factor * Real.exp (allocatedSiteSpatialMassLog (allocatedComparisonDimension m pAccuracy) w v + 1) := by
  intro K hSampling x hb o Q _ bW d _ _ f CM Cf hCM hfb hCMexp hCfexp hmask hperiod C V hC hV
    hCexp hVexp X _ _ P₀ hP₀ hn hdim hbudget _ _ _ μ _ _ ν _ _ p hp hmp stride hs R₁ S₀ ρ
    hS hSP hρ hρP hstride N hsize₁ hrank hR₁ W hW ξ hξ H law point profile factor
    reference base cells V₀ hZ₀ hrows hscale
  have hquarter : (1 / 4 : ℝ)⁻¹ ≤ Real.exp pSampling := by
    norm_num
    linarith [Real.add_one_le_exp pSampling]
  have hrowdim : Fintype.card (Fin dim) ≤ m + 1 := by
    simpa only [Fintype.card_fin] using hdimSmall
  obtain ⟨hLF, hpP, hamb, hδL, hLip, hfreq, hcoeff⟩ :=
    allocatedSiteErrorPrimitive_fourier_budget B U b S (rows) hrowdim
      (fun _ => Subtype.val_injective) hb bW M₀ q hqM 1 CM Cf C V
      (hpAccuracy.trans hAccuracySampling) hw hv (hvars.trans hAccuracySampling)
      (fun j => (hI j).trans hAccuracySampling) (fun j => (hn₁ j).trans hAccuracySampling)
      (fun j => (hJ j).trans hAccuracySampling) (le_refl _)
      (hM₀.trans (Real.exp_le_exp.mpr hAccuracySampling)) hS₁
      (fun j => (hCexp j).trans (Real.exp_le_exp.mpr hAccuracySampling))
      (fun j => (hVexp j).trans (Real.exp_le_exp.mpr hAccuracySampling)) hCMexp hCfexp hquarter
  have heP := Real.exp_le_exp.mpr hbudget
  have hquarterP : 1 / (1 / 4 : ℝ) ≤ Real.exp P₀ := by
    simpa only [one_div] using hquarter.trans (Real.exp_le_exp.mpr (hpP.trans hbudget))
  have hprevious := allocatedWholeProfile_recentered_mass B U b hR hσ S q (K := K) hSampling
  have hbound := @hprevious x hb o Q _ bW d _ _ f CM Cf hCM hfb hmask hperiod C V hC hV
    X _ _ P₀ hP₀ hn hdim _ _ _ μ _ _ ν _ _ p hp hmp stride hs R₁ S₀ ρ (1 / 4)
    hS hSP hρ (by norm_num) hρP hquarterP hstride N hsize₁ hrank hR₁
    (1 / 4) (allocatedSiteErrorFourierInput m pSampling w v) (by norm_num) hLF hamb hδL
    hLip (hfreq.trans heP) (hcoeff.trans heP) W hW ξ hξ reference base cells hZ₀ hrows hscale
  have hmass := allocatedSiteSpatialMass_primitive_bound B U b (rows) hrowdim
    (fun _ => Subtype.val_injective) hb bW M₀ q hqM CM Cf C hpAccuracy hw hvars hI hn₁ hJ hM₀ hCexp hCMexp hCfexp
  let L := allocatedSiteSpatialMassLog (allocatedComparisonDimension m pAccuracy) w v
  have hL : 0 ≤ L := allocatedSiteSpatialMassLog_nonneg (allocatedComparisonDimension_bounds m hpAccuracy).1 hw hv
  have hOne : 1 ≤ Real.exp L := Real.one_le_exp hL
  have htotal :
      ((Real.toNNReal (coefficientDeckPeriodCap (rowTypes) Q q) *
        CM ^ Fintype.card (LayerSamplerAxis I n) * Cf : ℝ≥0) : ℝ) *
        (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
          Fintype.card (Σ a : LayerSamplerAxis I n, (rowTypes) a.1) +
        2 * (1 / 4 : ℝ) + 1 / 4 ≤ Real.exp (L + 1) := by
    rw [Real.exp_add]
    nlinarith [Real.add_one_le_exp (1 : ℝ)]
  have hfactor : 0 ≤ factor := mul_nonneg
    (pow_nonneg (div_nonneg (by norm_num) smoothProbabilityProfile_pos_zero.le) _)
    (pow_nonneg (pow_nonneg (div_nonneg (by linarith) (Nat.cast_nonneg S.value)) _) _)
  exact hbound.trans (mul_le_mul_of_nonneg_left htotal hfactor)

end Erdos3.VectorPolynomial

end

end OAI
