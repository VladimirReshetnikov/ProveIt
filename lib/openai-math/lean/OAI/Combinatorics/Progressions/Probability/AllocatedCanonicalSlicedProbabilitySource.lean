import OAI.Combinatorics.Progressions.Geometry.AllocatedSlicedSpatialToCoarse
import OAI.Combinatorics.Progressions.Sampling.PhysicalRowsProbabilityMassSampling

namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uX uJ uO uG uI uB

open BooleanCubeKernel MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type uX) [Fintype X] [DecidableEq X] (modulus : ℕ) (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type uO} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset (Fin dim))
variable (hinj : ∀ j, Function.Injective (rows j)) (hcard : ∀ j a, (rows j a).card ≤ j.val + 1)
variable (cover : ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
variable (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
local notation "point" => physicalCubeRowSample U cover rows poly hm
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

variable [CompactSpace (CoefficientTorus (K := Fin dim) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin dim) U)]
variable [BorelSpace (CoefficientTorus (K := Fin dim) U)]
variable (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
local notation "jetHaar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))

include hinj hcard hp μ hW in
omit [DecidableEq G] [NeZero modulus] in
theorem allocatedRecentered_probability_mass_of_rank [DecidableEq G] [NeZero modulus]
    (law : FiniteProbabilityWeights fullTuple)
    (g : fullTuple → EuclideanJetLayers U O → ℝ)
    (hg0 : ∀ y z, 0 ≤ g y z) (hgi : ∀ y, Integrable (g y) jetHaar)
    (hgmass : ∀ y, (∫ z, g y z ∂jetHaar) = 1)
    (Lf Cf : ℝ≥0)
    (hambient : ∀ y, ∃ f : (JetAmbientIndex O J → UnitAddCircle) → ℂ,
      LipschitzWith Lf f ∧ (∀ z, ‖f z‖ ≤ Cf) ∧
      ∀ z, (g y z : ℂ) = f (coveredJetAmbientTorus U 1 z))
    (hq : ∀ t, 0 < q t) (hN : ∀ t, 0 < N t) (hτ : 0 < τ) (hξ : 0 < ξ)
    {P Rrank Sstride εsample η : ℝ}
    (hP : 0 ≤ P) (hX : (Fintype.card X : ℝ) ≤ P)
    (hframe : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P)
    (hcover : 0 < cover) (hcoverP : (cover : ℝ) ≤ Real.exp P)
    (hSstride : 0 ≤ Sstride) (hSstrideP : Sstride ≤ Real.exp P)
    (hstride : ∀ i, (q i : ℝ) ≤ Sstride)
    (hε : 0 < εsample) (hτP : 1 / τ ≤ Real.exp P) (hεP : 1 / εsample ≤ Real.exp P)
    (hsize : ∀ i, Real.exp ((P + Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,uO,max uG uI uB} m dim)) ^ Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,uO,max uG uI uB} m dim)) ≤ (N i : ℝ))
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (hRrank : Real.exp ((P + Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,uO,max uG uI uB} m dim)) ^ Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,uO,max uG uI uB} m dim)) ≤ Rrank)
    (hη : 0 < η) (hamb : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ P)
    (hLf : (Lf : ℝ) ≤ Real.exp P) (hCf : (Cf : ℝ) ≤ Real.exp P)
    (hjet : ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp P)
    (hηP : η⁻¹ ≤ Real.exp P) (hsmall : 2 * η + εsample ≤ 3)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
    (hrowsize : ∀ y : fullTuple, ∀ t i,
      (∑ k, |(physicalCubeCoefficient (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U b S x y) i k : ℝ)|) ≤ trimmedSpatialRootScale τ N q t)
    (hscale : ∀ t, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * trimmedSpatialRootScale τ N q t) :
    law.mean (allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x N base cells point (fun y z => (g y z : ℂ))) ≤
      coarseReferenceMassConstant dim X W S.value := by
  apply allocatedRecenteredProfileMass_le_of_window_law B U b S X modulus q wholeReference
    x N hW base cells point hN hq hτ hξ hmass law (fun y z => (g y z : ℂ))
  intro y _ a
  obtain ⟨f, hf, hfb, hactual⟩ := hambient y
  let y₀ := wholeReference (principalResidueLabel refined y)
  have hwidth (z : Option (Fin dim) × X) : τ * (N z.2 : ℝ) ≤
      referenceJetEnvelopeWidths q (trimmedSpatialRootScale τ N q) z := by
    rw [referenceJetEnvelopeWidths_trimmed q N hq τ z]
    nlinarith [mul_pos hτ (Nat.cast_pos.mpr (hN z.2))]
  have hsample := (Classical.choose_spec
    (exists_translated_physical_jet_density_window_mass.{uX,uJ,uO,max uG uI uB} m dim)).2
      (I := X) (J := J) (O := O)
  have he := hsample rows hinj hcard hP hX hframe U μ ν base poly hp hm cover hcover hcoverP q hq
    hSstride hSstrideP hτ hε hτP hεP hstride (fun i => (N i : ℝ)) hsize hrank hRrank
    (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y₀)
    (allocatedPhysicalCubeDirections B U b S x y₀) a.val (trimmedSpatialRootScale τ N q)
    (fun t => (trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)).1)
    (hrowsize y₀) hscale hwidth (g y) (hg0 y) (hgi y) (hgmass y)
    f Lf Cf hf hfb hactual hη hamb hLf hCf hjet hηP hsmall
  simpa only [Complex.norm_real, Real.norm_of_nonneg (hg0 y _),
    allocatedWholeResidueReconstruction, y₀] using he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uX uJ uO uG uI uB
open BooleanCubeKernel MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type uX) [Fintype X] [DecidableEq X] (modulus : ℕ) (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type uO} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset (Fin dim))
variable (hinj : ∀ j, Function.Injective (rows j)) (hcard : ∀ j a, (rows j a).card ≤ j.val + 1)
variable (cover : ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
variable (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
local notation "point" => physicalCubeRowSample U cover rows poly hm
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

variable (hN : ∀ t, 0 < N t) (hq : ∀ t, 0 < q t) (hτ : 0 < τ)
variable {C₀ ρ δ : ℝ} (hρ : 0 < ρ)
variable (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
variable (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀) (hWC : W ≤ C₀)
variable (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
variable (hsize : ∀ t, 8 * (1 + W) * (q t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ))
variable (hmesh : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
variable (hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
variable (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
  pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
    (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
variable (hδ : 0 ≤ δ)
variable (hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
variable (hρmove : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ δ * ρ)
variable (hmeshpos : 0 < mesh)
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (htest : ∀ v, ‖test v‖ ≤ 1)

local notation "spatialError" => allocatedTupleSpatialError (Fintype.card X) selection
  (PrincipalTupleIndex B (layerSamplerDegree I n)) M modulus C₀ ρ ξ W δ mesh
local notation "boundaryError" => (24 * (probabilityProfileLipschitz : ℝ) *
  Fintype.card (Option (LayerSamplerVariables G I n B) × X) / ρ)

variable [CompactSpace (CoefficientTorus (K := Fin dim) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin dim) U)]
variable [BorelSpace (CoefficientTorus (K := Fin dim) U)]
variable (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
local notation "jetHaar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))

include hinj hcard hp μ hN hq hτ hρ hbudget hC₀ hLC hWC hξ hξ1 hsize hmesh hρ8 hperiod hδ hρshift hρmove hmeshpos htest in
theorem allocatedNarrowTrimmed_probability_coarse_source
    (law : FiniteProbabilityWeights fullTuple)
    (hwhole : ∀ y, law.weight y ≠ 0 →
      principalResidueLabel refined (wholeReference (principalResidueLabel refined y)) = principalResidueLabel refined y)
    (g : fullTuple → EuclideanJetLayers U O → ℝ)
    (hg0 : ∀ y z, 0 ≤ g y z) (hgi : ∀ y, Integrable (g y) jetHaar)
    (hgmass : ∀ y, (∫ z, g y z ∂jetHaar) = 1)
    (Lf Cf : ℝ≥0)
    (hambient : ∀ y, ∃ f : (JetAmbientIndex O J → UnitAddCircle) → ℂ,
      LipschitzWith Lf f ∧ (∀ z, ‖f z‖ ≤ Cf) ∧
      ∀ z, (g y z : ℂ) = f (coveredJetAmbientTorus U 1 z))
    {Pmass Rrank : ℝ} (hPmass : 0 ≤ Pmass)
    (hXmass : (Fintype.card X : ℝ) ≤ Pmass)
    (hframe : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ Pmass)
    (hcover : 0 < cover) (hcoverP : (cover : ℝ) ≤ Real.exp Pmass)
    (hstrideP : ∀ i, (q i : ℝ) ≤ Real.exp Pmass)
    (hτP : 1 / τ ≤ Real.exp Pmass)
    (hsizeMass : ∀ i, Real.exp ((Pmass + Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,uO,max uG uI uB} m dim)) ^ Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,uO,max uG uI uB} m dim)) ≤ (N i : ℝ))
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (hRrank : Real.exp ((Pmass + Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,uO,max uG uI uB} m dim)) ^ Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,uO,max uG uI uB} m dim)) ≤ Rrank)
    (hamb : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ Pmass)
    (hLf : (Lf : ℝ) ≤ Real.exp Pmass) (hCf : (Cf : ℝ) ≤ Real.exp Pmass)
    (hjet : ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp Pmass)
    {Cg Z : ℝ} (hCg : 0 ≤ Cg)
    (hcap : ∀ y, law.weight y ≠ 0 → ∀ v, ‖(g y (point v) : ℂ)‖ ≤ Cg) (hZ : 1 / 2 ≤ Z) {target κ : ℝ}
    (hboundary : Cg * boundaryError ≤ normalizedSpatialShare target / 2)
    (hsite : spatialError * coarseReferenceMassConstant dim X W S.value ≤ normalizedSpatialShare target / 2)
    {p E : ℝ} (hpBudget : 0 ≤ p) (hE : 0 ≤ E)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hdim : ((dim + 1 : ℕ) : ℝ) ≤ p)
    (hMP : (M : ℝ) ≤ Real.exp p) (hmodulus : modulus ≤ M ^ (m + 1))
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp p)
    (hWscale : W ≤ Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ))
    (hmeshCoarse : mesh ≤ allocatedEarlyRecenteredMesh X selection M modulus p E) :
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let hV := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
    let projected := fun y => ∑' z, ((selectedResidueSmoothPMF q cells V hV hmass z).toReal : ℂ) *
        (test (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y) base z) *
          (g y (point (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U b S x y) base z)) : ℂ))
    κ ≤ (law.complexMean projected / (Z : ℂ)).re →
    Z * (κ - Real.exp (-target)) - Real.exp (-E) ≤
      (law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW
          (allocatedEarlyRecenteredMesh X selection M modulus p E) base cells point test (fun y z => (g y z : ℂ)))).re := by
  intro V hV projected hsource
  have hgeom (y : fullTuple) (t : X) := allocatedNarrow_reference_jet_geometry B U b S (fun _ => 0) x y
    N q hN hq hW hτ hξ1 hρ hsize hρ8 hρshift t
  have hscale (t : X) : 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * trimmedSpatialRootScale τ N q t := by
    obtain ⟨y, _⟩ := law.exists_weight_pos
    exact (hgeom y t).2.2.2
  have hmassBound := allocatedRecentered_probability_mass_of_rank B U b S X modulus q wholeReference
    x N hW base cells rows hinj hcard cover poly hp hm μ ν law g hg0 hgi hgmass Lf Cf hambient
    hq hN hτ hξ hPmass hXmass hframe hcover hcoverP (Real.exp_nonneg Pmass) le_rfl hstrideP
    (by norm_num : (0 : ℝ) < 1) hτP (by simpa using Real.one_le_exp hPmass)
    hsizeMass hrank hRrank (by norm_num : (0 : ℝ) < 1) hamb hLf hCf hjet
    (by simpa using Real.one_le_exp hPmass) (by norm_num : (2 : ℝ) * 1 + 1 ≤ 3)
    hmass (fun y t => (hgeom y t).2.1) hscale
  exact allocatedNarrowTrimmed_early_coarse_source_law B U b S X modulus q wholeReference
    x hM selection hx N hW mesh base cells point test hN hq hτ hρ hbudget hC₀ hLC hWC hξ hξ1
    hsize hmesh hρ8 hperiod hδ hρshift hρmove hmeshpos hmass htest law hwhole
    (fun y z => (g y z : ℂ)) hCg hcap hZ hmassBound hboundary hsite
    hpBudget hE hG hX hdim hMP hmodulus hvars hWscale hmeshCoarse hsource

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uX uJ uO uG uI uB
open BooleanCubeKernel MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type uX) [Fintype X] [DecidableEq X] (modulus : ℕ) (q : X → ℕ)
local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (label₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) →
  ZMod (residueRefinedPeriod modulus q))
variable (hcell : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel (residueRefinedPeriod modulus q) y = label₀)))
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hy₀ : 0 < (containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S)
  hH hsubset (residueRefinedPeriod modulus q) label₀ hcell).weight y₀)
local notation "law" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S)
  hH hsubset refined label₀ hcell
local notation "wholeReference" => (fun _ : labels => y₀)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (hcanonical : modulus = kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hx m))
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type uO} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset (Fin dim))
variable (hinj : ∀ j, Function.Injective (rows j)) (hcard : ∀ j a, (rows j a).card ≤ j.val + 1)
variable (cover : ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
variable (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
local notation "point" => physicalCubeRowSample U cover rows poly hm
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

variable (hN : ∀ t, 0 < N t) (hq : ∀ t, 0 < q t) (hτ : 0 < τ)
variable {C₀ ρ δ : ℝ} (hρ : 0 < ρ)
variable (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
variable (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀) (hWC : W ≤ C₀)
variable (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
variable (hsize : ∀ t, 8 * (1 + W) * (q t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ))
variable (hmesh : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
variable (hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
variable (hδ : 0 ≤ δ)
variable (hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
variable (hρmove : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ δ * ρ)
variable (hmeshpos : 0 < mesh)
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (htest : ∀ v, ‖test v‖ ≤ 1)

local notation "spatialError" => allocatedTupleSpatialError (Fintype.card X) selection
  (PrincipalTupleIndex B (layerSamplerDegree I n)) M modulus C₀ ρ ξ W δ mesh
local notation "boundaryError" => (24 * (probabilityProfileLipschitz : ℝ) *
  Fintype.card (Option (LayerSamplerVariables G I n B) × X) / ρ)

variable [CompactSpace (CoefficientTorus (K := Fin dim) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin dim) U)]
variable [BorelSpace (CoefficientTorus (K := Fin dim) U)]
variable (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
local notation "jetHaar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))

include hinj hcard hp μ hN hq hτ hρ hbudget hC₀ hLC hWC hξ hξ1 hsize hmesh hρ8
  hcanonical hδ hρshift hρmove hmeshpos htest hy₀ in
theorem allocatedCanonicalSlice_probability_coarse_source
    (g : fullTuple → EuclideanJetLayers U O → ℝ)
    (hg0 : ∀ y z, 0 ≤ g y z) (hgi : ∀ y, Integrable (g y) jetHaar)
    (hgmass : ∀ y, (∫ z, g y z ∂jetHaar) = 1)
    (Lf Cf : ℝ≥0)
    (hambient : ∀ y, ∃ f : (JetAmbientIndex O J → UnitAddCircle) → ℂ,
      LipschitzWith Lf f ∧ (∀ z, ‖f z‖ ≤ Cf) ∧
      ∀ z, (g y z : ℂ) = f (coveredJetAmbientTorus U 1 z))
    {Pmass Rrank : ℝ} (hPmass : 0 ≤ Pmass)
    (hXmass : (Fintype.card X : ℝ) ≤ Pmass)
    (hframe : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ Pmass)
    (hcover : 0 < cover) (hcoverP : (cover : ℝ) ≤ Real.exp Pmass)
    (hstrideP : ∀ i, (q i : ℝ) ≤ Real.exp Pmass)
    (hτP : 1 / τ ≤ Real.exp Pmass)
    (hsizeMass : ∀ i, Real.exp ((Pmass + Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,uO,max uG uI uB} m dim)) ^ Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,uO,max uG uI uB} m dim)) ≤ (N i : ℝ))
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (hRrank : Real.exp ((Pmass + Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,uO,max uG uI uB} m dim)) ^ Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,uO,max uG uI uB} m dim)) ≤ Rrank)
    (hamb : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ Pmass)
    (hLf : (Lf : ℝ) ≤ Real.exp Pmass) (hCf : (Cf : ℝ) ≤ Real.exp Pmass)
    (hjet : ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp Pmass)
    {Cg Z : ℝ} (hCg : 0 ≤ Cg)
    (hcap : ∀ y, (law).weight y ≠ 0 → ∀ v, ‖(g y (point v) : ℂ)‖ ≤ Cg) (hZ : 1 / 2 ≤ Z) {target κ : ℝ}
    (hboundary : Cg * boundaryError ≤ normalizedSpatialShare target / 2)
    (hsite : spatialError * coarseReferenceMassConstant dim X W S.value ≤ normalizedSpatialShare target / 2)
    {p E : ℝ} (hpBudget : 0 ≤ p) (hE : 0 ≤ E)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hdim : ((dim + 1 : ℕ) : ℝ) ≤ p)
    (hMP : (M : ℝ) ≤ Real.exp p)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp p)
    (hWscale : W ≤ Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ))
    (hmeshCoarse : mesh ≤ allocatedEarlyRecenteredMesh X selection M modulus p E) :
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let hV := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
    let projected := fun y => ∑' z, ((selectedResidueSmoothPMF q cells V hV hmass z).toReal : ℂ) *
        (test (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y) base z) *
          (g y (point (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U b S x y) base z)) : ℂ))
    κ ≤ ((law).complexMean projected / (Z : ℂ)).re →
    Z * (κ - Real.exp (-target)) - Real.exp (-E) ≤
      ((law).complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW
          (allocatedEarlyRecenteredMesh X selection M modulus p E) base cells point test (fun y z => (g y z : ℂ)))).re := by
  have hmodulus : modulus ≤ M ^ (m + 1) := by
    rw [hcanonical]
    exact kernelPeriodCandidate_le _ _
  have hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection) := by
    rw [hcanonical]
    exact (goodKernelUniformCandidate_spec.{0,uG,0} selection x hx m).1 _
  have hwhole : ∀ y, (law).weight y ≠ 0 →
      principalResidueLabel refined (wholeReference (principalResidueLabel refined y)) =
        principalResidueLabel refined y := by
    intro y hy
    exact containedSupportedProgressionLaw_residue_eq B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S)
      hH hsubset refined label₀ hcell y₀ y hy₀.ne' hy
  exact allocatedNarrowTrimmed_probability_coarse_source B U b S X modulus q wholeReference
    x hM selection hx N hW mesh base cells rows hinj hcard cover poly hp hm test
    hN hq hτ hρ hbudget hC₀ hLC hWC hξ hξ1 hsize hmesh hρ8 hperiod hδ hρshift hρmove
    hmeshpos hmass htest μ ν (law) hwhole g hg0 hgi hgmass Lf Cf hambient
    hPmass hXmass hframe hcover hcoverP hstrideP hτP hsizeMass hrank hRrank hamb hLf hCf hjet
    hCg hcap hZ hboundary hsite hpBudget hE hG hX hdim hMP hmodulus hvars hWscale hmeshCoarse

end Erdos3.VectorPolynomial

end

end OAI
