import OAI.Combinatorics.Progressions.Dynamics.AllocatedIdealSourceBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory Polynomial
open scoped BigOperators Classical NNReal

universe uX

def AllocatedIdealDensitySourceFamilyAt (m dim A T K : ℕ) : Prop :=
    ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    {D p e w E : ℝ}
    (_hdim : AllocatedComparisonDimensions (G := G) B (Fin dim)
      (fun j : Fin m => BoundedBooleanJet (Fin dim) (j.val + 1)) D)
    (_hp : 0 ≤ p) (_he : 0 ≤ e) (_hw : 0 ≤ w) (_hE : 0 ≤ E)
    (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp p) (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp p),
    let S := allocatedIdealScale (G := G) B U b hR hσ D p e w E
    let P := allocatedIdealSourceBudget m D p e w E
    (S.value : ℝ) ≤ Real.exp (allocatedIdealScaleLog m D p e w E) ∧
    ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    {M : ℕ} (_hperiod : HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range M),
    ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin dim)) U)] [BorelSpace (SiteTorus (Finset (Fin dim)) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hCp : ∀ j, (C j : ℝ) ≤ Real.exp p) (_hVp : ∀ j, (V j : ℝ) ≤ Real.exp p)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)],
    let density := allocatedCoefficientDensity B U b hb o hR hσ S
    let cap := (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let cover := quotientIntegerCover (coefficientIntegerLattice U) d
    let ξ := Measure.pi (fun j => Measure.pi (fun _ : BoundedBooleanJet (Fin dim) (j.val + 1) => ν j))
    AllocatedSourceNumerics B U b S C V P ∧
    ∃ g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S) →
        EuclideanJetLayers U (fun j => BoundedBooleanJet (Fin dim) (j.val + 1)) → ℝ,
      (∀ y, Continuous (g y)) ∧ (∀ y z, g y z ∈ Set.Icc (0 : ℝ) cap) ∧
      (∀ y, Integrable (g y) ξ) ∧ (∀ y, (∫ z, g y z ∂ξ) = 1) ∧
      (∀ y, (realDensityMeasure μ (fun z => density (cover z))).map
        (euclideanCoefficientJetMap U (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y)
          (fun j => (Subtype.val : BoundedBooleanJet (Fin dim) (j.val + 1) → Finset (Fin dim)))) =
            realDensityMeasure ξ (g y)) ∧
      (∀ y, physicalDensityProjection.{_, _, uX, 0} U (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U b S x y) d density (g y)) ∧
        AllocatedOriginalSourceProjectionAt.{uX} B U b hR hσ S x hb o d g P K ∧
        ∀ y,
        (∀ {δ : ℝ} (_hδ : 0 < δ) (_hδP : δ⁻¹ ≤ Real.exp P),
        let Q := allocatedJetFourierBudget m dim A P
        ∃ (Index : Type) (inst : Fintype Index), let _ := inst
        ∃ (frequency : Index → ∀ j, (Fin dim →₀ ℕ) → J j → ℤ) (coeff : Index → ℂ),
          (∀ a j e, e.degree ≤ j.val + 1 → ∀ t, |(frequency a j e t : ℝ)| ≤ Real.exp Q) ∧
          (∑ a, ‖coeff a‖) ≤ Real.exp Q ∧
          ∀ z : CoefficientTorus (K := Fin dim) U,
            ‖(g y (standardPhysicalJetMap U z) : ℂ) - coefficientTorusFourierSum U frequency coeff z‖ ≤ δ) ∧
        ∀ {X : Type uX} [Fintype X] [DecidableEq X]
          {Pmass : ℝ} (_hQ : allocatedJetFourierBudget m dim A P ≤ Pmass)
          (_hX : (Fintype.card X : ℝ) ≤ Pmass)
          (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ Pmass)
          (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
          (hm : ∀ j e, coefficients (p j) e ∈ U j)
          (N stride : X → ℕ) (_hs : ∀ t, 0 < stride t)
          {Rrank W τ ξ₀ ρ : ℝ} (_hW : 0 ≤ W) (_hτ : 0 < τ) (_hξ : ξ₀ ≤ 1) (_hρ : 0 < ρ)
          (_hτP : 1 / τ ≤ Real.exp Pmass) (_hstride : ∀ t, (stride t : ℝ) ≤ Real.exp Pmass)
          (_hsize : ∀ t, Real.exp ((Pmass + T) ^ T) ≤ (N t : ℝ))
          (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) Rrank (U j) (p j))
          (_hRank : Real.exp ((Pmass + T) ^ T) ≤ Rrank)
          (_hspatial : ∀ t, 8 * (1 + W) * (stride t : ℝ) * ρ ≤ (ξ₀ * τ) * (N t : ℝ))
          (_hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
          (_hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
            (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
          (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
          (base : X → ℤ)
          (residue : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride),
          let H := trimmedSpatialRootScale τ N stride
          (∑ v ∈ spatialWindow H 4, g y (physicalCubeEuclideanSample U d p hm
              (physicalResidueReconstruction (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y₀)
                (allocatedPhysicalCubeDirections B U b S x y₀) base
                (boundedColumnResidueRepresentative stride residue) stride v))) ≤
            (4 * (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X)) *
              (∏ t, ∏ _i : Unit ⊕ Fin dim, H t)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

universe uX

theorem exists_allocated_ideal_density_source_family (m dim : ℕ) :
    ∃ A T K : ℕ, 2 ≤ A ∧ 2 ≤ T ∧ 2 ≤ K ∧ AllocatedIdealDensitySourceFamilyAt.{uX} m dim A T K := by
  obtain ⟨A, T, K, hA, hT, hK, hfamily⟩ := exists_allocated_density_source_family.{uX} m dim
  refine ⟨A, T, K, hA, hT, hK, ?_⟩
  unfold AllocatedIdealDensitySourceFamilyAt
  intro G _ _ I _ _ n B _ _ J _ U b R σ hR hσ D p e w E hdim hp he hw hE hRi hσi S P
  obtain ⟨hP1, hDP, _hpP, hLP, _hrootP⟩ :=
    allocatedIdealSourceBudget_bounds m hdim.nonneg hp he hw hE
  have hP : 0 ≤ P := (by norm_num : (0 : ℝ) ≤ 1).trans hP1
  have hS : (S.value : ℝ) ≤ Real.exp (allocatedIdealScaleLog m D p e w E) :=
    allocatedIdealScale_upper B U b hR hσ hdim hp he hw hE hRi hσi
  refine ⟨hS, ?_⟩
  intro x M hperiod
  obtain ⟨d, hd, hdb, hfamily⟩ := hfamily B U b S x hP (hdim.kernel_variables.trans hDP)
    (hS.trans (Real.exp_le_exp.mpr hLP)) hperiod
  refine ⟨d, hd, hdb, ?_⟩
  intro _ _ _ _ _ _ hb o C V hC hV hCp hVp hσ1 Cinv hCinv hchart hsmall μ _ _ ν _ _
    density cap cover ξ
  have hnum : AllocatedSourceNumerics B U b S C V P :=
    allocatedIdealSource_numerics B U b o hdim hp he hw hE hR hσ hRi hσi C V hCp hVp
  obtain ⟨g, hgc, hgb, hgi, hgm, hglaw, hproject, hdata⟩ :=
    hfamily hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ ν
  refine ⟨hnum, g, hgc, hgb, hgi, hgm, hglaw, hproject, ?_⟩
  exact hdata hnum.degree hnum.variable_count hnum.radius_inv hnum.width_inv hnum.coefficients
    hnum.real_axes hnum.integer_axes hnum.ambient_axes hnum.profile hnum.chart hnum.covolume

end Erdos3.VectorPolynomial

end

end OAI
