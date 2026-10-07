import OAI.Combinatorics.Progressions.Estimates.AllocatedRowsAmbientProjectedFamilyMultiple
import OAI.Combinatorics.Progressions.Estimates.AllocatedSlicedRowsProjectedSource

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal
universe uX

def AllocatedSlicedSourceProjection {m q : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (x : G → IntegerScalarCubeBox (Fin q) S.value)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
    (d : ℕ)
    (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U b S) →
      EuclideanJetLayers U (fun j => {t : Finset (Fin q) // t ∈ boundedBooleanJetRows (Fin q) (j.val + 1)}) → ℝ)
    (Asample : ℕ) (P : ℝ) : Prop :=
    ∀ {W : ℝ}, 1 ≤ P → ∀ (_hm : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hW : 0 ≤ W) (_hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (_hWP : W ≤ Real.exp P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    {X : Type uX} [Fintype X] [DecidableEq X]
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {τ ξ : ℝ} (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (hN : ∀ i, 0 < N i) (_hsize : ∀ d, Real.exp ((P + Asample) ^ Asample) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + Asample) ^ Asample) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty)
    (bases : Finset (X → ℤ)) (_hbases : bases.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let Z := selectedJointDensityMass bases stride T widths
      (allocatedJointBaseDensity B U b hb o hR hσ S X p hm)
    ∃ hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z,
      (|Z - 1| ≤ Real.exp (-P) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2) ∧
      ∀ (law : FiniteProbabilityWeights (PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U b S))) (signal : (X → ℤ) → ℂ),
      (∀ v, ‖signal v‖ ≤ 1) → ∀ {κ : ℝ},
      κ ≤ (law.complexMean (fun y => allocatedSlicedTupleValue B U b hb o hR hσ S X p hm
        N hN _hW _hτ _hξ stride T hmass bases x y signal)).re →
      ∃ base ∈ bases,
        let projected := fun y => ∑' z,
          ((selectedResidueSmoothPMF stride T widths
            (narrowTrimmedSpatialWidths_pos _hW _hτ _hξ N hN) hmass z).toReal : ℂ) *
            (physicalCubeSiteTest (integerSelfSiteTest q signal) (physicalCubeRootDifferences
              (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
              (allocatedPhysicalCubeDirections B U b S x y) base z) *
            (g y (physicalCubeRowSample U d (fun j =>
              (Subtype.val : {t : Finset (Fin q) // t ∈ boundedBooleanJetRows (Fin q) (j.val + 1)} → Finset (Fin q))) p hm
              (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
                (allocatedPhysicalCubeDirections B U b S x y) base z)) : ℂ))
        κ - Real.exp (-P) ≤ (law.complexMean projected / (Z : ℂ)).re

theorem exists_allocated_sliced_constructed_projection (m q : ℕ) :
    ∃ A Asample : ℕ, 2 ≤ A ∧ 2 ≤ Asample ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (x : G → IntegerScalarCubeBox (Fin q) S.value)
    {P : ℝ} (_hP : 0 ≤ P) (_hG : (Fintype.card G : ℝ) ≤ P)
    (_hL : (S.value : ℝ) ≤ Real.exp P)
    {M : ℕ} (_hperiod : HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range M),
    ∀ (period : ℕ), 0 < period → (period : ℝ) ≤ Real.exp P →
    ∃ d : ℕ, period ∣ d ∧ 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + (q + 2 : ℕ) + A) ^ A) ∧
    ∀ [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin q)) U)] [BorelSpace (SiteTorus (Finset (Fin q)) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    [CompactSpace (CoefficientTorus (K := Fin q) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin q) U)]
    [BorelSpace (CoefficientTorus (K := Fin q) U)]
    (μrows : Measure (CoefficientTorus (K := Fin q) U))
    [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows],
    let density := allocatedCoefficientDensity B U b hb o hR hσ S
    let cap := (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let cover := quotientIntegerCover (coefficientIntegerLattice U) d
    let ξ := Measure.pi (fun j => Measure.pi (fun _ : {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (j.val + 1)} => ν j))
    let densityLip := Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) *
      allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V *
      allocatedAmbientFactorCap (G := G) B R σ S.value V ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let sectionLip := (Fintype.card (Finset (Fin q)) : ℝ≥0) *
      Real.toNNReal (Real.exp ((P + (q + 2 : ℕ) + A) ^ A))
    let reconstructionLip := ∑ j : Fin m, (Fintype.card (BoundedBooleanJet (Fin q) (j.val + 1)) : ℝ≥0)
    let Row := fun j : Fin m => {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (j.val + 1)}
    let Tuple := PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U b S)
    ∃ g : Tuple → EuclideanJetLayers U Row → ℝ,
      (∀ y, Continuous (g y)) ∧
      (∀ y z, g y z ∈ Set.Icc (0 : ℝ) cap) ∧
      (∀ y, Integrable (g y) ξ) ∧
      (∀ y, (∫ z, g y z ∂ξ) = 1) ∧
      (∀ y, (realDensityMeasure μ (fun z => density (cover z))).map
        (euclideanCoefficientJetMap U (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y)
          (fun j => (Subtype.val : Row j → Finset (Fin q)))) = realDensityMeasure ξ (g y)) ∧
      (∀ y, physicalDensityProjection.{_, _, uX, 0} U (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U b S x y) d density
        (fun z => g y ((physicalRowsStandardEquiv U).symm z))) ∧
      (∀ y, ∃ F : (JetAmbientIndex Row J → UnitAddCircle) → ℂ,
        LipschitzWith (densityLip * sectionLip * reconstructionLip) F ∧
        (∀ z, ‖F z‖ ≤ cap) ∧
        ∀ z, (g y z : ℂ) = F (coveredJetAmbientTorus U 1 z)) ∧
      (∀ law : FiniteProbabilityWeights Tuple,
        ∃ F : (JetAmbientIndex Row J → UnitAddCircle) → ℂ,
          LipschitzWith (densityLip * sectionLip * reconstructionLip) F ∧
          (∀ z, ‖F z‖ ≤ cap) ∧
          ∀ z, law.complexMean (fun y => (g y z : ℂ)) = F (coveredJetAmbientTorus U 1 z)) ∧
      AllocatedSlicedSourceProjection.{uX} B U b S x hb o hR hσ C V d g Asample P := by
  obtain ⟨A, hA, hcover⟩ := exists_allocated_rows_ambient_projected_family_multiple m q
  obtain ⟨An, hAn, hnorm⟩ := exists_allocated_narrow_normalization m
  obtain ⟨Ap, hAp, hprojectSource⟩ := exists_allocated_sliced_rows_projected_source.{uX} m q
  refine ⟨A, max An Ap, hA, hAn.trans (le_max_left _ _), ?_⟩
  intro G _ _ I _ n B _ J _ U b R σ S x P hP hG hL M hperiod period hp hpP
  obtain ⟨d, hdiv, hd, hdb, hconstruct⟩ := hcover B U b S (fun _ => 0) x hP hG
    (fun _ => by simpa using Real.exp_nonneg P) hL hperiod period hp hpP
  refine ⟨d, hdiv, hd, hdb, ?_⟩
  intro _ _ _ _ _ _ hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ _ _ ν _ _
    _ _ _ μrows _ _ density cap cover ξhaar densityLip sectionLip reconstructionLip Row Tuple
  obtain ⟨g, hgc, hgb, hgi, hgm, hglaw, hprojection, hambient, hmean⟩ :=
    hconstruct hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ ν μrows
  refine ⟨g, hgc, hgb, hgi, hgm, hglaw, hprojection, hambient, hmean, ?_⟩
  unfold AllocatedSlicedSourceProjection
  intro W hPone hmSize hK hW hroot hWP hRP hσP hcount hI hn hJ hAP hCP hVP
    X _ _ hX hdim p hpoly hm stride hs hsP τ ξ hτ hτP hξ hξ1 hξP N hN hsize
    rank hrank hRank T hT bases hbases widths Z
  have hnCut := Real.exp_le_exp.mpr (shifted_power_self_mono hP (by omega : 1 ≤ An)
    (le_max_left An Ap))
  have hpCut := Real.exp_le_exp.mpr (shifted_power_self_mono hP (by omega : 1 ≤ Ap)
    (le_max_right An Ap))
  obtain ⟨hwidths, hmass, _, hglobal⟩ := hnorm B U b S hb o μ ν hR hσ hσ1 C V hC hV
    Cinv hCinv hchart hsmall hP hmSize hK hX hdim hRP hσP hcount hI hn hJ hAP hL hCP hVP
    p hpoly hm stride hs hsP hW hWP hτ hτP hξ hξ1 hξP N (fun i => hnCut.trans (hsize i))
    hrank (hnCut.trans hRank) T hT
  have hnormal := hglobal bases hbases
  change |Z - 1| ≤ Real.exp (-P) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧
    0 < Z ∧ Z⁻¹ ≤ 2 at hnormal
  refine ⟨hmass, hnormal, ?_⟩
  intro law signal hsignal κ hsource
  have hZi : Z⁻¹ ≤ Real.exp P := hnormal.2.2.2.trans
    (by linarith [Real.add_one_le_exp P])
  exact hprojectSource B U b S x hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall
    hP hmSize hK hW hroot hWP hL hRP hσP hcount hI hn hJ hAP hCP hVP hperiod hX hdim
    p hpoly hm stride hs hsP hτ hτP hξ hξ1 hξP N hN (fun i => hpCut.trans (hsize i))
    hrank (hpCut.trans hRank) signal hsignal T hT bases hbases d g hprojection hwidths hmass law
    hnormal.2.2.1 hZi hsource

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal
universe uX

theorem exists_allocated_canonical_constructed_projection (m q : ℕ) :
    ∃ A Asample : ℕ, 2 ≤ A ∧ 2 ≤ Asample ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (x : G → IntegerScalarCubeBox (Fin q) S.value)
    {P : ℝ} (_hP : 0 ≤ P) (_hG : (Fintype.card G : ℝ) ≤ P)
    (_hL : (S.value : ℝ) ≤ Real.exp P)
    {M : ℕ} (selection : Fin q ↪ G)
    (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
    {Pk : ℝ} (_hMk : (M : ℝ) ≤ Real.exp Pk) (_hPk : ((m + 1 : ℕ) : ℝ) * Pk ≤ P),
    let period := kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hx m)

    ∃ d : ℕ, period ∣ d ∧ 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + (q + 2 : ℕ) + A) ^ A) ∧
    ∀ [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin q)) U)] [BorelSpace (SiteTorus (Finset (Fin q)) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    [CompactSpace (CoefficientTorus (K := Fin q) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin q) U)]
    [BorelSpace (CoefficientTorus (K := Fin q) U)]
    (μrows : Measure (CoefficientTorus (K := Fin q) U))
    [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows],
    let density := allocatedCoefficientDensity B U b hb o hR hσ S
    let cap := (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let cover := quotientIntegerCover (coefficientIntegerLattice U) d
    let ξ := Measure.pi (fun j => Measure.pi (fun _ : {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (j.val + 1)} => ν j))
    let densityLip := Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) *
      allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V *
      allocatedAmbientFactorCap (G := G) B R σ S.value V ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let sectionLip := (Fintype.card (Finset (Fin q)) : ℝ≥0) *
      Real.toNNReal (Real.exp ((P + (q + 2 : ℕ) + A) ^ A))
    let reconstructionLip := ∑ j : Fin m, (Fintype.card (BoundedBooleanJet (Fin q) (j.val + 1)) : ℝ≥0)
    let Row := fun j : Fin m => {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (j.val + 1)}
    let Tuple := PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U b S)
    ∃ g : Tuple → EuclideanJetLayers U Row → ℝ,
      (∀ y, Continuous (g y)) ∧
      (∀ y z, g y z ∈ Set.Icc (0 : ℝ) cap) ∧
      (∀ y, Integrable (g y) ξ) ∧
      (∀ y, (∫ z, g y z ∂ξ) = 1) ∧
      (∀ y, (realDensityMeasure μ (fun z => density (cover z))).map
        (euclideanCoefficientJetMap U (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y)
          (fun j => (Subtype.val : Row j → Finset (Fin q)))) = realDensityMeasure ξ (g y)) ∧
      (∀ y, physicalDensityProjection.{_, _, uX, 0} U (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U b S x y) d density
        (fun z => g y ((physicalRowsStandardEquiv U).symm z))) ∧
      (∀ y, ∃ F : (JetAmbientIndex Row J → UnitAddCircle) → ℂ,
        LipschitzWith (densityLip * sectionLip * reconstructionLip) F ∧
        (∀ z, ‖F z‖ ≤ cap) ∧
        ∀ z, (g y z : ℂ) = F (coveredJetAmbientTorus U 1 z)) ∧
      (∀ law : FiniteProbabilityWeights Tuple,
        ∃ F : (JetAmbientIndex Row J → UnitAddCircle) → ℂ,
          LipschitzWith (densityLip * sectionLip * reconstructionLip) F ∧
          (∀ z, ‖F z‖ ≤ cap) ∧
          ∀ z, law.complexMean (fun y => (g y z : ℂ)) = F (coveredJetAmbientTorus U 1 z)) ∧
      AllocatedSlicedSourceProjection.{uX} B U b S x hb o hR hσ C V d g Asample P := by
  obtain ⟨A, Asample, hA, hAsample, hconstruct⟩ := exists_allocated_sliced_constructed_projection.{uX} m q
  refine ⟨A, Asample, hA, hAsample, ?_⟩
  intro G _ _ I _ n B _ J _ U b R σ S x P hP hG hL M selection hx Pk hMk hPk period
  exact hconstruct B U b S x hP hG hL hx.2 period (kernelPeriodCandidate_pos _ _)
    ((kernelPeriodCandidate_le_exp hMk _ _).trans (Real.exp_le_exp.mpr hPk))

end Erdos3.VectorPolynomial

end

end OAI
