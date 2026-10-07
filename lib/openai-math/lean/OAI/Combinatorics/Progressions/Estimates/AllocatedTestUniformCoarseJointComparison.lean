import OAI.Combinatorics.Progressions.Dynamics.AllocatedTestUniformBudgetedComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory Polynomial
open scoped BigOperators Classical NNReal

universe uX

def allocatedTestUniformJointStatement (m dim : ℕ) : Prop :=
    ∃ A a : ℕ, 2 ≤ A ∧ 2 ≤ a ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ v, Fintype (B v)] [∀ v, DecidableEq (B v)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    {p Etarget T : ℝ} (_hp : 0 ≤ p) (_hE : 0 ≤ Etarget) (_hT : 0 ≤ T)
    (_hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (_hn : ∀ j, (n j : ℝ) ≤ p)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (_hRup : ∀ j, R j ≤ Real.exp p) (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp p)
    (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp p) (_hmsp : ((m + 2 : ℕ) : ℝ) ≤ p),
    let P := allocatedChosenScaleBudget m p (Etarget + 1) T
    let Pc := allocatedComparisonDimension m p
    let L₀ := allocatedNormalizedInitialScale m p Pc (Etarget + 1) T
    ∃ S : LayerSamplerScale (G := G) B U b R σ,
      S = allocatedPrimitiveNormalizedScale B U b hR hσ p (Etarget + 1) T ∧
      (S.value : ℝ) ≤ Real.exp ((p + Etarget + T + a) ^ a) ∧
    ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
      {M : ℕ} (hM : 0 < M) (_hMp : (M : ℝ) ≤ Real.exp p)
      (selection : Fin dim ↪ G) (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
      (_hdim : dim ≤ m + 1),
    ∃ (d : ℕ) (hd : 0 < d), let : NeZero d := ⟨hd.ne'⟩
    (d : ℝ) ≤ Real.exp ((p + Etarget + T + a) ^ a) ∧
    ∀ [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin dim)) U)] [BorelSpace (SiteTorus (Finset (Fin dim)) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv 1 j)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)],
    let O := fun j : Fin m => BoundedBooleanJet (Fin dim) (j.val + 1)
    let rows := fun j => (Subtype.val : O j → Finset (Fin dim))
    let density := allocatedCoefficientDensity B U b hb o hR hσ S
    let cap := (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let cover := quotientIntegerCover (coefficientIntegerLattice U) d
    let ξ := Measure.pi (fun j => Measure.pi (fun _ : BoundedBooleanJet (Fin dim) (j.val + 1) => ν j))
    ∃ g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S) →
        EuclideanJetLayers U (fun j => BoundedBooleanJet (Fin dim) (j.val + 1)) → ℝ,
      (∀ y, Continuous (g y)) ∧ (∀ y z, g y z ∈ Set.Icc (0 : ℝ) cap) ∧
      (∀ y, Integrable (g y) ξ) ∧ (∀ y, (∫ z, g y z ∂ξ) = 1) ∧
      (∀ y, (realDensityMeasure μ (fun z => density (cover z))).map
        (euclideanCoefficientJetMap U (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y)
          (fun j => (Subtype.val : BoundedBooleanJet (Fin dim) (j.val + 1) → Finset (Fin dim)))) =
            realDensityMeasure ξ (g y)) ∧
        ((∀ y, physicalDensityProjection.{_, _, uX, 0} U
          (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y) d density (g y)) ∧
          allocatedProjectedFourierData B U b S C V d g A P) ∧
      ∀ (_hCp : ∀ j, (C j : ℝ) ≤ Real.exp p) (_hVp : ∀ j, (V j : ℝ) ≤ Real.exp p)
        {X : Type uX} [Fintype X] [DecidableEq X] (_hXp : (Fintype.card X : ℝ) ≤ p),
        let ξ₀ := normalizedTupleNarrowWidth X (PrincipalTupleIndex B (layerSamplerDegree I n))
          selection M p (Etarget + 1)
        let hξ := normalizedTupleNarrowWidth_pos X (PrincipalTupleIndex B (layerSamplerDegree I n))
          selection M p (Etarget + 1)
        let W : ℝ := Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ)
        let hW : 0 ≤ W := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        let Pmass := allocatedUnifiedSamplingBudget m dim A P p (Etarget + 1)
        ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
        (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
        (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
        (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
        (c : ∀ j, U j)
        (_hc : coefficientConstantCenter U center =
          -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
            (constantCoefficientArray U (fun s => c s.1))))
        (N stride : X → ℕ) (_hs : ∀ t, 0 < stride t)
        {Rrank τ : ℝ} (hτ : 0 < τ),
        let δ := normalizedTupleRadius X selection M p (Etarget + 1) W
        let mesh := δ / 4
        ∀ (_hτp : 1 / τ ≤ Real.exp p) (_hstrideT : ∀ t, (stride t : ℝ) ≤ Real.exp T)
        (_hsize : ∀ t, Real.exp ((p + Etarget + T + a) ^ a) ≤ (N t : ℝ))
        (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) Rrank (U j) (poly j))
        (_hRank : Real.exp ((p + Etarget + T + a) ^ a) ≤ Rrank)
        (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
        (_hcells : cells.Nonempty) (bases : Finset (X → ℤ)) (_hbases : bases.Nonempty)
        {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
        (bW : ∀ j, Basis (Kcov j) ℤ
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))),
        let centeredPoly := fun j => subtractConstant (c j).val (poly j)
        let centeredMem := fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j)
        let widths := narrowTrimmedSpatialWidths (G := G)
          (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ₀ N
        let baseDensity := jointSelectedPhysicalDensity B U b hb o R σ hR hσ L₀ poly hmem center
        let Z := selectedJointDensityMass bases stride cells widths baseDensity
        ∃ (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z)
          (hN : ∀ t, 0 < N t) (hZ : 0 < Z),
        let hwidths := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
        let whole := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
          (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
        let law := whole.prod (selectedJointFiniteLaw bases _hbases stride cells widths hwidths
          hmass baseDensity (jointSelectedPhysicalDensity_nonneg B U b hb o R σ hR hσ L₀ poly hmem center) hZ)
        (|Z - 1| ≤ Real.exp (-Pmass) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ Z⁻¹ ≤ 2) ∧
        ∃ reference : (X → ℤ) → ((X → (Unit ⊕ Fin dim) → ℤ) → ℂ) → ℂ,
        (∀ base, allocatedRefinedReferenceFunctional (τ := τ) (ξ := ξ₀) B U b hR hσ S x rows X
          hM selection hx stride hb o bW d N hW mesh base cells
          (physicalCubeEuclideanSample U d centeredPoly centeredMem) Z Pc T (reference base)) ∧
        ∀ (test : Finset (Fin dim) → (X → ℝ) → ℂ) (_htest : ∀ s v, ‖test s v‖ ≤ 1),
        (∀ base, ‖allocatedOriginalTupleSource B U b hR hσ S x X stride hb o N hN hW hτ hξ
          base cells hmass (physicalCubeSiteTest test) Z centeredPoly centeredMem -
            reference base (physicalCubeSiteTest test)‖ ≤ Real.exp (-Etarget)) ∧
        ‖law.complexMean (fun z => physicalCubeSiteTest test (physicalCubeRootDifferences
          (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x z.1)
          (allocatedPhysicalCubeDirections B U b S x z.1) z.2.1.val z.2.2.val)) -
            (𝔼 base ∈ bases, reference base (physicalCubeSiteTest test))‖ ≤ Real.exp (-Etarget)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem allocatedTestUniformChosenScaleTupleComparison (m dim : ℕ) :
    allocatedTestUniformChosenScaleTupleStatement m dim true := by
  obtain ⟨A, Amass, hA, hAmass, hactual⟩ := allocatedTestUniformBudgetedTupleComparison m dim
  obtain ⟨a, ha, hcut⟩ := exists_allocatedChosenThreshold_bound m A Amass
  unfold allocatedTestUniformChosenScaleTupleStatement
  refine ⟨A, a, hA, ha, ?_⟩
  intro G _ _ I _ _ n B _ _ J _ U b R σ hR hσ p Etarget T hp hE hT
    hvars hI hn hJ hRup hRi hσi hmsp P Pc
  let S := allocatedPrimitiveNormalizedScale (G := G) B U b hR hσ p Etarget T
  obtain ⟨hP, hpP, _, hTP, hPcP, hLogP⟩ := allocatedChosenScaleBudget_bounds m hp hE hT
  have hL : (S.value : ℝ) ≤ Real.exp P :=
    (allocatedPrimitiveNormalizedScale_upper B U b hR hσ hp hE hT hvars hn hRi hσi).trans
      (Real.exp_le_exp.mpr hLogP)
  obtain ⟨hPS, hDS, hNS⟩ := hcut hp hE hT
  refine ⟨S, rfl, hL.trans (Real.exp_le_exp.mpr hPS), ?_⟩
  intro x M hM hMp selection hx hdim
  have hGP : (Fintype.card G : ℝ) ≤ P :=
    (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans (hvars.trans hpP)
  obtain ⟨d, hd, hdb, hconstruct⟩ := hactual B U b S x hP hGP hL hM selection hx hdim
  let : NeZero d := ⟨hd.ne'⟩
  refine ⟨d, hd, hdb.trans (Real.exp_le_exp.mpr hDS), ?_⟩
  intro _ _ _ _ _ hb o C V hC hV hσ1 Cinv hCinv hchart hsmall μ _ _ ν _ _
    O rows density cap cover ξ
  obtain ⟨g, hgc, hgb, hgi, hgm, hglaw, hprojection, hdata⟩ :=
    hconstruct hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ ν
  refine ⟨g, hgc, hgb, hgi, hgm, hglaw, hprojection, ?_⟩
  intro hCp hVp X _ _ hXp ξ₀ hξ W hW Pmass poly hpoly hmem N stride hs Rrank τ hτ
    δ mesh hτp hstrideT hsize hrank hRank base cells hcells bases hbases Kcov _ bW
    widths baseDensity Z
  obtain ⟨hPc, hpPc, hcountc⟩ := allocatedNormalizedCoefficientInput B hp hvars
  obtain ⟨_, _, _, _, hcountDim, _, _, _, hprofile⟩ := allocatedComparisonDimension_bounds m hp
  have hcount (j : Fin m) :
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P :=
    (boundedCoefficientExponent_card_le_geometricSiteBudget m 0
      (Nat.succ_le_of_lt j.isLt) hp hvars).trans (hcountDim.trans hPcP)
  have hmP : (m : ℝ) ≤ P := by
    have hmp : (m : ℝ) ≤ p := by push_cast at hmsp; linarith
    exact hmp.trans hpP
  have hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P :=
    (probabilityProfileLipschitz_le_comparisonProfileBound.trans (hprofile.trans hPcP)).trans
      (by linarith [Real.add_one_le_exp P])
  obtain ⟨_, hPerr, _, _, _, _, hPplus, hpMass, _, _⟩ :=
    allocatedUnifiedSamplingBudget_bounds m dim A hP hp hE
  have hPMass : P ≤ Pmass := by linarith
  have hDMass : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp p :=
    hvars.trans (by linarith [Real.add_one_le_exp p])
  have hWScale : W ≤ (Fintype.card (LayerSamplerVariables G I n B) : ℝ) * S.value := le_rfl
  have hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W := by
    dsimp only [W, allocatedPhysicalRootBudget]
    simp
  have hlarge : Real.exp (allocatedRefinedJointLengthLog (G := G) B (Fin dim) O Pc
      (allocatedCoefficientAccuracyLog m p (Etarget + 3))
      ((m + 1 : ℕ) * Pc + Fintype.card X * T)) ≤ S.value :=
    allocatedPrimitiveNormalizedScale_ready B U b hR hσ rows
      (by simpa only [Fintype.card_fin] using hdim) (fun _ => Subtype.val_injective) X
      hp hE hT hvars hI hn hXp
  exact hdata hmP (hvars.trans hpP)
    (fun j => (hRi j).trans (Real.exp_le_exp.mpr hpP))
    (fun j => (hσi j).trans (Real.exp_le_exp.mpr hpP)) hcount
    (fun j => (hI j).trans hpP) (fun j => (hn j).trans hpP) (fun j => (hJ j).trans hpP)
    hAP (fun j => (hCp j).trans (Real.exp_le_exp.mpr hpP))
    (fun j => (hVp j).trans (Real.exp_le_exp.mpr hpP)) hp hE hvars hI hn hJ hXp hCp hMp hmsp
    hDMass poly hpoly hmem N stride hs hW hτ hWScale
    (hτp.trans (Real.exp_le_exp.mpr hpMass))
    (fun t => (hstrideT t).trans (Real.exp_le_exp.mpr (hTP.trans hPMass)))
    (fun t => (Real.exp_le_exp.mpr hNS).trans (hsize t)) hrank
    ((Real.exp_le_exp.mpr hNS).trans hRank) hbudget base cells hcells bases hbases bW
    hPc (hPcP.trans hPerr) hT (hMp.trans (Real.exp_le_exp.mpr hpPc))
    (fun j => (hRup j).trans (Real.exp_le_exp.mpr hpPc))
    (fun j => (hRi j).trans (Real.exp_le_exp.mpr hpPc))
    (fun j => (hσi j).trans (Real.exp_le_exp.mpr hpPc)) hcountc hstrideT hlarge

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem allocatedTestUniformOriginalChosenTupleComparison (m dim : ℕ) :
    allocatedTestUniformOriginalChosenTupleStatement m dim := by
  obtain ⟨A, Atuple, hA, hAtuple, hcomparison⟩ := allocatedTestUniformChosenScaleTupleComparison m dim
  obtain ⟨Aproj, _, hprojection⟩ := exists_allocated_uniform_mixture_projection m dim
  obtain ⟨a₀, ha₀, hcut⟩ := exists_allocatedOriginalThreshold_bound m dim A Aproj Atuple (by omega)
  let a := a₀ + 2
  unfold allocatedTestUniformOriginalChosenTupleStatement
  refine ⟨A, a, hA, by dsimp [a]; omega, ?_⟩
  intro G _ _ I _ _ n B _ _ J _ U b R σ hR hσ p Etarget T hp hE hT
    hvars hI hn hJ hRup hRi hσi hmsp P Pc
  let Ew := Etarget + 1
  have hEw : 0 ≤ Ew := by dsimp [Ew]; linarith
  have hworkBound : (p + Ew + T + a₀) ^ a₀ ≤ (p + Etarget + T + a) ^ a := by
    have hbase : p + Ew + T + a₀ ≤ p + Etarget + T + a := by
      dsimp [Ew, a]
      push_cast
      linarith
    have hone : 1 ≤ p + Etarget + T + a := by
      dsimp [a]
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) a₀]
    exact (pow_le_pow_left₀ (by positivity) hbase a₀).trans
      (pow_le_pow_right₀ hone (by dsimp [a]; omega))
  obtain ⟨hprojCut, htupleCut⟩ := hcut hp hEw hT
  have hprojFinal := hprojCut.trans hworkBound
  have htupleFinal := htupleCut.trans hworkBound
  obtain ⟨hP, hpP, _, hTP, hPcP, hLogP⟩ := allocatedChosenScaleBudget_bounds m hp hEw hT
  obtain ⟨S, hS, hSbound, hkernel⟩ := hcomparison B U b hR hσ hp hEw hT
    hvars hI hn hJ hRup hRi hσi hmsp
  have hL : (S.value : ℝ) ≤ Real.exp P := by
    rw [hS]
    exact (allocatedPrimitiveNormalizedScale_upper B U b hR hσ hp hEw hT hvars hn hRi hσi).trans
      (Real.exp_le_exp.mpr hLogP)
  refine ⟨S, hS, hSbound.trans (Real.exp_le_exp.mpr htupleFinal), ?_⟩
  intro x M hM hMp selection hx hdim
  obtain ⟨d, hd, hdb, hconstruct⟩ := hkernel x hM hMp selection hx hdim
  let : NeZero d := ⟨hd.ne'⟩
  refine ⟨d, hd, hdb.trans (Real.exp_le_exp.mpr htupleFinal), ?_⟩
  intro _ _ _ _ _ hb o C Vcap hC hV hσ1 Cinv hCinv hchart hsmall μ _ _ ν _ _
    O rows density cap cover ξ
  obtain ⟨g, hgc, hgb, hgi, hgm, hglaw, hgproj, hdata⟩ :=
    hconstruct hb o C Vcap hC hV hσ1 Cinv hCinv hchart hsmall μ ν
  refine ⟨g, hgc, hgb, hgi, hgm, hglaw, hgproj, ?_⟩
  intro hCp hVp X _ _ hXp ξ₀ hξ W hW Pmass poly hpoly hmem N stride hs Rrank τ hτ
    δ mesh hτp hstrideT hsize hrank hRank base cells hcells bases hbases Kcov _ bW
    widths baseDensity Z
  obtain ⟨hmass, hnormal, hN, modulus, hmodulus, hmod, hspatialPeriod, hperiod,
    s, hsA, hi, hRefined, hdiv, hbound, hlengths, reference, residue, href, hr, hcompare⟩ :=
    hdata hCp hVp hXp poly hpoly hmem N stride hs hτ hτp hstrideT
      (fun t => (Real.exp_le_exp.mpr htupleFinal).trans (hsize t)) hrank
      ((Real.exp_le_exp.mpr htupleFinal).trans hRank) base cells hcells bases hbases
      bW
  let : NeZero modulus := ⟨hmodulus.ne'⟩
  let : NeZero (residueRefinedPeriod modulus stride) := ⟨hRefined.ne'⟩
  refine ⟨hmass, hnormal, hN, modulus, hmodulus, hmod, hspatialPeriod, hperiod,
    s, hsA, hi, hRefined, hdiv, hbound, hlengths, reference, residue, href, hr, ?_⟩
  intro test htest
  have hcompare := hcompare (physicalCubeSiteTest test)
    (fun v => physicalCubeSiteTest_norm_le test htest v)
  let Pmix := allocatedOriginalProjectionBudget m dim A p Ew T
  obtain ⟨hPmix, hQmix, hPmixP, hEmix⟩ := allocatedOriginalProjectionBudget_bounds m dim A hp hEw hT
  obtain ⟨_, _, _, hQ, _, hwidth, hPplus, hpQ, _, hnorm⟩ :=
    allocatedUnifiedSamplingBudget_bounds m dim A hP hp hEw
  have hpMix : p ≤ Pmix := hpP.trans hPmixP
  have hTMix : T ≤ Pmix := hTP.trans hPmixP
  have hexp := Real.exp_le_exp.mpr hpMix
  have hmMix : (m : ℝ) ≤ Pmix := by
    have hmp : (m : ℝ) ≤ p := by push_cast at hmsp; linarith
    exact hmp.trans hpMix
  obtain ⟨_, _, _, _, hcountDim, _, _, _, hprofile⟩ := allocatedComparisonDimension_bounds m hp
  have hcount (j : Fin m) :
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pmix :=
    (boundedCoefficientExponent_card_le_geometricSiteBudget m 0
      (Nat.succ_le_of_lt j.isLt) hp hvars).trans (hcountDim.trans (hPcP.trans hPmixP))
  have hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pmix :=
    (probabilityProfileLipschitz_le_comparisonProfileBound.trans
      (hprofile.trans (hPcP.trans hPmixP))).trans (by linarith [Real.add_one_le_exp Pmix])
  have hnormdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ Pmix := by
    calc
      _ = ((Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 1) * Fintype.card X := by
        simp only [Fintype.card_prod, Fintype.card_option, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      _ ≤ (p + 1) * p := mul_le_mul (add_le_add hvars le_rfl) hXp (Nat.cast_nonneg _) (by positivity)
      _ = p * (p + 1) := mul_comm _ _
      _ ≤ Pmix := hnorm.trans hQmix
  have hD : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp p :=
    hvars.trans (by linarith [Real.add_one_le_exp p])
  have hWP : W ≤ Real.exp Pmix := by
    calc
      _ ≤ Real.exp p * Real.exp P := mul_le_mul hD hL (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (P + p) := by rw [← Real.exp_add, add_comm]
      _ ≤ _ := Real.exp_le_exp.mpr (hPplus.trans hQmix)
  have hroot : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W := by
    dsimp only [W, allocatedPhysicalRootBudget]
    simp
  have hGp : (Fintype.card G : ℝ) ≤ p :=
    (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans hvars
  have hNp : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (allocatedPrincipalIndex_card_le_variables (G := G) B)).trans hvars
  have hmsp' : ((m + 1 : ℕ) : ℝ) ≤ p := by push_cast at hmsp ⊢; linarith
  have hdimsp : ((dim + 1 : ℕ) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (by omega : dim + 1 ≤ m + 2)).trans hmsp
  have hqcard : (Fintype.card (Unit ⊕ Fin dim) : ℝ) ≤ p := by
    simpa only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Nat.add_comm 1] using hdimsp
  have hchoice := normalizedTupleSpatialChoices (N := PrincipalTupleIndex B (layerSamplerDegree I n))
    (X := X) (m := m) selection hM hp hEw hmsp' hdimsp hGp hXp hMp
  have hlog := (normalizedTuple_log_envelopes X (PrincipalTupleIndex B (layerSamplerDegree I n))
    selection hp hEw (le_refl (0 : ℝ)) hqcard hGp hNp hXp).1
  have hξP : ξ₀⁻¹ ≤ Real.exp Pmix :=
    hchoice.2.2.1.trans (Real.exp_le_exp.mpr (hlog.trans (hwidth.trans hQmix)))
  have hsmall₀ := allocatedPhysicalChartRadius_density_small (G := G) B (Fin dim) Cinv R
    hCinv (fun j => (hR j).le) hsmall
  let η := Real.exp (-(Etarget + 4))
  have hη : 0 < η := Real.exp_pos _
  have hηP : η⁻¹ ≤ Real.exp Pmix := by
    dsimp only [η]
    rw [Real.exp_neg, inv_inv]
    apply Real.exp_le_exp.mpr
    dsimp only [Ew] at hEmix
    linarith
  have hfirst := hprojection B U b S (fun _ => 0) x hb o hR hσ C Vcap hC hV hσ1
    Cinv hCinv hchart hsmall₀ hPmix (hvars.trans hpMix) hW hroot hWP
    (hL.trans (Real.exp_le_exp.mpr hPmixP)) hmMix
    (fun j => (hRi j).trans hexp) (fun j => (hσi j).trans hexp) hcount
    (fun j => (hI j).trans hpMix) (fun j => (hn j).trans hpMix) (fun j => (hJ j).trans hpMix)
    hAP (fun j => (hCp j).trans hexp) (fun j => (hVp j).trans hexp) hx.2 (hXp.trans hpMix) hnormdim
    poly hpoly hmem base stride hs (fun t => (hstrideT t).trans (Real.exp_le_exp.mpr hTMix))
    hτ (by simpa only [one_div] using hτp.trans hexp) hξ hchoice.2.1 hξP hη hηP
    N (fun t => (Real.exp_le_exp.mpr hprojFinal).trans (hsize t)) hrank
    ((Real.exp_le_exp.mpr hprojFinal).trans hRank) test htest cells hcells d g hgproj.1 hη hηP
    hnormal.2.2.1 (narrowTrimmedSpatialWidths_pos hW hτ hξ N hN) hmass
  have hsource :
      ‖allocatedOriginalTupleSource B U b hR hσ S x X stride hb o N hN hW hτ hξ base cells hmass
          (physicalCubeSiteTest test) Z poly hmem -
        allocatedProjectedTupleSource B U b S x X stride g N hN hW hτ hξ base cells hmass
          (physicalCubeEuclideanSample U d poly hmem) (physicalCubeSiteTest test) Z‖ ≤
        (2 * Real.exp (-(Etarget + 4)) + Real.exp (-(Etarget + 4))) / Z := by
    simpa only [allocatedOriginalTupleSource, allocatedProjectedTupleSource, physicalCubePositiveTest] using hfirst
  exact allocatedOriginalTupleDifference_exp_bound B U b hR hσ S x rows X hM selection hx modulus s hsA
    stride reference residue hb o bW d g N hN hW hτ hξ mesh base cells hmass
    (physicalCubeEuclideanSample U d poly hmem) (physicalCubeSiteTest test) Z poly hmem
    hnormal.2.1.1 hsource hcompare

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem allocatedTestUniformCenteredChosenTupleComparison (m dim : ℕ) :
    allocatedTestUniformCenteredChosenTupleStatement m dim := by
  obtain ⟨A, a, hA, ha, hcomparison⟩ := allocatedTestUniformOriginalChosenTupleComparison m dim
  unfold allocatedTestUniformCenteredChosenTupleStatement
  refine ⟨A, a, hA, ha, ?_⟩
  intro G _ _ I _ _ n B _ _ J _ U b R σ hR hσ p Etarget T hp hE hT
    hvars hI hn hJ hRup hRi hσi hmsp P Pc L₀
  obtain ⟨S, hS, hSbound, hkernel⟩ := hcomparison B U b hR hσ hp hE hT
    hvars hI hn hJ hRup hRi hσi hmsp
  have hselected : S = selectedLayerSamplerScale B U b R σ hR hσ L₀ := hS
  refine ⟨S, hS, hSbound, ?_⟩
  intro x M hM hMp selection hx hdim
  obtain ⟨d, hd, hdb, hconstruct⟩ := hkernel x hM hMp selection hx hdim
  let : NeZero d := ⟨hd.ne'⟩
  refine ⟨d, hd, hdb, ?_⟩
  intro _ _ _ _ _ hb o C Vcap hC hV hσ1 Cinv hCinv hchart hsmall μ _ _ ν _ _
    O rows density cap cover ξ
  obtain ⟨g, hgc, hgb, hgi, hgm, hglaw, hgproj, hdata⟩ :=
    hconstruct hb o C Vcap hC hV hσ1 Cinv hCinv hchart hsmall μ ν
  refine ⟨g, hgc, hgb, hgi, hgm, hglaw, hgproj, ?_⟩
  intro hCp hVp X _ _ hXp ξ₀ hξ W hW Pmass poly hpoly hmem center c hc N stride hs Rrank τ hτ
    δ mesh hτp hstrideT hsize hrank hRank base cells hcells bases hbases Kcov _ bW
    centeredPoly centeredMem widths baseDensity Z
  have hpoly' (j : Fin m) : DegreeLE (1 : X → ℕ) (j.val + 1) (centeredPoly j) :=
    (hpoly j).subtractConstant (c j).val
  have hrank' (j : Fin m) :
      HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) Rrank (U j) (centeredPoly j) :=
    (hasLayerSamplingRank_subtractConstant_iff (Nat.zero_lt_succ _) _ _ (U j)
      (c j).val (poly j)).mpr (hrank j)
  have hdensity : (fun (a : X → ℤ) z => density (affineSampleCoefficientTorus U
      (fun j => translate (fun t => (a t : ℝ)) (centeredPoly j))
      (fun j => coefficients_translate_mem (U j) (fun t => (a t : ℝ))
        (centeredPoly j) (centeredMem j)) (fun k t => (z (k, t) : ℝ)))) = baseDensity := by
    funext a z
    exact allocatedJointDensity_subtractConstant B U b hb o R σ hR hσ L₀ S hselected
      poly hmem center c hc a z
  have hnormalizer := congrArg (selectedJointDensityMass bases stride cells widths) hdensity
  obtain ⟨hmass, hnormal, hN, modulus, hmodulus, hmod, hspatialPeriod, hperiod,
    s, hsA, hi, hRefined, hdiv, hbound, hlengths, reference, residue, href, hr, hcompare⟩ :=
    hdata hCp hVp hXp centeredPoly hpoly' centeredMem N stride hs hτ hτp hstrideT
      hsize hrank' hRank base cells hcells bases hbases bW
  let : NeZero modulus := ⟨hmodulus.ne'⟩
  let : NeZero (residueRefinedPeriod modulus stride) := ⟨hRefined.ne'⟩
  rw [hnormalizer] at hnormal hcompare
  exact ⟨hmass, hnormal, hN, modulus, hmodulus, hmod, hspatialPeriod, hperiod,
    s, hsA, hi, hRefined, hdiv, hbound, hlengths, reference, residue, href, hr, hcompare⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem allocatedTestUniformJointComparison (m dim : ℕ) :
    allocatedTestUniformJointStatement m dim := by
  obtain ⟨A, a, hA, ha, hcomparison⟩ := allocatedTestUniformCenteredChosenTupleComparison m dim
  unfold allocatedTestUniformJointStatement
  refine ⟨A, a, hA, ha, ?_⟩
  intro G _ _ I _ _ n B _ _ J _ U b R σ hR hσ p Etarget T hp hE hT
    hvars hI hn hJ hRup hRi hσi hmsp P Pc L₀
  obtain ⟨S, hS, hSbound, hkernel⟩ := hcomparison B U b hR hσ hp hE hT
    hvars hI hn hJ hRup hRi hσi hmsp
  have hselected : S = selectedLayerSamplerScale B U b R σ hR hσ L₀ := hS
  refine ⟨S, hS, hSbound, ?_⟩
  intro x M hM hMp selection hx hdim
  obtain ⟨d, hd, hdb, hconstruct⟩ := hkernel x hM hMp selection hx hdim
  let : NeZero d := ⟨hd.ne'⟩
  refine ⟨d, hd, hdb, ?_⟩
  intro _ _ _ _ _ hb o C Vcap hC hV hσ1 Cinv hCinv hchart hsmall μ _ _ ν _ _
    O rows density cap cover ξ
  obtain ⟨g, hgc, hgb, hgi, hgm, hglaw, hgproj, hdata⟩ :=
    hconstruct hb o C Vcap hC hV hσ1 Cinv hCinv hchart hsmall μ ν
  refine ⟨g, hgc, hgb, hgi, hgm, hglaw, hgproj, ?_⟩
  intro hCp hVp X _ _ hXp ξ₀ hξ W hW Pmass poly hpoly hmem center c hc N stride hs Rrank τ hτ
    δ mesh hτp hstrideT hsize hrank hRank cells hcells bases hbases Kcov _ bW
    centeredPoly centeredMem widths baseDensity Z
  have hbase (base : X → ℤ) := hdata hCp hVp hXp poly hpoly hmem center c hc N stride hs hτ
    hτp hstrideT hsize hrank hRank base cells hcells bases hbases bW
  obtain ⟨hmass, hnormal, hN, hrest⟩ := hbase (fun _ => 0)
  have hZ : 0 < Z := hnormal.2.2.1
  let source := fun base test => allocatedOriginalTupleSource B U b hR hσ S x X stride hb o
    N hN hW hτ hξ base cells hmass test Z centeredPoly centeredMem
  let represents := fun base functional => allocatedRefinedReferenceFunctional (τ := τ) (ξ := ξ₀)
    B U b hR hσ S x rows X hM selection hx stride hb o bW d N hW mesh base cells
    (physicalCubeEuclideanSample U d centeredPoly centeredMem) Z Pc T functional
  have hperBase (base : X → ℤ) :
      ∃ functional : ((X → (Unit ⊕ Fin dim) → ℤ) → ℂ) → ℂ,
        represents base functional ∧
        ∀ (test : Finset (Fin dim) → (X → ℝ) → ℂ), (∀ s v, ‖test s v‖ ≤ 1) →
          ‖source base (physicalCubeSiteTest test) - functional (physicalCubeSiteTest test)‖ ≤
            Real.exp (-Etarget) := by
    obtain ⟨hmass', _, hN', modulus, hmodulus, hmod, hspatialPeriod, hperiod,
      s, hsA, hi, hRefined, hdiv, hbound, hlengths, tupleRef, residue, href, hr, hcompare⟩ := hbase base
    let : NeZero modulus := ⟨hmodulus.ne'⟩
    let : NeZero (residueRefinedPeriod modulus stride) := ⟨hRefined.ne'⟩
    let functional := fun test => allocatedRefinedTupleReference (τ := τ) (ξ := ξ₀)
      B U b hR hσ S x rows X hM selection hx modulus s hsA stride tupleRef residue hb o bW d N hW
      mesh base cells (physicalCubeEuclideanSample U d centeredPoly centeredMem) test Z
    refine ⟨functional, ?_, ?_⟩
    · exact ⟨modulus, hmodulus, hmod, hspatialPeriod, hperiod, s, hsA, hi,
        hRefined, hdiv, hbound, hlengths, tupleRef, residue, href, hr, fun _ => rfl⟩
    · intro test htest
      exact hcompare test htest
  choose reference hrep herror using hperBase
  refine ⟨hmass, hN, hZ, ⟨hnormal.1, hnormal.2.1, hnormal.2.2.2⟩, reference, hrep, ?_⟩
  intro test htest
  refine ⟨fun base => herror base test htest, ?_⟩
  exact allocatedCenteredJointSource_comparison B U b hR hσ S L₀ hselected x X hb o
    poly hmem center c hc N hN hW hτ hξ stride cells bases hbases hmass hZ
    (physicalCubeSiteTest test) (fun base => reference base (physicalCubeSiteTest test))
    (fun base _ => herror base test htest)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem allocatedTestUniformCoarseJointComparison (m dim : ℕ) :
    allocatedTestUniformCoarseJointStatement m dim := by
  obtain ⟨A, afine, hA, hafine, hcomparison⟩ := allocatedTestUniformJointComparison m dim
  obtain ⟨acoarse, hacoarse, hcoarsen⟩ := exists_allocated_chosen_functional_coarsening m dim A
  let afinal := max (afine+1) (acoarse+2)
  have hafinal : 2 ≤ afinal := by dsimp [afinal]; omega
  unfold allocatedTestUniformCoarseJointStatement
  refine ⟨A, afinal, hA, hafinal, ?_⟩
  intro G _ _ I _ _ n B _ _ J _ U b R σ hR hσ p Etarget T hp hE hT
    hvars hI hn hJ hRup hRi hσi hmsp P Pc L₀
  have hE1 : 0 ≤ Etarget+1 := by linarith
  have hE2 : 0 ≤ Etarget+2 := by linarith
  have hshift1 : afine+1 ≤ afinal := le_max_left _ _
  have hshift2 : acoarse+2 ≤ afinal := le_max_right _ _
  have hshift1R : (afine : ℝ)+1 ≤ afinal := by exact_mod_cast hshift1
  have hshift2R : (acoarse : ℝ)+2 ≤ afinal := by exact_mod_cast hshift2
  have hbase1 : (1 : ℝ) ≤ p+Etarget+T+afinal := by
    have h : (2 : ℝ) ≤ afinal := by exact_mod_cast hafinal
    linarith
  have hcutFine : (p+(Etarget+1)+T+afine)^afine ≤ (p+Etarget+T+afinal)^afinal := by
    calc
      _ ≤ (p+Etarget+T+afinal)^afine := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ ≤ _ := pow_le_pow_right₀ hbase1 (by omega)
  have hcutCoarse : (p+(Etarget+2)+T+acoarse)^acoarse ≤ (p+Etarget+T+afinal)^afinal := by
    calc
      _ ≤ (p+Etarget+T+afinal)^acoarse := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ ≤ _ := pow_le_pow_right₀ hbase1 (by omega)
  have hraw := hcomparison B U b hR hσ hp hE1 hT hvars hI hn hJ hRup hRi hσi hmsp
  have heq : Etarget+1+1 = Etarget+2 := by ring
  simp only [heq] at hraw
  obtain ⟨S, hS, hSbound, hkernel⟩ := hraw
  have hselected : S = selectedLayerSamplerScale B U b R σ hR hσ L₀ := hS
  refine ⟨S, hS, hSbound.trans (Real.exp_le_exp.mpr hcutFine), ?_⟩
  intro x M hM hMp selection hx hdim
  obtain ⟨d, hd, hdb, hconstruct⟩ := hkernel x hM hMp selection hx hdim
  let : NeZero d := ⟨hd.ne'⟩
  refine ⟨d, hd, hdb.trans (Real.exp_le_exp.mpr hcutFine), ?_⟩
  intro _ _ _ _ _ hb o C Vcap hC hV hσ1 Cinv hCinv hchart hsmall μ _ _ ν _ _
    O rows density cap cover ξ
  obtain ⟨g, hgc, hgb, hgi, hgm, hglaw, hgproj, hdata⟩ :=
    hconstruct hb o C Vcap hC hV hσ1 Cinv hCinv hchart hsmall μ ν
  refine ⟨g, hgc, hgb, hgi, hgm, hglaw, hgproj, ?_⟩
  intro hCp hVp X _ _ hXp ξ₀ hξ W hW Pmass poly hpoly hmem center c hc N stride hs Rrank τ hτ
    mesh hτp hstrideT hsize hrank hRank cells hcells bases hbases Kcov _ bW
    centeredPoly centeredMem widths baseDensity Z
  obtain ⟨hmass, hN, hZ, hnormal, reference, hrep, herror⟩ :=
    hdata hCp hVp hXp poly hpoly hmem center c hc N stride hs hτ hτp hstrideT
      (fun t => (Real.exp_le_exp.mpr hcutFine).trans (hsize t)) hrank
      ((Real.exp_le_exp.mpr hcutFine).trans hRank) cells hcells bases hbases bW
  have hpoly' (j : Fin m) : DegreeLE (1 : X → ℕ) (j.val+1) (centeredPoly j) :=
    (hpoly j).subtractConstant (c j).val
  have hrank' (j : Fin m) :
      HasLayerSamplingRank (j.val+1) (fun t => (N t : ℝ)) Rrank (U j) (centeredPoly j) :=
    (hasLayerSamplingRank_subtractConstant_iff (Nat.zero_lt_succ _) _ _ (U j)
      (c j).val (poly j)).mpr (hrank j)
  have hmB : ((m+1 : ℕ) : ℝ) ≤ p := by push_cast at hmsp ⊢; linarith
  have hdimB : ((dim+1 : ℕ) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (by omega : dim+1 ≤ m+2)).trans hmsp
  let _ : CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U) :=
    coefficientTorus_compact_of_lattice U
  have hcoarse (base : X → ℤ) := hcoarsen B U b hR hσ S x hb o bW d C Vcap hp hE2 hT hS
    hC hV ν stride hs hM selection hx (by simpa only [Fintype.card_fin] using hdim)
    hmB hdimB hvars hI hn hJ hXp hMp hCp hVp hRup hRi hσi N hN hW hτ base cells hmass
    centeredPoly hpoly' centeredMem hτp hstrideT
    (fun t => (Real.exp_le_exp.mpr hcutCoarse).trans (hsize t)) hrank'
    ((Real.exp_le_exp.mpr hcutCoarse).trans hRank) Cinv hCinv hchart hsmall μ g hgc
    (fun y z => (hgb y z).1) hglaw hgi hgm hgproj.2 hσ1 hZ hnormal.2.2 rfl (reference base) (hrep base)
  choose coarse hsite hclose using hcoarse
  have hsmallError : Real.exp (-(Etarget+1)) + normalizedSpatialShare (Etarget+2)/2 ≤
      Real.exp (-Etarget) := by
    have hs : normalizedSpatialShare (Etarget+2)/2 ≤ Real.exp (-(Etarget+1)) := by
      change Real.exp (-((Etarget+2)+2))/2 ≤ _
      exact (half_le_self (Real.exp_nonneg _)).trans (Real.exp_le_exp.mpr (by linarith))
    calc
      _ ≤ 2 * Real.exp (-(Etarget+1)) := by linarith
      _ ≤ Real.exp 1 * Real.exp (-(Etarget+1)) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  refine ⟨hmass, hN, hZ, hnormal, coarse, hsite, ?_⟩
  intro test htest
  have hbase (base : X → ℤ) :
      ‖allocatedOriginalTupleSource B U b hR hσ S x X stride hb o N hN hW hτ hξ
        base cells hmass (physicalCubeSiteTest test) Z centeredPoly centeredMem - coarse base test‖ ≤
        Real.exp (-Etarget) :=
    ((norm_sub_le_norm_sub_add_norm_sub _ (reference base (physicalCubeSiteTest test)) _).trans
      (add_le_add ((herror test htest).1 base) (hclose base test htest))).trans hsmallError
  refine ⟨hbase, ?_⟩
  exact allocatedCenteredJointSource_comparison B U b hR hσ S L₀ hselected x X hb o
    poly hmem center c hc N hN hW hτ hξ stride cells bases hbases hmass hZ
    (physicalCubeSiteTest test) (fun base => coarse base test) (fun base _ => hbase base)

end Erdos3.VectorPolynomial

end

end OAI
