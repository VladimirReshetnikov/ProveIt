import OAI.Combinatorics.Progressions.Dynamics.AllocatedChosenScaleBudget
import OAI.Combinatorics.Progressions.Dynamics.AllocatedProjectedBudgetedComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory Polynomial
open scoped BigOperators Classical NNReal

universe uX

def allocatedChosenScaleTupleStatement (m dim : ℕ) (keepProjection : Bool := false) : Prop :=
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
    let P := allocatedChosenScaleBudget m p Etarget T
    let Pc := allocatedComparisonDimension m p
    ∃ S : LayerSamplerScale (G := G) B U b R σ,
      S = allocatedPrimitiveNormalizedScale B U b hR hσ p Etarget T ∧
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
      ((if keepProjection then And
        (∀ y, physicalDensityProjection.{_, _, uX, 0} U
          (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y) d density (g y))
      else id) <|
      ∀ (_hCp : ∀ j, (C j : ℝ) ≤ Real.exp p) (_hVp : ∀ j, (V j : ℝ) ≤ Real.exp p)
        {X : Type uX} [Fintype X] [DecidableEq X] (_hXp : (Fintype.card X : ℝ) ≤ p),
        let ξ₀ := normalizedTupleNarrowWidth X (PrincipalTupleIndex B (layerSamplerDegree I n))
          selection M p Etarget
        let hξ := normalizedTupleNarrowWidth_pos X (PrincipalTupleIndex B (layerSamplerDegree I n))
          selection M p Etarget
        let W : ℝ := Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ)
        let hW : 0 ≤ W := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        let Pmass := allocatedUnifiedSamplingBudget m dim A P p Etarget
        ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
        (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
        (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
        (N stride : X → ℕ) (_hs : ∀ t, 0 < stride t)
        {Rrank τ : ℝ} (hτ : 0 < τ),
        let δ := normalizedTupleRadius X selection M p Etarget W
        let mesh := δ / 4
        ∀ (_hτp : 1 / τ ≤ Real.exp p) (_hstrideT : ∀ t, (stride t : ℝ) ≤ Real.exp T)
        (_hsize : ∀ t, Real.exp ((p + Etarget + T + a) ^ a) ≤ (N t : ℝ))
        (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) Rrank (U j) (poly j))
        (_hRank : Real.exp ((p + Etarget + T + a) ^ a) ≤ Rrank)
        (base : X → ℤ)
        (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
        (_hcells : cells.Nonempty) (bases : Finset (X → ℤ)) (_hbases : bases.Nonempty)
        (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (_htest : ∀ v, ‖test v‖ ≤ 1)
        {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
        (bW : ∀ j, Basis (Kcov j) ℤ
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))),
        let widths := narrowTrimmedSpatialWidths (G := G)
          (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ₀ N
        let baseDensity := fun (a : X → ℤ) z => density (affineSampleCoefficientTorus U
          (fun j => translate (fun t => (a t : ℝ)) (poly j))
          (fun j => coefficients_translate_mem (U j) (fun t => (a t : ℝ)) (poly j) (hmem j))
          (fun k t => (z (k, t) : ℝ)))
        let Z := selectedJointDensityMass bases stride cells widths baseDensity
        ∃ (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z),
        (|Z - 1| ≤ Real.exp (-Pmass) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧
          0 < Z ∧ Z⁻¹ ≤ 2) ∧
        ∃ (hN : ∀ t, 0 < N t) (modulus : ℕ) (hmodulus : 0 < modulus),
        let : NeZero modulus := ⟨hmodulus.ne'⟩
        modulus ≤ M^(m+1) ∧
        (∀ root : G → ℤ, integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
          pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
            (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
        (∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
          (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range) ∧
        ∃ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
          (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0),
        let refined := residueRefinedPeriod modulus stride
        (∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ))) ∧
        ∃ hRefined : 0 < refined,
        let : NeZero refined := ⟨hRefined.ne'⟩
        (∀ t, stride t * modulus ∣ refined) ∧
        (refined : ℝ) ≤ Real.exp ((m+1 : ℕ)*Pc + Fintype.card X*T) ∧
        ∃ hlengths : ∀ t, (Fintype.card (Fin dim)+1)*refined ≤
          principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S) t,
        ∃ (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
              (allocatedPrincipalSides B U b S) →
            (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
              (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod refined) →
            PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
              (allocatedPrincipalSides B U b S))
          (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
              (allocatedPrincipalSides B U b S) →
            (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
              (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod refined) →
            ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)),
        (∀ u r, principalResidueLabel refined (reference u r) = r) ∧
        (∀ u r v, (allocatedLongResidueWeights B U b S refined hRefined r hlengths).weight v ≠ 0 → ∀ j,
          integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) modulus = residue u r j) ∧
        ‖allocatedRefinedTupleDifference B U b hR hσ S x rows X hM selection hx modulus s hA
          stride reference residue hb o bW d g N hN hW hτ hξ mesh base cells hmass
          (physicalCubeEuclideanSample U d poly hmem) test Z‖ ≤ Real.exp (-Etarget)
      )

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem allocatedChosenScaleTupleComparison (m dim : ℕ) :
    allocatedChosenScaleTupleStatement m dim := by
  obtain ⟨A, Amass, hA, hAmass, hactual⟩ := allocatedBudgetedTupleComparison m dim
  obtain ⟨a, ha, hcut⟩ := exists_allocatedChosenThreshold_bound m A Amass
  unfold allocatedChosenScaleTupleStatement
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
  obtain ⟨g, hgc, hgb, hgi, hgm, hglaw, hdata⟩ :=
    hconstruct hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ ν
  refine ⟨g, hgc, hgb, hgi, hgm, hglaw, ?_⟩
  intro hCp hVp X _ _ hXp ξ₀ hξ W hW Pmass poly hpoly hmem N stride hs Rrank τ hτ
    δ mesh hτp hstrideT hsize hrank hRank base cells hcells bases hbases test htest Kcov _ bW
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
    ((Real.exp_le_exp.mpr hNS).trans hRank) hbudget base cells hcells bases hbases test htest bW
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

theorem allocatedChosenScaleTupleComparison_withProjection (m dim : ℕ) :
    allocatedChosenScaleTupleStatement m dim true := by
  obtain ⟨A, Amass, hA, hAmass, hactual⟩ := allocatedBudgetedTupleComparison_withProjection m dim
  obtain ⟨a, ha, hcut⟩ := exists_allocatedChosenThreshold_bound m A Amass
  unfold allocatedChosenScaleTupleStatement
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
    δ mesh hτp hstrideT hsize hrank hRank base cells hcells bases hbases test htest Kcov _ bW
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
    ((Real.exp_le_exp.mpr hNS).trans hRank) hbudget base cells hcells bases hbases test htest bW
    hPc (hPcP.trans hPerr) hT (hMp.trans (Real.exp_le_exp.mpr hpPc))
    (fun j => (hRup j).trans (Real.exp_le_exp.mpr hpPc))
    (fun j => (hRi j).trans (Real.exp_le_exp.mpr hpPc))
    (fun j => (hσi j).trans (Real.exp_le_exp.mpr hpPc)) hcountc hstrideT hlarge

end Erdos3.VectorPolynomial

end

end OAI
