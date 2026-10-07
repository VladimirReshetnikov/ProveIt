import OAI.Combinatorics.Progressions.Estimates.AllocatedCenteredJointStatement
import OAI.Combinatorics.Progressions.Estimates.AllocatedChosenFunctionalCoarsening

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory Polynomial
open scoped BigOperators Classical NNReal

universe uX

def allocatedTestUniformActualTupleStatement (m dim : ℕ) (keepProjection : Bool := false) : Prop :=
    ∃ A Amass : ℕ, 2 ≤ A ∧ 2 ≤ Amass ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    {P : ℝ} (_hP : 0 ≤ P) (_hG : (Fintype.card G : ℝ) ≤ P)
    (_hL : (S.value : ℝ) ≤ Real.exp P)
    {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
    (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x) (_hdim : dim ≤ m + 1),
    ∃ (d : ℕ) (hd : 0 < d), let : NeZero d := ⟨hd.ne'⟩
    (d : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin dim)) U)] [BorelSpace (SiteTorus (Finset (Fin dim)) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
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
        ((∀ y, physicalDensityProjection.{_, _, uX, 0} U
          (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y) d density (g y)) ∧
          allocatedProjectedFourierData B U b S C V d g A P)
      else id) <|
      ∀ (_hm : (m : ℝ) ≤ P)
        (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
        (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (_hcount : ∀ j : Fin m,
          (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
        (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
        (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
        (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
        (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
        {X : Type uX} [Fintype X] [DecidableEq X]
        {Pmass : ℝ} (_hQ : allocatedJetFourierBudget m dim A P ≤ Pmass)
        (_hX : (Fintype.card X : ℝ) ≤ Pmass)
        (_hXdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ Pmass)
        (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
        (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
        (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
        (N stride : X → ℕ) (_hs : ∀ t, 0 < stride t)
        {Rrank W τ ξ₀ ρ C₀ δ mesh Z : ℝ}
        (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ₀) (_hξ1 : ξ₀ ≤ 1) (_hρ : 0 < ρ)
        (_hτP : 1 / τ ≤ Real.exp Pmass) (_hstride : ∀ t, (stride t : ℝ) ≤ Real.exp Pmass)
        (_hsize : ∀ t, Real.exp ((Pmass + Amass) ^ Amass) ≤ (N t : ℝ))
        (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) Rrank (U j) (poly j))
        (_hRank : Real.exp ((Pmass + Amass) ^ Amass) ≤ Rrank)
        (_hspatial : ∀ t, 8 * (1 + W) * (stride t : ℝ) * ρ ≤ (ξ₀ * τ) * (N t : ℝ))
        (_hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
        (_hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
          (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
        (_hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
        (_hC₀ : 1 ≤ C₀) (_hLC : (S.value : ℝ) ≤ C₀) (_hWC : W ≤ C₀)
        (_hmeshSize : anisotropicSpatialMeshThreshold selection
          (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
        (_hδ : 0 ≤ δ)
        (_hρmove : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
          (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ δ * ρ)
        (_hmesh : 0 < mesh) (_hZ : 0 < Z) (base : X → ℤ)
        (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
        (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
          (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ₀ N) z)
        {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
        (bW : ∀ j, Basis (Kcov j) ℤ
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
        {Pc E T η : ℝ} (_hPc : 0 ≤ Pc) (_hE : 0 ≤ E) (_hT : 0 ≤ T) (_hη : 0 < η) (_hη1 : η ≤ 1)
        (_hMP : (M : ℝ) ≤ Real.exp Pc) (_hRupper : ∀ j, R j ≤ Real.exp Pc)
        (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp Pc) (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp Pc)
        (_hcountc : ∀ j : Fin m,
          (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp Pc)
        (_hηE : η⁻¹ ≤ Real.exp E) (_hstridec : ∀ t, (stride t : ℝ) ≤ Real.exp T)
        (_hlarge : Real.exp (allocatedRefinedJointLengthLog (G := G) B (Fin dim) O Pc E
          ((m+1 : ℕ)*Pc + Fintype.card X*T)) ≤ S.value),
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
        ∀ (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (_htest : ∀ v, ‖test v‖ ≤ 1),
        allocatedRefinedTupleMassEstimate B U b hR hσ S x rows X hM selection hx modulus s hA
          stride reference residue hb o bW d g N hN hW hτ hξ C₀ ρ δ mesh base cells hmass
          (physicalCubeEuclideanSample U d poly hmem) test cap Z η
      )

def allocatedTestUniformActualScalarTupleStatement (m dim : ℕ) (keepProjection : Bool := false) : Prop :=
    ∃ A Amass : ℕ, 2 ≤ A ∧ 2 ≤ Amass ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    {P : ℝ} (_hP : 0 ≤ P) (_hG : (Fintype.card G : ℝ) ≤ P)
    (_hL : (S.value : ℝ) ≤ Real.exp P)
    {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
    (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x) (_hdim : dim ≤ m + 1),
    ∃ (d : ℕ) (hd : 0 < d), let : NeZero d := ⟨hd.ne'⟩
    (d : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin dim)) U)] [BorelSpace (SiteTorus (Finset (Fin dim)) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
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
        ((∀ y, physicalDensityProjection.{_, _, uX, 0} U
          (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y) d density (g y)) ∧
          allocatedProjectedFourierData B U b S C V d g A P)
      else id) <|
      ∀ (_hm : (m : ℝ) ≤ P)
        (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
        (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (_hcount : ∀ j : Fin m,
          (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
        (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
        (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
        (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
        (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
        {X : Type uX} [Fintype X] [DecidableEq X]
        {Perr Pmass : ℝ} (_hPerr : P ≤ Perr)
        (_hQ : allocatedScalarSamplingBudget m dim A P Perr ≤ Pmass)
        {δf ε : ℝ} (_hδf : 0 < δf) (_hδfP : δf⁻¹ ≤ Real.exp Perr)
        (_hε : 0 < ε) (_hεP : 1 / ε ≤ Real.exp Pmass)
        (_hX : (Fintype.card X : ℝ) ≤ Pmass)
        (_hXdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ Pmass)
        (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
        (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
        (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
        (N stride : X → ℕ) (_hs : ∀ t, 0 < stride t)
        {Rrank W τ ξ₀ ρ C₀ δ mesh Z : ℝ}
        (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ₀) (_hξ1 : ξ₀ ≤ 1) (_hρ : 0 < ρ)
        (_hτP : 1 / τ ≤ Real.exp Pmass) (_hstride : ∀ t, (stride t : ℝ) ≤ Real.exp Pmass)
        (_hsize : ∀ t, Real.exp ((Pmass + Amass) ^ Amass) ≤ (N t : ℝ))
        (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) Rrank (U j) (poly j))
        (_hRank : Real.exp ((Pmass + Amass) ^ Amass) ≤ Rrank)
        (_hspatial : ∀ t, 8 * (1 + W) * (stride t : ℝ) * ρ ≤ (ξ₀ * τ) * (N t : ℝ))
        (_hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
        (_hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
          (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
        (_hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
        (_hC₀ : 1 ≤ C₀) (_hLC : (S.value : ℝ) ≤ C₀) (_hWC : W ≤ C₀)
        (_hmeshSize : anisotropicSpatialMeshThreshold selection
          (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
        (_hδ : 0 ≤ δ)
        (_hρmove : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
          (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ δ * ρ)
        (_hmesh : 0 < mesh) (_hZ : 0 < Z) (base : X → ℤ)
        (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
        (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
          (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ₀ N) z)
        {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
        (bW : ∀ j, Basis (Kcov j) ℤ
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
        {Pc E T η : ℝ} (_hPc : 0 ≤ Pc) (_hPcErr : Pc ≤ Perr) (_hE : 0 ≤ E) (_hT : 0 ≤ T) (_hη : 0 < η) (_hη1 : η ≤ 1)
        (_hMP : (M : ℝ) ≤ Real.exp Pc) (_hRupper : ∀ j, R j ≤ Real.exp Pc)
        (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp Pc) (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp Pc)
        (_hcountc : ∀ j : Fin m,
          (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp Pc)
        (_hηE : η⁻¹ ≤ Real.exp E) (_hstridec : ∀ t, (stride t : ℝ) ≤ Real.exp T)
        (_hlarge : Real.exp (allocatedRefinedJointLengthLog (G := G) B (Fin dim) O Pc E
          ((m+1 : ℕ)*Pc + Fintype.card X*T)) ≤ S.value),
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
        ∀ (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (_htest : ∀ v, ‖test v‖ ≤ 1),
        let Aerr := coefficientDeckPeriodCap O Kcov modulus
        let Cψ := ((modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
          anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
        let Vsp := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
          (((1 + W) / S.value) ^ dim) ^ Fintype.card X
        let Merr := η * Aerr *
          (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
            Fintype.card (Σ a : LayerSamplerAxis I n, O a.1)
        allocatedRefinedTupleScalarEstimate B U b hR hσ S x rows X hM selection hx modulus s hA
          stride reference residue hb o bW d g N hN hW hτ hξ C₀ ρ δ mesh base cells hmass
          (physicalCubeEuclideanSample U d poly hmem) test cap Z (Cψ * (Vsp * (Merr + 2 * δf + ε)))
      )

def allocatedTestUniformActualNormalizedTupleStatement (m dim : ℕ) (keepProjection : Bool := false) : Prop :=
    ∃ A Amass : ℕ, 2 ≤ A ∧ 2 ≤ Amass ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    {P : ℝ} (_hP : 0 ≤ P) (_hG : (Fintype.card G : ℝ) ≤ P)
    (_hL : (S.value : ℝ) ≤ Real.exp P)
    {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
    (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x) (_hdim : dim ≤ m + 1),
    ∃ (d : ℕ) (hd : 0 < d), let : NeZero d := ⟨hd.ne'⟩
    (d : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin dim)) U)] [BorelSpace (SiteTorus (Finset (Fin dim)) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
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
        ((∀ y, physicalDensityProjection.{_, _, uX, 0} U
          (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y) d density (g y)) ∧
          allocatedProjectedFourierData B U b S C V d g A P)
      else id) <|
      ∀ (_hm : (m : ℝ) ≤ P)
        (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
        (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (_hcount : ∀ j : Fin m,
          (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
        (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
        (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
        (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
        (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
        {X : Type uX} [Fintype X] [DecidableEq X]
        {p Etarget : ℝ} (_hp : 0 ≤ p) (_hEtarget : 0 ≤ Etarget)
        (_hvarsp : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
        (_hIp : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (_hnp : ∀ j, (n j : ℝ) ≤ p)
        (_hJp : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
        (_hXp : (Fintype.card X : ℝ) ≤ p) (_hCp : ∀ j, (C j : ℝ) ≤ Real.exp p)
        (_hMp : (M : ℝ) ≤ Real.exp p)
        {D : ℝ} (_hD : D ≤ Real.exp p)
        {Perr Pmass : ℝ} (_hPerr : P ≤ Perr)
        (_hAccuracy : allocatedCoefficientAccuracyLog m p (Etarget + 1) ≤ Perr)
        (_hQ : allocatedScalarSamplingBudget m dim A P Perr ≤ Pmass)
        (_hnormdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ Pmass)
        (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
        (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
        (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
        (N stride : X → ℕ) (_hs : ∀ t, 0 < stride t)
        {Rrank W τ ξ₀ ρ C₀ δ mesh : ℝ}
        (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ₀) (_hξ1 : ξ₀ ≤ 1) (_hρ : 0 < ρ)
        (_hWScale : W ≤ D * S.value) (_hWP : W ≤ Real.exp Pmass)
        (_hξP : ξ₀⁻¹ ≤ Real.exp Pmass)
        (_hτP : 1 / τ ≤ Real.exp Pmass) (_hstride : ∀ t, (stride t : ℝ) ≤ Real.exp Pmass)
        (_hsize : ∀ t, Real.exp ((Pmass + Amass) ^ Amass) ≤ (N t : ℝ))
        (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) Rrank (U j) (poly j))
        (_hRank : Real.exp ((Pmass + Amass) ^ Amass) ≤ Rrank)
        (_hspatial : ∀ t, 8 * (1 + W) * (stride t : ℝ) * ρ ≤ (ξ₀ * τ) * (N t : ℝ))
        (_hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
        (_hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
          (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
        (_hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
        (_hC₀ : 1 ≤ C₀) (_hLC : (S.value : ℝ) ≤ C₀) (_hWC : W ≤ C₀)
        (_hmeshSize : anisotropicSpatialMeshThreshold selection
          (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
        (_hδ : 0 ≤ δ)
        (_hρmove : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
          (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ δ * ρ)
        (_hmesh : 0 < mesh) (base : X → ℤ)
        (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
        (_hcells : cells.Nonempty) (bases : Finset (X → ℤ)) (_hbases : bases.Nonempty)
        {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
        (bW : ∀ j, Basis (Kcov j) ℤ
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
        {Pc T : ℝ} (_hPc : 0 ≤ Pc) (_hPcErr : Pc ≤ Perr) (_hT : 0 ≤ T)
        (_hMP : (M : ℝ) ≤ Real.exp Pc) (_hRupper : ∀ j, R j ≤ Real.exp Pc)
        (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp Pc) (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp Pc)
        (_hcountc : ∀ j : Fin m,
          (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp Pc)
        (_hstridec : ∀ t, (stride t : ℝ) ≤ Real.exp T)
        (_hlarge : Real.exp (allocatedRefinedJointLengthLog (G := G) B (Fin dim) O Pc
          (allocatedCoefficientAccuracyLog m p (Etarget + 1))
          ((m+1 : ℕ)*Pc + Fintype.card X*T)) ≤ S.value),
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
        ∀ (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (_htest : ∀ v, ‖test v‖ ≤ 1),
        allocatedRefinedTupleScalarEstimate B U b hR hσ S x rows X hM selection hx modulus s hA
          stride reference residue hb o bW d g N hN hW hτ hξ C₀ ρ δ mesh base cells hmass
          (physicalCubeEuclideanSample U d poly hmem) test cap Z (Z * Real.exp (-Etarget))
      )

def allocatedTestUniformSpatiallyNormalizedTupleStatement (m dim : ℕ) (keepProjection : Bool := false) : Prop :=
    ∃ A Amass : ℕ, 2 ≤ A ∧ 2 ≤ Amass ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    {P : ℝ} (_hP : 0 ≤ P) (_hG : (Fintype.card G : ℝ) ≤ P)
    (_hL : (S.value : ℝ) ≤ Real.exp P)
    {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
    (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x) (_hdim : dim ≤ m + 1),
    ∃ (d : ℕ) (hd : 0 < d), let : NeZero d := ⟨hd.ne'⟩
    (d : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin dim)) U)] [BorelSpace (SiteTorus (Finset (Fin dim)) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
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
        ((∀ y, physicalDensityProjection.{_, _, uX, 0} U
          (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y) d density (g y)) ∧
          allocatedProjectedFourierData B U b S C V d g A P)
      else id) <|
      ∀ (_hm : (m : ℝ) ≤ P)
        (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
        (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (_hcount : ∀ j : Fin m,
          (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
        (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
        (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
        (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
        (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
        {X : Type uX} [Fintype X] [DecidableEq X]
        {p Etarget : ℝ} (_hp : 0 ≤ p) (_hEtarget : 0 ≤ Etarget)
        (_hvarsp : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
        (_hIp : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (_hnp : ∀ j, (n j : ℝ) ≤ p)
        (_hJp : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
        (_hXp : (Fintype.card X : ℝ) ≤ p) (_hCp : ∀ j, (C j : ℝ) ≤ Real.exp p)
        (_hMp : (M : ℝ) ≤ Real.exp p)
        (_hmsp : ((m + 2 : ℕ) : ℝ) ≤ p),
        let ξ₀ := normalizedTupleNarrowWidth X (PrincipalTupleIndex B (layerSamplerDegree I n))
          selection M p Etarget
        let hξ := normalizedTupleNarrowWidth_pos X (PrincipalTupleIndex B (layerSamplerDegree I n))
          selection M p Etarget
        ∀ {D : ℝ} (_hD : D ≤ Real.exp p)
        {Perr Pmass : ℝ} (_hPerr : P ≤ Perr)
        (_hAccuracy : allocatedCoefficientAccuracyLog m p (Etarget + 3) ≤ Perr)
        (_hQ : allocatedScalarSamplingBudget m dim A P Perr ≤ Pmass)
        (_hnormdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ Pmass)
        (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
        (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
        (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
        (N stride : X → ℕ) (_hs : ∀ t, 0 < stride t)
        {Rrank W τ : ℝ}
        (hW : 0 ≤ W) (hτ : 0 < τ),
        let l := allocatedSpatialLateLog (G := G) B P Pmass
        let δ := normalizedTupleRadius X selection M p Etarget W
        let mesh := δ / 4
        ∀ (_hWScale : W ≤ D * S.value) (_hWP : W ≤ Real.exp Pmass)
        (_hξP : ξ₀⁻¹ ≤ Real.exp Pmass)
        (_hτP : 1 / τ ≤ Real.exp Pmass) (_hstride : ∀ t, (stride t : ℝ) ≤ Real.exp Pmass)
        (_hsize : ∀ t, Real.exp ((Pmass + Amass) ^ Amass) ≤ (N t : ℝ))
        (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) Rrank (U j) (poly j))
        (_hRank : Real.exp ((Pmass + Amass) ^ Amass) ≤ Rrank)
        (_hspatialSize : ∀ t, Real.exp (normalizedTupleSideLog X
          (PrincipalTupleIndex B (layerSamplerDegree I n)) selection p Etarget l) ≤ (N t : ℝ))
        (_hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
        (base : X → ℤ)
        (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
        (_hcells : cells.Nonempty) (bases : Finset (X → ℤ)) (_hbases : bases.Nonempty)
        {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
        (bW : ∀ j, Basis (Kcov j) ℤ
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
        {Pc T : ℝ} (_hPc : 0 ≤ Pc) (_hPcErr : Pc ≤ Perr) (_hT : 0 ≤ T)
        (_hMP : (M : ℝ) ≤ Real.exp Pc) (_hRupper : ∀ j, R j ≤ Real.exp Pc)
        (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp Pc) (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp Pc)
        (_hcountc : ∀ j : Fin m,
          (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp Pc)
        (_hstridec : ∀ t, (stride t : ℝ) ≤ Real.exp T)
        (_hlarge : Real.exp (allocatedRefinedJointLengthLog (G := G) B (Fin dim) O Pc
          (allocatedCoefficientAccuracyLog m p (Etarget + 3))
          ((m+1 : ℕ)*Pc + Fintype.card X*T)) ≤ S.value),
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
        ∀ (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (_htest : ∀ v, ‖test v‖ ≤ 1),
        ‖allocatedRefinedTupleDifference B U b hR hσ S x rows X hM selection hx modulus s hA
          stride reference residue hb o bW d g N hN hW hτ hξ mesh base cells hmass
          (physicalCubeEuclideanSample U d poly hmem) test Z‖ ≤ Real.exp (-Etarget)
      )

def allocatedTestUniformBudgetedTupleStatement (m dim : ℕ) (keepProjection : Bool := false) : Prop :=
    ∃ A Amass : ℕ, 2 ≤ A ∧ 2 ≤ Amass ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    {P : ℝ} (_hP : 0 ≤ P) (_hG : (Fintype.card G : ℝ) ≤ P)
    (_hL : (S.value : ℝ) ≤ Real.exp P)
    {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
    (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x) (_hdim : dim ≤ m + 1),
    ∃ (d : ℕ) (hd : 0 < d), let : NeZero d := ⟨hd.ne'⟩
    (d : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin dim)) U)] [BorelSpace (SiteTorus (Finset (Fin dim)) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
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
        ((∀ y, physicalDensityProjection.{_, _, uX, 0} U
          (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y) d density (g y)) ∧
          allocatedProjectedFourierData B U b S C V d g A P)
      else id) <|
      ∀ (_hm : (m : ℝ) ≤ P)
        (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
        (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (_hcount : ∀ j : Fin m,
          (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
        (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
        (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
        (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
        (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
        {X : Type uX} [Fintype X] [DecidableEq X]
        {p Etarget : ℝ} (_hp : 0 ≤ p) (_hEtarget : 0 ≤ Etarget)
        (_hvarsp : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
        (_hIp : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (_hnp : ∀ j, (n j : ℝ) ≤ p)
        (_hJp : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
        (_hXp : (Fintype.card X : ℝ) ≤ p) (_hCp : ∀ j, (C j : ℝ) ≤ Real.exp p)
        (_hMp : (M : ℝ) ≤ Real.exp p)
        (_hmsp : ((m + 2 : ℕ) : ℝ) ≤ p),
        let ξ₀ := normalizedTupleNarrowWidth X (PrincipalTupleIndex B (layerSamplerDegree I n))
          selection M p Etarget
        let hξ := normalizedTupleNarrowWidth_pos X (PrincipalTupleIndex B (layerSamplerDegree I n))
          selection M p Etarget
        ∀ {D : ℝ} (_hD : D ≤ Real.exp p),
        let Perr := allocatedTupleErrorBudget m P p Etarget
        let Pmass := allocatedUnifiedSamplingBudget m dim A P p Etarget
        ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
        (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
        (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
        (N stride : X → ℕ) (_hs : ∀ t, 0 < stride t)
        {Rrank W τ : ℝ}
        (hW : 0 ≤ W) (hτ : 0 < τ),
        let δ := normalizedTupleRadius X selection M p Etarget W
        let mesh := δ / 4
        ∀ (_hWScale : W ≤ D * S.value)
        (_hτP : 1 / τ ≤ Real.exp Pmass) (_hstride : ∀ t, (stride t : ℝ) ≤ Real.exp Pmass)
        (_hsize : ∀ t, Real.exp ((P + p + Etarget + Amass) ^ Amass) ≤ (N t : ℝ))
        (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) Rrank (U j) (poly j))
        (_hRank : Real.exp ((P + p + Etarget + Amass) ^ Amass) ≤ Rrank)
        (_hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
        (base : X → ℤ)
        (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
        (_hcells : cells.Nonempty) (bases : Finset (X → ℤ)) (_hbases : bases.Nonempty)
        {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
        (bW : ∀ j, Basis (Kcov j) ℤ
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
        {Pc T : ℝ} (_hPc : 0 ≤ Pc) (_hPcErr : Pc ≤ Perr) (_hT : 0 ≤ T)
        (_hMP : (M : ℝ) ≤ Real.exp Pc) (_hRupper : ∀ j, R j ≤ Real.exp Pc)
        (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp Pc) (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp Pc)
        (_hcountc : ∀ j : Fin m,
          (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp Pc)
        (_hstridec : ∀ t, (stride t : ℝ) ≤ Real.exp T)
        (_hlarge : Real.exp (allocatedRefinedJointLengthLog (G := G) B (Fin dim) O Pc
          (allocatedCoefficientAccuracyLog m p (Etarget + 3))
          ((m+1 : ℕ)*Pc + Fintype.card X*T)) ≤ S.value),
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
        ∀ (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (_htest : ∀ v, ‖test v‖ ≤ 1),
        ‖allocatedRefinedTupleDifference B U b hR hσ S x rows X hM selection hx modulus s hA
          stride reference residue hb o bW d g N hN hW hτ hξ mesh base cells hmass
          (physicalCubeEuclideanSample U d poly hmem) test Z‖ ≤ Real.exp (-Etarget)
      )

def allocatedTestUniformChosenScaleTupleStatement (m dim : ℕ) (keepProjection : Bool := false) : Prop :=
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
        ((∀ y, physicalDensityProjection.{_, _, uX, 0} U
          (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y) d density (g y)) ∧
          allocatedProjectedFourierData B U b S C V d g A P)
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
        ∀ (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (_htest : ∀ v, ‖test v‖ ≤ 1),
        ‖allocatedRefinedTupleDifference B U b hR hσ S x rows X hM selection hx modulus s hA
          stride reference residue hb o bW d g N hN hW hτ hξ mesh base cells hmass
          (physicalCubeEuclideanSample U d poly hmem) test Z‖ ≤ Real.exp (-Etarget)
      )

def allocatedTestUniformOriginalChosenTupleStatement (m dim : ℕ) : Prop :=
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
        (N stride : X → ℕ) (_hs : ∀ t, 0 < stride t)
        {Rrank τ : ℝ} (hτ : 0 < τ),
        let δ := normalizedTupleRadius X selection M p (Etarget + 1) W
        let mesh := δ / 4
        ∀ (_hτp : 1 / τ ≤ Real.exp p) (_hstrideT : ∀ t, (stride t : ℝ) ≤ Real.exp T)
        (_hsize : ∀ t, Real.exp ((p + Etarget + T + a) ^ a) ≤ (N t : ℝ))
        (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) Rrank (U j) (poly j))
        (_hRank : Real.exp ((p + Etarget + T + a) ^ a) ≤ Rrank)
        (base : X → ℤ)
        (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
        (_hcells : cells.Nonempty) (bases : Finset (X → ℤ)) (_hbases : bases.Nonempty)
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
        ∀ (test : Finset (Fin dim) → (X → ℝ) → ℂ) (_htest : ∀ s v, ‖test s v‖ ≤ 1),
        ‖allocatedOriginalTupleDifference B U b hR hσ S x rows X hM selection hx modulus s hA
          stride reference residue hb o bW d N hN hW hτ hξ mesh base cells hmass
          (physicalCubeEuclideanSample U d poly hmem) (physicalCubeSiteTest test) Z poly hmem‖ ≤ Real.exp (-Etarget)

def allocatedTestUniformCenteredChosenTupleStatement (m dim : ℕ) : Prop :=
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
        (base : X → ℤ)
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
        ∀ (test : Finset (Fin dim) → (X → ℝ) → ℂ) (_htest : ∀ s v, ‖test s v‖ ≤ 1),
        ‖allocatedOriginalTupleDifference B U b hR hσ S x rows X hM selection hx modulus s hA
          stride reference residue hb o bW d N hN hW hτ hξ mesh base cells hmass
          (physicalCubeEuclideanSample U d centeredPoly centeredMem) (physicalCubeSiteTest test)
          Z centeredPoly centeredMem‖ ≤ Real.exp (-Etarget)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem allocatedTestUniformActualTupleComparison (m dim : ℕ) : allocatedTestUniformActualTupleStatement m dim true := by
  unfold allocatedTestUniformActualTupleStatement
  classical
  obtain ⟨A, Amass, hA, hAmass, hfamily⟩ := exists_allocated_projected_density_family m dim
  refine ⟨A, Amass, hA, hAmass, ?_⟩
  intro G _ _ I _ _ n B _ _ J _ U b R σ S x P hP hG hL M hM selection hx hdim
  obtain ⟨d, hd, hdb, hfamily⟩ := hfamily B U b S (fun _ => 0) x hP hG
    (fun _ => by simpa only [Int.cast_zero, abs_zero] using (Real.exp_pos P).le) hL hx.2
  let : NeZero d := ⟨hd.ne'⟩
  refine ⟨d, hd, hdb, ?_⟩
  intro _ _ _ _ _ hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ _ _ ν _ _
    O rows density cap cover ξ
  let _ := coefficientTorus_compact_of_lattice (K := LayerSamplerVariables G I n B) U
  have hsmall₀ := allocatedPhysicalChartRadius_density_small (G := G) B (Fin dim) Cinv R
    hCinv (fun j => (hR j).le) hsmall
  obtain ⟨g, hgc, hgb, hgi, hgm, hglaw, hprojection, hdata⟩ :=
    hfamily hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall₀ μ ν
  have hfourier : allocatedProjectedFourierData B U b S C V d g A P := by
    refine ⟨hdb.trans (Real.exp_le_exp.mpr (allocatedJetFourierBudget_dominates m dim A hP).1), ?_⟩
    intro hm hK hRP hσP hcount hI hn hJ hAP hCP hVP y δ hδ hδP
    exact (hdata hm hK hRP hσP hcount hI hn hJ hAP hCP hVP y).1 hδ hδP
  refine ⟨g, hgc, hgb, hgi, hgm, hglaw, ⟨hprojection, hfourier⟩, ?_⟩
  intro hm₀ hK hRP hσP hcount hI hn hJ hAP hCP hVP X _ _ Pmass hQ hX hXdim
    poly hpoly hmem N stride hs Rrank W τ ξ₀ ρ C₀ δ mesh Z hW hτ hξ hξ1 hρ
    hτP hstride hsize hrank hRank hspatial hρ8 hρshift hbudget hC₀ hLC hWC hmeshSize hδ
    hρmove hmesh hZ base cells hmass Kcov _ bW Pc E T η hPc hE hT hη hη1
    hMP hRupper hRi hσi hcountc hηE hstridec hlarge
  have hN (t : X) : 0 < N t := by
    exact_mod_cast (Real.exp_pos _).trans_le (hsize t)
  have hcomparison := allocatedGoodKernel_original_mass_tuple_density B U b hR hσ S x rows X
    hM selection hx (by simpa only [Fintype.card_fin] using hdim)
    (fun _ => Subtype.val_injective) (fun _ z => z.property) hσ1 hPc hE hT hη hη1
    hMP hRupper hRi hσi hcountc hηE hlarge
  unfold allocatedMassTupleStatement at hcomparison
  obtain ⟨modulus, hmodulus, hrest⟩ := hcomparison
  let : NeZero modulus := ⟨hmodulus.ne'⟩
  obtain ⟨hmod, hspatialPeriod, hperiod, s, hsA, hi, hstrideData⟩ := hrest
  obtain ⟨hRefined, hdiv, hbound, hlengths, reference, residue, href, hr, hcompare⟩ :=
    hstrideData stride hs hstridec
  let : NeZero (residueRefinedPeriod modulus stride) := ⟨hRefined.ne'⟩
  refine ⟨hN, modulus, hmodulus, hmod, hspatialPeriod, hperiod, s, hsA, hi,
    hRefined, hdiv, hbound, hlengths, reference, residue, href, hr, ?_⟩
  intro test htest
  have hcap : 0 ≤ cap := pow_nonneg (NNReal.coe_nonneg _) _
  unfold allocatedRefinedTupleMassEstimate
  exact hcompare hb o Cinv hCinv hchart hsmall bW d μ ν g hgc
    (fun y z => (hgb y z).1) hglaw N hN hW hτ hρ hbudget hC₀ hLC hWC hξ hξ1
    hspatial hmeshSize hρ8 hδ hρshift hρmove hmesh base cells hmass
    (physicalCubeEuclideanSample U d poly hmem) test htest hcap hZ
    (fun y v => (hgb y (physicalCubeEuclideanSample U d poly hmem v)).2)
    (fun y y₀ a => (hdata hm₀ hK hRP hσP hcount hI hn hJ hAP hCP hVP y).2
      hQ hX hXdim poly hpoly hmem N stride hs hW hτ hξ1 hρ hτP hstride hsize hrank hRank
      hspatial hρ8 hρshift y₀ base a)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory Polynomial
open scoped BigOperators Classical NNReal

universe uX

def allocatedTestUniformCoarseJointStatement (m dim : ℕ) : Prop :=
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
    let P := allocatedChosenScaleBudget m p (Etarget + 2) T
    let Pc := allocatedComparisonDimension m p
    let L₀ := allocatedNormalizedInitialScale m p Pc (Etarget + 2) T
    ∃ S : LayerSamplerScale (G := G) B U b R σ,
      S = allocatedPrimitiveNormalizedScale B U b hR hσ p (Etarget + 2) T ∧
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
          selection M p (Etarget + 2)
        let hξ := normalizedTupleNarrowWidth_pos X (PrincipalTupleIndex B (layerSamplerDegree I n))
          selection M p (Etarget + 2)
        let W : ℝ := Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ)
        let hW : 0 ≤ W := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        let Pmass := allocatedUnifiedSamplingBudget m dim A P p (Etarget + 2)
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
        let mesh := normalizedTupleRadius X selection M p (Etarget + 2)
          (Fintype.card (LayerSamplerVariables G I n B)) / 4
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
        ∃ reference : (X → ℤ) → (Finset (Fin dim) → (X → ℝ) → ℂ) → ℂ,
        (∀ base, allocatedRefinedSiteFunctional (τ := τ) (ξ := ξ₀) B U b hR hσ S x rows X
          hM selection hx stride hb o bW d N hW mesh base cells
          (physicalCubeEuclideanSample U d centeredPoly centeredMem) Z Pc T (Real.exp (coefficientErrorVolumeLog p + 4)) (reference base)) ∧
        ∀ (test : Finset (Fin dim) → (X → ℝ) → ℂ) (_htest : ∀ s v, ‖test s v‖ ≤ 1),
        (∀ base, ‖allocatedOriginalTupleSource B U b hR hσ S x X stride hb o N hN hW hτ hξ
          base cells hmass (physicalCubeSiteTest test) Z centeredPoly centeredMem -
            reference base test‖ ≤ Real.exp (-Etarget)) ∧
        ‖law.complexMean (fun z => physicalCubeSiteTest test (physicalCubeRootDifferences
          (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x z.1)
          (allocatedPhysicalCubeDirections B U b S x z.1) z.2.1.val z.2.2.val)) -
            (𝔼 base ∈ bases, reference base test)‖ ≤ Real.exp (-Etarget)

end Erdos3.VectorPolynomial

end

end OAI
