import OAI.Combinatorics.Progressions.Lattices.ActualFixedSpatialSlicedCRTIdentification
import OAI.Combinatorics.Progressions.Probability.ActualFixedSpatialSlicedDensityIdentification

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j) (C : ℝ)
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
variable {sampleFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n}
variable {readFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  AllocatedActualCoefficientIndex G X I Eout n B → ℤ}

omit [Fintype Tsp] in

theorem centered_recovery
    (h : AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ originalpoly hmem
      (allocatedShortAxis (I := I) U b S.value) spatial kernel block C
      center path.center path.base sampleFn readFn)
    (hz : allocatedCenteredJointDensity B U b hb o hR hσ S originalpoly hmem
      center path.base path.noise ≠ 0)
    (hsample : sampleFn path.noise = path.sample)
    (hread : readFn path.noise = path.read) :
    canonicalCoefficientSample U b hb o path.sample =
      affineSampleCoefficientTorus U (path.physicalPolynomial originalpoly)
        (path.physicalPolynomial_mem originalpoly hmem)
        (fun k x => (jointIntegerFrame (path.base, path.noise) k x : ℝ)) ∧
    (∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (path.sample j) ∧
      mixedArraySupported (allocatedLayerCenters B U b S j)
        (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j)
        (path.sample j)) ∧
    (∀ d, |coefficientSamplerAmbientPoint U b o path.sample d| < 1 / 2) ∧
    (∀ (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
      ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n Eout q → Prop,
        coefficientDeckChartEvent U bW b hb o q event
          (affineCoefficientCoverSample U (path.physicalPolynomial originalpoly)
            (path.physicalPolynomial_mem originalpoly hmem) q
            (fun k x => (jointIntegerFrame (path.base, path.noise) k x : ℝ))) ↔
          event (allocatedReadCoefficientChartResidues (fun i => (path.read i : ZMod q)))) := by
  have hr := h.centeredJointFrame_recovery B U bW b hb o S hR hσ originalpoly hmem
    (allocatedShortAxis (I := I) U b S.value) spatial kernel block C path.noise hz
  rw [h.centeredJointFrame_read B U bW b hb o S hR hσ originalpoly hmem
    (allocatedShortAxis (I := I) U b S.value) spatial kernel block C path.noise,
    hsample, hread] at hr
  exact ⟨hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.2⟩

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

local instance slicedDecayModulusNeZero : NeZero slice.path.referenceModulus :=
  ⟨slice.path.referenceModulus_pos.ne'⟩

omit [Fintype Tsp] in

theorem stepInputLaw_sample_characteristic_decay (hm : 0 < m)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U b S))
    (χ : AddChar (Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod slice.path.referenceModulus) ℂ) :
    ‖finiteImageCharacteristic slice.stepInputLaw
      (fun t j => (integerLongPolynomialOutput
        (allocatedForecastPolynomial (allocatedShortAxis (I := I) U b S.value)
          slice.path.base slice.path.noise (allocatedReadDeck slice.path.read)
          (allocatedOriginalSampleCongruenceProjection B U b S slice.path.sample))
        (fun k => (y k.1 k.2 : ℤ)) slice.path.referenceModulus t j :
          ZMod slice.path.referenceModulus)) χ‖ ≤
      ((slice.path.Rbad * ∏ p : slice.path.primes,
        p.val ^ slice.path.prescribed p.val : ℕ) : ℝ) ^
        (modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) *
          modularRankChargeFactor m) *
        (orderOf χ : ℝ) ^ (-modularRankDecayExponent m
          (modularForecastRankConstant m Dmod : ℝ)) := by
  have h := slice.path.reference_characteristic_decay hm y χ
  rw [slice.referenceInputLaw_eq_step, slice.referencePolynomial_eq_sample] at h
  exact h

end ActualFixedSpatialSlicedForecastPath

namespace ActualFixedSpatialForecastSetup
variable {B U b S Dmod τ δslice}
variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)

omit [DecidableEq X] [Fintype A] in
include s in

theorem modular_decay_dimension :
    ((Fintype.card (Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value))) + 2 : ℕ) : ℝ) ≤
      modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) := by
  exact allocatedCongruenceForecastRankConstant_dimension
    (allocatedShortAxis (I := I) U b S.value) s.hm Dmod s.hDmod

end ActualFixedSpatialForecastSetup
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [decX : DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp))
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0)) (S.value : ℝ) physicalN τ δslice P Pbad Ppres)

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ δslice)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (originalpoly j))
variable (ξ : ℝ) (hξ : 0 < ξ)
variable (hbox : ∀ x, 0 < physicalN x)
variable (hframe : slice.path.noise ∈ rectangularWeightIndices 0
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
    (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ physicalN) 1)
variable {t δ ε η : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
variable (hδ : 0 < δ) (hδone : δ ≤ 1)
variable (hdense : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  ∀ p : B a.val × Fin (layerSamplerDegree I n a.val), δ * S.value ≤
    ((integerProgressionSupport (slice.principalStart ⟨a.val,p⟩) (slice.step : ℤ)
      (slice.principalLength ⟨a.val,p⟩)).card : ℝ))
variable (q : ℕ) [NeZero q]
variable (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (hqN : q ∣ slice.path.referenceModulus)
variable (hsizeG : ∀ g, q ≤ slice.kernelLength g)
variable (hsmallG : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / slice.kernelLength g) < 1)
variable (hsize : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  ∀ p : B a.val × Fin (layerSamplerDegree I n a.val), q ≤ slice.principalLength ⟨a.val,p⟩)
variable (hsmall : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  ∀ p : B a.val × Fin (layerSamplerDegree I n a.val),
    scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / slice.principalLength ⟨a.val,p⟩) < 1)
variable (hε : 0 ≤ ε) (hmesh : (slice.step : ℝ) / S.value ≤ ε)
variable (hη : 0 < η)
variable (htail : |t| * polynomialMassC2Budget
  (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val))) m 1 ≤
  slicedPrincipalC2Tolerance
    (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      B a.val × Fin (layerSamplerDegree I n a.val)))
    (Fintype.card {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}) m 1
    (unitProfilePrincipalLowerBound B) (δ / 2) s.L η)

local notation "Active" => {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}
local notation "activeH" => (fun j : (Σ a : Active, B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a))) =>
  slice.principalLength (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))
local notation "activeStart" => (fun j : (Σ a : Active, B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a))) =>
  slice.principalStart (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))
local notation "selected" => allocatedShortIntegerSelection U b S.value
local notation "Original" => PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U b S)
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis U b S.value))
local notation "Knative" => Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U b o R)
local instance actualComparisonReferenceNeZero : NeZero slice.path.referenceModulus :=
  ⟨slice.path.referenceModulus_pos.ne'⟩

noncomputable def nativeMean : ℂ :=
  allocatedSlicedNativeEvalMean B U b S W slice.path.base slice.path.noise physicalN
    (slice.path.physicalPolynomial originalpoly) slice.principalLength slice.principalStep
    slice.principalStart slice.principalInside slice.principalLength_pos slice.kernelLength
    slice.kernelLength_two slice.kernelStart slice.step slice.kernelSupport activeH activeStart
    (fun j => slice.activeLength_two s.hδslice j.1 j.2) (fun j => slice.activeSupport j.1 j.2)

noncomputable def decayConstant : ℝ :=
  ((slice.path.Rbad * ∏ p : slice.path.primes, p.val ^ slice.path.prescribed p.val : ℕ) : ℝ) ^
    (modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) * modularRankChargeFactor m)

variable (gridVolume : ℝ) (hVpos : 0 < gridVolume)
local notation "κ" => ((forecastGeometricJacobian (X := X) (I := I) U b R S.value gridVolume τ : ℝ) : ℂ)
local notation "referenceTarget" => forecastLawDensityPhysicalTarget B U b S slice.principalLaw
  (slice.density s.hBactive) selected slice.path.sample slice.path.commonTuple
  (fun _ : Original => slice.path.referenceInputLaw)
  (fun y => integerLongPolynomialOutput slice.path.referencePolynomial
    (fun k => (y (Prod.fst k) (Prod.snd k) : ℤ)) slice.path.referenceModulus)
  slice.path.referenceModulus gridVolume slice.path.base physicalN τ o hb bW

variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)
variable (htrimbase : slice.path.base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN))
variable {Findex : Type} [Fintype Findex] {pf cf : ℝ} {Lf : ℝ≥0}
variable (F : Findex → NormalizedPolynomialTwist X (Σ j, J j) pf cf Lf)
variable (nativeCoeff : Findex → ℂ) (δnative : ℝ)
variable (happrox : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
  (hp : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ),
  ‖((forecastGeometricJacobian (X := X) (I := I) U b R S.value gridVolume τ : ℝ) : ℂ) *
    forecastLawDensityPhysicalTarget B U b S slice.principalLaw (slice.density s.hBactive)
      (allocatedShortIntegerSelection U b S.value) slice.path.sample slice.path.commonTuple
      (fun _ : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U b S) =>
        slice.path.referenceInputLaw)
      (fun y => integerLongPolynomialOutput slice.path.referencePolynomial
        (fun k => (y (Prod.fst k) (Prod.snd k) : ℤ)) slice.path.referenceModulus)
      slice.path.referenceModulus gridVolume slice.path.base physicalN τ o hb bW poly hp u -
    ∑ i, nativeCoeff i * (F i).eval physicalN poly u‖ ≤ δnative)
variable {Pambient Eprec Rrank M : ℝ} (hPambient : 0 ≤ Pambient) (hEprec : 0 ≤ Eprec)
variable (hPP : s.P ≤ Pambient)
variable (hLip : ((Lip * max 1 (Real.toNNReal cf) + Lf * max 1 (Real.toNNReal coverCap) : ℝ≥0) : ℝ) ≤ Real.exp Pambient)
variable (hcoverF : ∀ i, ((W.cover * (F i).cover : ℕ) : ℝ) ≤ Real.exp Pambient)
variable (hmodF : ∀ i, ((W.modulus * (F i).modulus : ℕ) : ℝ) ≤ Real.exp Pambient)
variable (hmass : ∑ i, ‖nativeCoeff i‖ ≤ M)
variable (hlarge : ∀ i, Real.exp ((max Pambient Eprec + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ (physicalN i : ℝ))
variable (hRrank : Real.exp ((max Pambient Eprec + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ Rrank)
variable (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (physicalN i : ℝ))
  Rrank (U j) (originalpoly j))
variable (cutoff : ℕ) (hcutoff : 0 < cutoff)
variable {δgrid : ℝ} (hδgrid : 0 ≤ δgrid) (hδgrid1 : δgrid ≤ 1)
variable (hgridmesh : ∀ j, ((q * cutoff : ℕ) : ℝ) /
  forecastJointGridScale U b R S.value physicalN τ j ≤ δgrid)

noncomputable def comparisonError : ℝ :=
  allocatedSlicedPhysicalComparisonError B U b S ξ slice.kernelLength (t := t) activeH q
    (ε := ε) (η := η) (Kφ := Knative) +
  ((2 * δnative + M * Real.exp (-Eprec)) +
    allocatedSlicedPhysicalAmbientGridError (B := B) (U := U) (basis := b) (S := S) (E := Eout)
      (τ := τ) (ξ := ξ) (box := physicalN) (integerFrame := slice.path.noise)
      (HG := slice.kernelLength) (hHG := slice.kernelLength_two) (cG := slice.kernelStart)
      (stepG := slice.step) (hstepG := slice.step_pos) (e := spatialEquiv)
      (h0 := slice.analyticKernelDetFalse ξ) (h1 := slice.analyticKernelDetTrue ξ)
      (hδ := hδ) (o := o) (Lip := Lip) (cutoff := cutoff) (D := slice.decayConstant) (δgrid := δgrid))

variable (C : ℝ)
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
variable {sampleFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n}
variable {readFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  AllocatedActualCoefficientIndex G X I Eout n B → ℤ}
variable (hglobal : AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ
  originalpoly hmem (allocatedShortAxis (I := I) U b S.value) spatial kernel block C
  center slice.path.center slice.path.base sampleFn readFn)
variable (hz : allocatedCenteredJointDensity B U b hb o hR hσ S originalpoly hmem
  center slice.path.base slice.path.noise ≠ 0)
variable (hsampleAt : sampleFn slice.path.noise = slice.path.sample)
variable (hreadAt : readFn slice.path.noise = slice.path.read)

include hR hσ hdegree hξ hbox hframe ht hσbound hδ hδone hdense hperiod hcover hqN
  hsizeG hsmallG hsize hsmall hε hmesh hη htail hVpos ν hlattice hcompact
  hmargin htrimbase happrox hPambient hEprec hPP hLip hcoverF hmodF hmass hlarge
  hRrank hrank hcutoff hδgrid hδgrid1 hgridmesh hglobal hz hsampleAt hreadAt in

theorem native_ambient_comparison :
    ‖slice.nativeMean s W originalpoly -
      (𝔼 u ∈ integerBox physicalN,
        W.eval physicalN (slice.path.physicalPolynomial originalpoly) u *
          (κ * referenceTarget (slice.path.physicalPolynomial originalpoly)
            (slice.path.physicalPolynomial_mem originalpoly hmem) u))‖ ≤
      slice.comparisonError (Lip := Lip) (ξ := ξ) (t := t) (δ := δ) (ε := ε) (η := η) (q := q)
        (hδ := hδ) (o := o) (δnative := δnative) (M := M) (Eprec := Eprec) (cutoff := cutoff) (δgrid := δgrid) := by
  cases Subsingleton.elim decX (Classical.decEq X)
  let := Classical.decEq X
  let := slice.path.primeNeZero
  have hr := slice.path.centered_recovery bW hb o originalpoly hmem C
    hglobal hz hsampleAt hreadAt
  have hframeEq : (fun k x => (jointIntegerFrame (slice.path.base, slice.path.noise) k x : ℝ)) =
      (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B)
        slice.path.base + slice.path.noise) (k,x) : ℝ)) := by
    funext k x
    cases k <;> simp [jointIntegerFrame, integerBaseTranslation, baseArrayJoin]
  rw [hframeEq] at hr
  have hphysicalDegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1)
      (slice.path.physicalPolynomial originalpoly j) :=
    fun j => (hdegree j).subtractConstant _
  have hphysicalRank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (physicalN i : ℝ)) Rrank (U j)
      (slice.path.physicalPolynomial originalpoly j) := by
    intro j
    exact (hasLayerSamplingRank_subtractConstant_iff (Nat.succ_pos j.val)
      _ _ _ _ _).mpr (hrank j)
  have hnonempty : ∀ a : Active, Nonempty (B a.val) := fun a =>
    Fintype.card_pos_iff.mp (lt_of_lt_of_le (by decide : 0 < 4) (s.hBactive a))
  let bActive : ∀ a : Active, B a.val := fun a => Classical.choice (hnonempty a)
  have hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ Pambient := by
    simpa only [Fintype.card_sigma] using s.hdim.trans (s.hDP.trans hPP)
  have hPdecay := s.modular_decay_dimension
  have hdecay := slice.stepInputLaw_sample_characteristic_decay s.hm
  have happrox' := happrox
  rw [slice.density_eq_allocatedSlicedPhysicalForecastDensity s.hBactive s.hδslice ξ,
    slice.referenceInputLaw_eq_step, slice.referencePolynomial_eq_sample] at happrox'
  dsimp only [nativeMean, comparisonError]
  rw [slice.density_eq_allocatedSlicedPhysicalForecastDensity s.hBactive s.hδslice ξ,
    slice.referenceInputLaw_eq_step, slice.referencePolynomial_eq_sample]
  dsimp only [principalLaw, stepInputLaw] at happrox' hdecay ⊢
  exact allocatedFixedPath_sliced_native_ambient_comparison
    (B := B) (U := U) (basis := b) (hR := hR) (hσ := hσ) (S := S)
    (primes := fun p : slice.path.primes => p.val)
    (exponent := fun p : slice.path.primes => slice.path.exponent p.val)
    (HP := slice.principalLength) (stepP := slice.principalStep)
    (cP := slice.principalStart) (hinsideP := slice.principalInside)
    (hHP := slice.principalLength_pos) (τ := τ) (ξ := ξ) (hτ := s.hτ) (hξ := hξ)
    (box := physicalN) (hbox := hbox) (integerFrame := slice.path.noise) (hframe := hframe)
    (HG := slice.kernelLength) (hHG := slice.kernelLength_two) (cG := slice.kernelStart)
    (stepG := slice.step) (hstepG := slice.step_pos) (hcontainedG := slice.kernelSupport)
    (e := spatialEquiv) (h0 := slice.analyticKernelDetFalse ξ)
    (h1 := slice.analyticKernelDetTrue ξ) (hB := s.hBactive)
    (sample := slice.path.sample) (hs := slice.path.hs) (ht := ht) (hσbound := hσbound)
    (H := fun j => slice.principalLength ⟨j.1.val,j.2⟩)
    (c := fun j => slice.principalStart ⟨j.1.val,j.2⟩)
    (hH := fun j => slice.activeLength_two s.hδslice j.1 j.2)
    (hδ := hδ) (hsubset := fun j => slice.activeSupport j.1 j.2)
    (hdense := fun j => hdense j.1 j.2) (q := q) (hsizeG := hsizeG) (hsmallG := hsmallG)
    (hsize := fun j => hsize j.1 j.2) (hsmall := fun j => hsmall j.1 j.2)
    (hε := hε) (hmesh := fun _ => hmesh) (hδone := hδone)
    (b := bActive) (hη := hη) (A := s.L) (hA := s.hL) (htail := htail)
    (hb := hb) (o := o) (bW := bW) (W := W) (hm := s.hm)
    (hperiod := hperiod) (hcover := hcover) (xref := slice.path.commonTuple)
    (base := slice.path.base) (read := slice.path.read)
    (hp := fun p => slice.path.prime p.val p.property)
    (hcoprime := primePower_crt_coprime (fun p : slice.path.primes => p.val)
      (fun p : slice.path.primes => slice.path.exponent p.val)
      (fun p => slice.path.prime p.val p.property) Subtype.val_injective)
    (hqN := hqN) (hV := hVpos.ne')
    (nativePoly := slice.path.physicalPolynomial originalpoly)
    (hmem := slice.path.physicalPolynomial_mem originalpoly hmem)
    (hdegree := hphysicalDegree) (hbase := hr.1) (hsmallChart := hr.2.2.1)
    (hread := hr.2.2.2 W.cover W.cover_pos)
    (ν := ν) (hσ1 := s.hσ1) (radius := s.radius)
    (hradius0 := by exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3) s.hr3)
    (hradius3 := s.hr3) (hradius := s.hradius)
    (chartCap := s.inverse) (hchartCap := s.hinverse) (hchart := s.hchart)
    (hchartBudget := s.hbudget) (hmargin := hmargin) (htrimbase := htrimbase)
    (hVpos := hVpos) (F := F) (nativeCoeff := nativeCoeff) (δnative := δnative)
    (happrox := happrox') (hPambient := hPambient) (hEprec := hEprec)
    (hX := s.hX.trans hPP) (hdim := hdim) (hLip := hLip) (hcoverF := hcoverF)
    (hmodF := hmodF) (hmass := hmass) (hlarge := hlarge) (hRrank := hRrank)
    (hrank := hphysicalRank) (cutoff := cutoff) (hcutoff := hcutoff)
    (D := slice.decayConstant) (hD := Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (hPdecay := hPdecay) (hdecay := hdecay) (hδgrid := hδgrid)
    (hδgrid1 := hδgrid1) (hgridmesh := hgridmesh)

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [decX : DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp))
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0)) (S.value : ℝ) physicalN τ δslice P Pbad Ppres)

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ δslice)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (originalpoly j))
variable (ξ : ℝ) (hξ : 0 < ξ)
variable (hbox : ∀ x, 0 < physicalN x)
variable (hframe : slice.path.noise ∈ rectangularWeightIndices 0
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
    (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ physicalN) 1)
variable {t δ ε η : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
variable (hδ : 0 < δ) (hδone : δ ≤ 1)
variable (hdense : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  ∀ p : B a.val × Fin (layerSamplerDegree I n a.val), δ * S.value ≤
    ((integerProgressionSupport (slice.principalStart ⟨a.val,p⟩) (slice.step : ℤ)
      (slice.principalLength ⟨a.val,p⟩)).card : ℝ))
variable (q : ℕ) [NeZero q]
variable (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (hqN : q ∣ slice.path.referenceModulus)
variable (hsizeG : ∀ g, q ≤ slice.kernelLength g)
variable (hsmallG : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / slice.kernelLength g) < 1)
variable (hsize : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  ∀ p : B a.val × Fin (layerSamplerDegree I n a.val), q ≤ slice.principalLength ⟨a.val,p⟩)
variable (hsmall : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  ∀ p : B a.val × Fin (layerSamplerDegree I n a.val),
    scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / slice.principalLength ⟨a.val,p⟩) < 1)
variable (hε : 0 ≤ ε) (hmesh : (slice.step : ℝ) / S.value ≤ ε)
variable (hη : 0 < η)
variable (htail : |t| * polynomialMassC2Budget
  (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val))) m 1 ≤
  slicedPrincipalC2Tolerance
    (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      B a.val × Fin (layerSamplerDegree I n a.val)))
    (Fintype.card {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}) m 1
    (unitProfilePrincipalLowerBound B) (δ / 2) s.L η)

variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)
variable (htrimbase : slice.path.base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN))

variable {Pnative massLog capLog Edata Ptest : ℝ}
variable (data : ActualForecastData physicalN originalpoly Pnative massLog capLog Edata)
variable (hcenter : data.centerConstant = fun j => (slice.path.center j).val)
variable (hκ : s.κ = forecastGeometricJacobian (X := X) (I := I) U b R S.value (∏ a, (basisAxisScale (b ((allocatedShortIntegerSelection U b S.value) a).1) ((allocatedShortIntegerSelection U b S.value) a).2 : ℝ)) τ)
variable (hUniversal : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
  (hm : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ),
  ‖slice.targetAt (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb poly hm s.κ u -
    ∑ i, data.coefficient i * (data.twists i).eval physicalN
      (fun j => subtractConstant (data.centerConstant j) (poly j)) u‖ ≤ Real.exp (-Edata))
variable (hPtest : 0 ≤ Ptest) (hLw : (Lip : ℝ) ≤ Real.exp Ptest)
variable (hpw : periodCap ≤ Real.exp Ptest) (hcw : coverCap ≤ Real.exp Ptest)
variable {Eprec Rrank : ℝ} (hEprec : 0 ≤ Eprec)
variable (hlarge : ∀ i, Real.exp ((max (max s.P (2 * max Ptest (3 * Pnative + 3) + 1)) Eprec + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ (physicalN i : ℝ))
variable (hRrank : Real.exp ((max (max s.P (2 * max Ptest (3 * Pnative + 3) + 1)) Eprec + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ Rrank)
variable (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (physicalN i : ℝ))
  Rrank (U j) (originalpoly j))
variable (cutoff : ℕ) (hcutoff : 0 < cutoff)
variable {δgrid : ℝ} (hδgrid : 0 ≤ δgrid) (hδgrid1 : δgrid ≤ 1)
variable (hgridmesh : ∀ j, ((q * cutoff : ℕ) : ℝ) /
  forecastJointGridScale U b R S.value physicalN τ j ≤ δgrid)
variable (C : ℝ)
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
variable {sampleFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n}
variable {readFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  AllocatedActualCoefficientIndex G X I Eout n B → ℤ}
variable (hglobal : AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ
  originalpoly hmem (allocatedShortAxis (I := I) U b S.value) spatial kernel block C
  center slice.path.center slice.path.base sampleFn readFn)
variable (hz : allocatedCenteredJointDensity B U b hb o hR hσ S originalpoly hmem
  center slice.path.base slice.path.noise ≠ 0)
variable (hsampleAt : sampleFn slice.path.noise = slice.path.sample)
variable (hreadAt : readFn slice.path.noise = slice.path.read)

include hR hσ hdegree hξ hbox hframe ht hσbound hδ hδone hdense hperiod hcover hqN
  hsizeG hsmallG hsize hsmall hε hmesh hη htail ν hlattice hcompact hmargin htrimbase
  hcenter hκ hUniversal hPtest hLw hpw hcw hEprec hlarge hRrank hrank hcutoff hδgrid
  hδgrid1 hgridmesh hglobal hz hsampleAt hreadAt in

theorem native_ambient_comparison_actualForecastData :
    ‖slice.nativeMean s W originalpoly -
      (𝔼 u ∈ integerBox physicalN,
        W.eval physicalN (slice.path.physicalPolynomial originalpoly) u *
          slice.rawTarget (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb s.κ
            (slice.path.physicalPolynomial originalpoly)
            (slice.path.physicalPolynomial_mem originalpoly hmem) u)‖ ≤
      slice.comparisonError (Lip := Lip) (ξ := ξ) (t := t) (δ := δ) (ε := ε) (η := η) (q := q)
        (hδ := hδ) (o := o) (δnative := Real.exp (-Edata)) (M := Real.exp massLog)
        (Eprec := Eprec) (cutoff := cutoff) (δgrid := δgrid) := by
  have hV : 0 < (∏ a, (basisAxisScale (b ((allocatedShortIntegerSelection U b S.value) a).1) ((allocatedShortIntegerSelection U b S.value) a).2 : ℝ)) := by
    apply Finset.prod_pos
    intro a _
    exact_mod_cast basisAxisScale_pos (b ((allocatedShortIntegerSelection U b S.value) a).1) ((allocatedShortIntegerSelection U b S.value) a).2
  have hPa : 0 ≤ (max s.P (2 * max Ptest (3 * Pnative + 3) + 1)) := (by linarith [s.hP] : (0 : ℝ) ≤ s.P).trans (le_max_left _ _)
  have hbds := data.native_product_bounds W hPtest hLw hpw hcw
  have hLip := data.native_product_lipschitz_bound W hPtest hLw hcw
  have hexp : Real.exp (2 * max Ptest (3 * Pnative + 3) + 1) ≤ Real.exp (max s.P (2 * max Ptest (3 * Pnative + 3) + 1)) :=
    Real.exp_le_exp.mpr (le_max_right _ _)
  have happ := slice.rawTarget_actualForecastData_approx (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb
    originalpoly data hcenter s.κ hUniversal
  have hcomp := slice.native_ambient_comparison
    (s := s) (hb := hb) (o := o) (bW := bW) (W := W) (originalpoly := originalpoly)
    (hmem := hmem) (hdegree := hdegree) (ξ := ξ) (hξ := hξ) (hbox := hbox)
    (hframe := hframe) (ht := ht) (hσbound := hσbound) (hδ := hδ) (hδone := hδone)
    (hdense := hdense) (q := q) (hperiod := hperiod) (hcover := hcover) (hqN := hqN)
    (hsizeG := hsizeG) (hsmallG := hsmallG) (hsize := hsize) (hsmall := hsmall)
    (hε := hε) (hmesh := hmesh) (hη := hη) (htail := htail)
    (gridVolume := (∏ a, (basisAxisScale (b ((allocatedShortIntegerSelection U b S.value) a).1) ((allocatedShortIntegerSelection U b S.value) a).2 : ℝ))) (hVpos := hV) (ν := ν) (hmargin := hmargin)
    (htrimbase := htrimbase) (F := data.twists) (nativeCoeff := data.coefficient)
    (δnative := Real.exp (-Edata)) (happrox := by simpa only [rawTarget, hκ] using happ)
    (hPambient := hPa) (hEprec := hEprec) (hPP := le_max_left _ _)
    (hLip := hLip.trans hexp) (hcoverF := fun i => (hbds i).2.1.trans hexp)
    (hmodF := fun i => (hbds i).2.2.trans hexp) (hmass := data.mass)
    (hlarge := hlarge) (hRrank := hRrank) (hrank := hrank) (cutoff := cutoff)
    (hcutoff := hcutoff) (hδgrid := hδgrid) (hδgrid1 := hδgrid1) (hgridmesh := hgridmesh)
    (C := C) (hglobal := hglobal) (hz := hz) (hsampleAt := hsampleAt) (hreadAt := hreadAt)
  simpa only [rawTarget, hκ] using hcomp

variable (hfinite : (integerBox physicalN).Nonempty)
variable (htarget : data.target = slice.target (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb originalpoly hmem s.κ)

include hR hσ hdegree hξ hbox hframe ht hσbound hδ hδone hdense hperiod hcover hqN
  hsizeG hsmallG hsize hsmall hε hmesh hη htail ν hlattice hcompact hmargin htrimbase
  hcenter hκ hUniversal hPtest hLw hpw hcw hEprec hlarge hRrank hrank hcutoff hδgrid
  hδgrid1 hgridmesh hglobal hz hsampleAt hreadAt hfinite htarget in

theorem native_ambient_model_comparison :
    ‖slice.nativeMean s W originalpoly -
      (FiniteProbabilityWeights.uniformFinset (integerBox physicalN) hfinite).complexMean
        (fun u => W.eval physicalN
          (fun j => subtractConstant (data.centerConstant j) (originalpoly j)) u.val * data.target u)‖ ≤
      slice.comparisonError (Lip := Lip) (ξ := ξ) (t := t) (δ := δ) (ε := ε) (η := η) (q := q)
        (hδ := hδ) (o := o) (δnative := Real.exp (-Edata)) (M := Real.exp massLog)
        (Eprec := Eprec) (cutoff := cutoff) (δgrid := δgrid) := by
  have hc := slice.native_ambient_comparison_actualForecastData
    (s := s) (hb := hb) (o := o) (bW := bW) (W := W) (originalpoly := originalpoly)
    (hmem := hmem) (hdegree := hdegree) (ξ := ξ) (hξ := hξ) (hbox := hbox)
    (hframe := hframe) (ht := ht) (hσbound := hσbound) (hδ := hδ) (hδone := hδone)
    (hdense := hdense) (q := q) (hperiod := hperiod) (hcover := hcover) (hqN := hqN)
    (hsizeG := hsizeG) (hsmallG := hsmallG) (hsize := hsize) (hsmall := hsmall)
    (hε := hε) (hmesh := hmesh) (hη := hη) (htail := htail)
    (ν := ν) (hmargin := hmargin) (htrimbase := htrimbase)
    (data := data) (hcenter := hcenter) (hκ := hκ) (hUniversal := hUniversal)
    (hPtest := hPtest) (hLw := hLw) (hpw := hpw) (hcw := hcw)
    (hEprec := hEprec) (hlarge := hlarge) (hRrank := hRrank) (hrank := hrank)
    (cutoff := cutoff) (hcutoff := hcutoff) (hδgrid := hδgrid) (hδgrid1 := hδgrid1)
    (hgridmesh := hgridmesh) (C := C) (hglobal := hglobal) (hz := hz)
    (hsampleAt := hsampleAt) (hreadAt := hreadAt)
  have he := FiniteProbabilityWeights.uniformFinset_complexMean (integerBox physicalN) hfinite
    (fun u => W.eval physicalN (slice.path.physicalPolynomial originalpoly) u *
      slice.rawTarget (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb s.κ
        (slice.path.physicalPolynomial originalpoly)
        (slice.path.physicalPolynomial_mem originalpoly hmem) u)
  rw [← he] at hc
  have hfunctions :
      (fun u : integerBox physicalN => W.eval physicalN
        (fun j => subtractConstant (data.centerConstant j) (originalpoly j)) u.val * data.target u) =
      (fun u : integerBox physicalN => W.eval physicalN
        (slice.path.physicalPolynomial originalpoly) u.val *
        slice.rawTarget (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb s.κ
          (slice.path.physicalPolynomial originalpoly)
          (slice.path.physicalPolynomial_mem originalpoly hmem) u.val) := by
    funext u
    rw [hcenter, htarget]
    rfl
  rw [hfunctions]
  exact hc

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
