import OAI.Combinatorics.Progressions.Sampling.ForecastLawOriginalNativeHaarJointMean
import OAI.Combinatorics.Progressions.Sampling.ForecastLawPhysicalAmbientHaarComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} {X : Type} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Principal" => PrincipalIntegerTuples B degree Empty (allocatedPrincipalSides B U basis S)
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
local notation "selected" => allocatedShortIntegerSelection U basis S.value
variable (lowerSlice widthSlice : ∀ a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (xref : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout short)
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω → Sigma (AllocatedCongruenceRankOutput X Eout
    (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (gridVolume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {pw cw : ℝ} {Lw : ℝ≥0}
variable (Wtest : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable {Tgeo : Type*} [Fintype Tgeo]
variable (e : G ≃ X ⊕ (X ⊕ Tgeo)) (rootBudget rootLength : ℝ) (z : Option G × X → ℝ)
variable (lowerG widthG : G → ℝ)
variable (hwGne : ∀ g, widthG g ≠ 0)
variable (h0 : (fixedSpatialKernelBlock e rootBudget rootLength z false).det ≠ 0)
variable (h1 : (fixedSpatialKernelBlock e rootBudget rootLength z true).det ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
  4 ≤ Fintype.card (B a.val))
local notation "density" => fixedSpatialKernelSliceOriginalForecastDensity B U basis S e rootBudget
  rootLength z lowerG widthG h0 h1 hwGne hB lowerSlice widthSlice sample
local notation "κ" => ((forecastGeometricJacobian (X := X) (I := I) U basis R S.value gridVolume τ : ℝ) : ℂ)

include hR hσ ν hcompact hlattice in
theorem fixedSpatialSliceNativeAmbientMean_comparison
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    {δP : ℝ} (hδP : 0 < δP)
    (hwP : ∀ a p, δP ≤ widthSlice a p) (hlP : ∀ a p, 0 ≤ lowerSlice a p)
    (hwidthP : ∀ a p, |lowerSlice a p| + |widthSlice a p| ≤ 1)
    (hlG : ∀ g, 0 ≤ lowerG g) (hwG : ∀ g, 0 ≤ widthG g)
    (hcontainedG : ∀ g, lowerG g + widthG g ≤ 1)
    (hσ1 : ∀ a : AllocatedShortIntegerAxis U basis S.value, σ a.val.1 ≤ 1)
    (r : ℝ≥0) (hr : 0 < r) (hr3 : (3 : ℝ) ≤ r)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ r)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
      C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (hW : 0 ≤ rootBudget) (hL : 0 ≤ rootLength)
    (hsize : (Fintype.card G : ℝ) * rootLength ≤ rootBudget) (hz : ∀ a, |z a| ≤ 1)
    (hτ : 0 < τ) (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)
    (hbase : base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN))
    (q : ℕ) [NeZero q] (hq : q ∣ N) (hm : 0 < m)
    (hperiod : Wtest.modulus ∣ q) (hcover : Wtest.cover ∣ q) (hV : 0 < gridVolume)
    {Findex : Type} [Fintype Findex] {pf cf : ℝ} {Lf : ℝ≥0}
    (F : Findex → NormalizedPolynomialTwist X (Σ j, J j) pf cf Lf)
    (c : Findex → ℂ) (δ : ℝ)
    (happrox : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (hmem : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ),
      ‖κ * forecastLawDensityPhysicalTarget B U basis S law density selected sample xref
        active Y N gridVolume base physicalN τ o hb bW poly hmem u -
        ∑ i, c i * (F i).eval physicalN poly u‖ ≤ δ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
    (hmem : ∀ j d, coefficients (poly j) d ∈ U j)
    {P E Rrank M : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hX : (Fintype.card X : ℝ) ≤ P) (hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ P)
    (hLip : ((Lw * max 1 (Real.toNNReal cf) + Lf * max 1 (Real.toNNReal cw) : ℝ≥0) : ℝ) ≤ Real.exp P)
    (hcoverF : ∀ i, ((Wtest.cover * (F i).cover : ℕ) : ℝ) ≤ Real.exp P)
    (hmodF : ∀ i, ((Wtest.modulus * (F i).modulus : ℕ) : ℝ) ≤ Real.exp P)
    (hmass : ∑ i, ‖c i‖ ≤ M)
    (hlarge : ∀ i, Real.exp ((max P E + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ (physicalN i : ℝ))
    (hRrank : Real.exp ((max P E + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (physicalN i : ℝ))
      Rrank (U j) (poly j)) :
    ‖(𝔼 u ∈ integerBox physicalN, Wtest.eval physicalN poly u *
        (κ * forecastLawDensityPhysicalTarget B U basis S law density selected sample xref
          active Y N gridVolume base physicalN τ o hb bW poly hmem u)) -
      forecastJointOriginalGridMean U basis S.value hm law active
        (forecastInactiveFixedOutput B U basis S selected
          (allocatedOriginalSampleInactiveCoefficients B selected sample) xref)
        Y N q hq gridVolume density
        (Wtest.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
          (fun a => (base a : ℝ) / physicalN a) τ)
        (fun j => (forecastJointGridCenter U basis S.value base j : ℝ))
        (forecastJointGridScale U basis R S.value physicalN τ)‖ ≤
      2 * δ + M * Real.exp (-E) := by
  have hdensity := (fixedSpatialKernelSliceOriginalForecastDensity_bounds B U basis hR hσ S
    e rootBudget rootLength z lowerG widthG h0 h1 hwGne hB lowerSlice widthSlice
    hδP hwP hlP sample hs).2.continuous
  have hN (i : X) : 0 < physicalN i := by
    exact_mod_cast (Real.exp_pos _).trans_le (hlarge i)
  have hsupport := fixedSpatialKernelSliceOriginalForecastDensity_zero_of_norm_gt_two
    B U basis hR hσ S e rootBudget rootLength z lowerG widthG h0 h1 hwGne hB
    lowerSlice widthSlice hδP hwP hlP sample hs hwidthP hW hL hsize hz hlG hwG hcontainedG
  have hhaar := forecastLawNativeHaarMean_eq_jointMean B U basis S law density sample xref
    active Y N gridVolume base physicalN τ o hb bW Wtest ν hR hσ hs hσ1
    r hr hr3 hradius C hC hchart hbudget hdensity hsupport hN hτ hmargin hbase
    q hq hm hperiod hcover hV
  have h := forecastLawDensityPhysicalTarget_ambientHaarComparison B U basis S law density selected sample xref
    active Y N gridVolume base physicalN τ o hb bW ν hdensity.measurable Wtest F c κ δ
    (dvd_trans hcover hq) happrox poly hp hmem hP hE hX hdim hLip hcoverF hmodF hmass
    hlarge hRrank hrank
  simp_rw [mul_assoc, integral_const_mul] at h
  rw [← Finset.mul_expect, hhaar] at h
  exact h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} {X : Type} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Principal" => PrincipalIntegerTuples B degree Empty (allocatedPrincipalSides B U basis S)
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
local notation "selected" => allocatedShortIntegerSelection U basis S.value
variable (lowerSlice widthSlice : ∀ a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (xref : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout short)
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω → Sigma (AllocatedCongruenceRankOutput X Eout
    (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (gridVolume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {pw cw : ℝ} {Lw : ℝ≥0}
variable (Wtest : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable {Tgeo : Type*} [Fintype Tgeo]
variable (e : G ≃ X ⊕ (X ⊕ Tgeo)) (rootBudget rootLength : ℝ) (z : Option G × X → ℝ)
variable (lowerG widthG : G → ℝ)
variable (hwGne : ∀ g, widthG g ≠ 0)
variable (h0 : (fixedSpatialKernelBlock e rootBudget rootLength z false).det ≠ 0)
variable (h1 : (fixedSpatialKernelBlock e rootBudget rootLength z true).det ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
  4 ≤ Fintype.card (B a.val))
local notation "density" => fixedSpatialKernelSliceOriginalForecastDensity B U basis S e rootBudget
  rootLength z lowerG widthG h0 h1 hwGne hB lowerSlice widthSlice sample
local notation "κ" => ((forecastGeometricJacobian (X := X) (I := I) U basis R S.value gridVolume τ : ℝ) : ℂ)

include hR hσ ν hcompact hlattice in
theorem fixedSpatialSliceNativeAmbientRationalMean_comparison
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    {δP : ℝ} (hδP : 0 < δP)
    (hwP : ∀ a p, δP ≤ widthSlice a p) (hlP : ∀ a p, 0 ≤ lowerSlice a p)
    (hwidthP : ∀ a p, |lowerSlice a p| + |widthSlice a p| ≤ 1)
    (hlG : ∀ g, 0 ≤ lowerG g) (hwG : ∀ g, 0 ≤ widthG g)
    (hcontainedG : ∀ g, lowerG g + widthG g ≤ 1)
    (hσ1 : ∀ a : AllocatedShortIntegerAxis U basis S.value, σ a.val.1 ≤ 1)
    (r : ℝ≥0) (hr : 0 < r) (hr3 : (3 : ℝ) ≤ r)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ r)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
      C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (hW : 0 ≤ rootBudget) (hL : 0 ≤ rootLength)
    (hsize : (Fintype.card G : ℝ) * rootLength ≤ rootBudget) (hz : ∀ a, |z a| ≤ 1)
    (hτ : 0 < τ) (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)
    (hbase : base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN))
    (q : ℕ) [NeZero q] (hq : q ∣ N) (hm : 0 < m)
    (hperiod : Wtest.modulus ∣ q) (hcover : Wtest.cover ∣ q) (hV : 0 < gridVolume)
    {Findex : Type} [Fintype Findex] {pf cf : ℝ} {Lf : ℝ≥0}
    (F : Findex → NormalizedPolynomialTwist X (Σ j, J j) pf cf Lf)
    (c : Findex → ℂ) (δ : ℝ)
    (happrox : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (hmem : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ),
      ‖κ * forecastLawDensityPhysicalTarget B U basis S law density selected sample xref
        active Y N gridVolume base physicalN τ o hb bW poly hmem u -
        ∑ i, c i * (F i).eval physicalN poly u‖ ≤ δ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
    (hmem : ∀ j d, coefficients (poly j) d ∈ U j)
    {P E Rrank M : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hX : (Fintype.card X : ℝ) ≤ P) (hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ P)
    (hLip : ((Lw * max 1 (Real.toNNReal cf) + Lf * max 1 (Real.toNNReal cw) : ℝ≥0) : ℝ) ≤ Real.exp P)
    (hcoverF : ∀ i, ((Wtest.cover * (F i).cover : ℕ) : ℝ) ≤ Real.exp P)
    (hmodF : ∀ i, ((Wtest.modulus * (F i).modulus : ℕ) : ℝ) ≤ Real.exp P)
    (hmass : ∑ i, ‖c i‖ ≤ M)
    (hlarge : ∀ i, Real.exp ((max P E + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ (physicalN i : ℝ))
    (hRrank : Real.exp ((max P E + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (physicalN i : ℝ))
      Rrank (U j) (poly j))
    (cutoff : ℕ) (hcutoff : 0 < cutoff)
    {D Pdecay δgrid : ℝ} (hD : 0 ≤ D)
    (hPdecay : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ Pdecay)
    (hdecay : ∀ i (χ : AddChar (Out → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-Pdecay))
    (hδgrid : 0 ≤ δgrid) (hδgrid1 : δgrid ≤ 1)
    (hmesh : ∀ j, ((q * cutoff : ℕ) : ℝ) /
      forecastJointGridScale U basis R S.value physicalN τ j ≤ δgrid) :
    let frame := fixedSpatialKernelSliceFrame rootBudget rootLength z lowerG widthG
    let h0slice := fixedSpatialKernelBlock_slice_det_ne_zero e rootBudget rootLength z
      lowerG widthG false h0 hwGne
    let h1slice := fixedSpatialKernelBlock_slice_det_ne_zero e rootBudget rootLength z
      lowerG widthG true h1 hwGne
    let Cgrid := fixedSpatialOriginalForecastCap B
      (fixedSpatialKernelBlockEquiv e rootBudget rootLength frame true h1slice) hδP
    let Lgrid := fixedSpatialOriginalForecastLip B
      (fixedSpatialKernelBlockEquiv e rootBudget rootLength frame false h0slice)
      (fixedSpatialKernelBlockEquiv e rootBudget rootLength frame true h1slice) hδP
    let Kgrid := Lw * max ‖τ / 8‖₊ (forecastNativeAmbientLip U basis o R)
    let grid := forecastInactiveFixedOutput B U basis S selected
      (allocatedOriginalSampleInactiveCoefficients B selected sample) xref
    let test := Wtest.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
      (fun a => (base a : ℝ) / physicalN a) τ
    ‖(𝔼 u ∈ integerBox physicalN, Wtest.eval physicalN poly u *
        (κ * forecastLawDensityPhysicalTarget B U basis S law density selected sample xref
          active Y N gridVolume base physicalN τ o hb bW poly hmem u)) -
      (∑' g, 𝔼 r : Out → ZMod N,
        ((rationalInactiveForecast law active grid Y N gridVolume g r / gridVolume : ℝ) : ℂ) *
          ∫ y, test g (fun a => ZMod.castHom hq (ZMod q) (r a)) y
            ∂realDensityMeasure volume density)‖ ≤
      (2 * δ + M * Real.exp (-E)) +
        forecastJointGridError (Fintype.card Out)
          (Fintype.card (X ⊕ AllocatedActiveIntegerAxis U basis S.value))
          (Fintype.card (Σ j, I j)) cutoff D Lgrid Cgrid Kgrid δgrid := by
  intro frame h0slice h1slice Cgrid Lgrid Kgrid grid test
  have hamb := fixedSpatialSliceNativeAmbientMean_comparison B U basis hR hσ S law
    lowerSlice widthSlice sample xref active Y N gridVolume base physicalN τ o hb bW
    Wtest ν e rootBudget rootLength z lowerG widthG hwGne h0 h1 hB
    hs hδP hwP hlP hwidthP hlG hwG hcontainedG hσ1 r hr hr3 hradius
    C hC hchart hbudget hW hL hsize hz hτ hmargin hbase q hq hm hperiod hcover hV
    F c δ happrox poly hp hmem hP hE hX hdim hLip hcoverF hmodF hmass
    hlarge hRrank hrank
  have hN (i : X) : 0 < physicalN i := by
    exact_mod_cast (Real.exp_pos _).trans_le (hlarge i)
  have hgrid := fixedSpatialSliceNativeJointGridMean_comparison B U basis hR hσ S
    hb o bW Wtest e rootBudget rootLength z h0 h1 lowerG widthG hwGne
    hlG hwG hcontainedG hB lowerSlice widthSlice hδP hwP hlP hwidthP
    hW hL hsize hz sample hs hm τ base physicalN xref law active Y N q hq hperiod hcover
    gridVolume hV.ne' (fun j => (forecastJointGridCenter U basis S.value base j : ℝ))
    (forecastJointGridScale U basis R S.value physicalN τ)
    (forecastJointGridScale_pos U basis hR S.value physicalN hN hτ)
    cutoff hcutoff hD hPdecay hdecay hδgrid hδgrid1 hmesh
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hamb hgrid)

end Erdos3.VectorPolynomial

end

end OAI
