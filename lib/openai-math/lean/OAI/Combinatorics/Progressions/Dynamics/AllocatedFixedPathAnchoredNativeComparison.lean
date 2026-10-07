import OAI.Combinatorics.Progressions.Geometry.AllocatedRecoveredSampleSiteChart
import OAI.Combinatorics.Progressions.Lattices.AllocatedSlicedPhysicalResidueIdentity
import OAI.Combinatorics.Progressions.Probability.AllocatedFixedPathSlicedPhysicalDensityComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {T : Type*} [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)
local notation "Domain" => (Spatial × (Output → ℝ))
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)
local notation "ShortTuple" => PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)

local notation "sides" => allocatedPrincipalSides B U basis S
local notation "hSides" => allocatedPrincipalSides_pos B U basis S
local notation "FullInput" => PrincipalTupleIndex B degree
local notation "Original" => PrincipalIntegerTuples B degree Empty sides

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]
local notation "N" => (∏ l, primes l ^ exponent l)
local instance fixedPathNativeCRTModulusNeZero : NeZero N :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (primes l)))⟩
local notation "Long" => LayerSamplerLongVariables short G B
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)

variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
local notation "selected" => allocatedShortIntegerSelection U basis S.value
local notation "Grid" => AllocatedShortIntegerAxis U basis S.value →
  ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ

include hR hσ in
theorem allocatedFixedPath_native_test_eq_eval
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (base : X → ℤ) (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (box : X → ℕ) (hbox : ∀ a, 0 < box a) {τ : ℝ} (hτ : τ ≠ 0)
    (q : ℕ) [NeZero q] (hm : 0 < m) (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (nativePoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j a, coefficients (nativePoly j) a ∈ U j)
    (x : G → IntegerScalarCubeBox Empty S.value) (v : Original)
    (hchart : let _ : NeZero W.cover := ⟨W.cover_pos.ne'⟩
      ∀ j, physicalSingleSiteValue U W.cover nativePoly hmem
        (fun a => ((base a + integerPhysicalSite
          (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x v) integerFrame a : ℤ) : ℝ)) j () =
        normalizedCoveredChart (euclideanSubspace (U j)) (basis j) (hb j) (bW j) W.cover
          (orthonormalMixedChart (o j) (allocatedOriginalSamplePhysicalMixedValue B U basis S sample x v j),
            integerResidueMap (E j) W.cover (allocatedOriginalSampleDeckValue B U basis S deck x v j))) :
    W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
      (fun a => (base a : ℝ) / box a) τ
      (forecastInactiveShortGrid B U basis S selected
        (allocatedOriginalSampleInactiveCoefficients B selected sample) (principalAxisRestrict short v))
      (allocatedJointResidueOutput B U basis S base integerFrame deck
        (allocatedOriginalSampleCongruenceProjection B U basis S sample) q
        (fun g => ((x g none : ℤ) : ZMod q)) (principalResidueLabel q v))
      ((fun a : Σ _ : X, Unit ⊕ Empty =>
          (integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x v)
            integerFrame a.1 : ℝ) / (τ * (box a.1 : ℝ) / 8)),
        allocatedOriginalSampleFullSliceMap B U basis S x (principalAxisRestrict short v)
          (fun _ _ => 0) (fun _ _ => 1) sample
          (fun j => (((principalAxisRestrict (fun a => ¬short a) v) j none : ℤ) : ℝ) / S.value)) =
      W.eval box nativePoly (fun a => base a + integerPhysicalSite
        (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x v) integerFrame a) := by
  have hfull := allocatedOriginalSampleFullSliceMap_physical B U basis S sample x v
  change allocatedOriginalSampleFullSliceMap B U basis S x (principalAxisRestrict short v)
    (fun _ _ => 0) (fun _ _ => 1) sample
    (fun j => (((principalAxisRestrict (fun a => ¬short a) v) j none : ℤ) : ℝ) / S.value) = _ at hfull
  rw [allocatedOriginalSample_jointResidueOutput_eq_congruence, hfull]
  have hsite : base + integerPhysicalSite
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x v) integerFrame =
        fun a => base a + integerPhysicalSite
          (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x v) integerFrame a := rfl
  rw [hsite]
  simpa only [Int.cast_add, add_sub_cancel_left] using
    W.forecastShortGridTest_originalSample_eq_eval U basis hb o bW R B S hR hσ sample hs x v
      q hm hperiod hcover base
      (fun a => base a + integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x v) integerFrame a)
      box hbox hτ (allocatedOriginalSampleDeckValue B U basis S deck x v) nativePoly hmem hchart

include hR hσ in
theorem allocatedFixedPath_native_rational_density_comparison
    (τ ξ : ℝ) (hτ : 0 < τ) (hξ : 0 < ξ) (box : X → ℕ) (hbox : ∀ x, 0 < box x)
    (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hframe : integerFrame ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := FullInput) budget τ ξ box) 1)
    (e : G ≃ X ⊕ (X ⊕ T))
    (h0 : (fixedSpatialKernelBlock e budget (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) false).det ≠ 0)
    (h1 : (fixedSpatialKernelBlock e budget (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) true).det ≠ 0)
    (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    {t : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
    (b : ∀ a : Active, B a.val) {η : ℝ} (hη : 0 < η)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (htail : |t| * polynomialMassC2Budget (Fintype.card Input) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card Input) (Fintype.card Active) m 1
        (unitProfilePrincipalLowerBound B) (1 / 2) A η)
    (hS : 2 ≤ S.value) (q : ℕ) [NeZero q] (hsize : q ≤ S.value)
    (hsmall : scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / S.value) < 1)
    (hm : 0 < m) (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (xref : G → IntegerScalarCubeBox Empty S.value)
    (base : X → ℤ)
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (nativePoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j a, coefficients (nativePoly j) a ∈ U j)
    (hchart : let _ : NeZero W.cover := ⟨W.cover_pos.ne'⟩
      ∀ (x : G → IntegerScalarCubeBox Empty S.value) (v : Original) j,
        physicalSingleSiteValue U W.cover nativePoly hmem
          (fun a => ((base a + integerPhysicalSite
            (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x v) integerFrame a : ℤ) : ℝ)) j () =
          normalizedCoveredChart (euclideanSubspace (U j)) (basis j) (hb j) (bW j) W.cover
            (orthonormalMixedChart (o j) (allocatedOriginalSamplePhysicalMixedValue B U basis S sample x v j),
              integerResidueMap (E j) W.cover (allocatedOriginalSampleDeckValue B U basis S deck x v j)))
    (hp : ∀ l, (primes l).Prime) (hinj : Function.Injective primes)
    (hcoprime : Pairwise (fun l k => (primes l ^ exponent l).Coprime (primes k ^ exponent k)))
    (origin : ∀ l, Long → ZMod (primes l ^ exponent l))
    (hqN : q ∣ N) {gridVolume : ℝ} (hV : gridVolume ≠ 0) :
    let c := fun a => (sample (selected a).1).2 (selected a).2
    let projection := allocatedOriginalSampleCongruenceProjection B U basis S sample
    let poly := allocatedForecastPolynomial short base integerFrame deck projection
    let lower := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) => (0 : ℝ)
    let width := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) =>
      ((S.value : ℝ) - 1) / S.value
    let Kφ := Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U basis o R)
    let K := Kφ * allocatedOriginalSampleFullSliceLip B U basis S t
    let kernel := FiniteProbabilityWeights.pi (fun _ : G => integerScalarCubeWeights Empty S.value S.positive)
    let law := principalTupleWeights (α := Empty) B degree sides hSides
    let density := fixedSpatialKernelOriginalForecastDensity B U basis S e budget
      (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) h0 h1 hB lower width sample
    ‖kernel.complexMean (fun x => law.complexMean (fun v =>
        W.eval box nativePoly (fun a => base a + integerPhysicalSite
          (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x v) integerFrame a))) -
      (∑' grid, 𝔼 residue : Out → ZMod N,
        ((rationalInactiveForecast law
          (fun _ => crtPolynomialInputLaw primes exponent (fun _ => 0) hcoprime origin)
          (forecastInactiveFixedOutput B U basis S selected c xref)
          (fun v => integerLongPolynomialOutput poly (fun k => (v k.1 k.2 : ℤ)) N)
          N gridVolume grid residue / gridVolume : ℝ) : ℂ) *
          ∫ y, W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
            (fun a => (base a : ℝ) / box a) τ grid
            (fun j => ZMod.castHom hqN (ZMod q) (residue j)) y
            ∂realDensityMeasure volume density)‖ ≤
      ((Fintype.card Input : ℝ) * ((q : ℝ) / S.value) +
        (2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
          ∑ _j : Input, (q : ℝ) / S.value + K * (1 / S.value)) + 2 * η)) +
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + Kφ)) *
        (Fintype.card G * ((q : ℝ) / S.value)) + (Kφ : ℝ) * ξ := by
  classical
  intro c projection poly lower width Kφ K kernel law density
  have htest := W.forecastShortGridTest_bounds U basis S.value hb o bW R q hm hperiod hcover
    (fun a => (base a : ℝ) / box a) τ
  have he := allocatedFixedPath_physical_rational_density_comparison B U basis hR hσ S primes exponent
    τ ξ hτ hξ box hbox integerFrame hframe e h0 h1 hB sample hs
    ht hσbound b hη A hA htail hS q hsize hsmall selected
    (allocatedShortIntegerSelection_small U basis S.value) xref base deck projection
    hp hinj hcoprime origin hqN hV
    (W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
      (fun a => (base a : ℝ) / box a) τ)
    (fun grid residue => (htest grid residue).2) (fun grid residue => (htest grid residue).1)
  have hid (x : G → IntegerScalarCubeBox Empty S.value) (v : Original) :=
    allocatedFixedPath_native_test_eq_eval B U basis hR hσ S hb o bW W sample hs
      base integerFrame deck box hbox hτ.ne' q hm hperiod hcover nativePoly hmem x v (hchart x v)
  let F := fun (x : G → IntegerScalarCubeBox Empty S.value) (v : Original) =>
    W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
      (fun a => (base a : ℝ) / box a) τ
      (forecastInactiveShortGrid B U basis S selected c (principalAxisRestrict short v))
      (allocatedJointResidueOutput B U basis S base integerFrame deck projection q
        (fun g => ((x g none : ℤ) : ZMod q)) (principalResidueLabel q v))
      ((fun a : Σ _ : X, Unit ⊕ Empty =>
          (integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x v)
            integerFrame a.1 : ℝ) / (τ * (box a.1 : ℝ) / 8)),
        allocatedOriginalSampleFullSliceMap B U basis S x (principalAxisRestrict short v)
          (fun _ _ => 0) (fun _ _ => 1) sample
          (fun j => (((principalAxisRestrict (fun a => ¬short a) v) j none : ℤ) : ℝ) / S.value))
  have hF : F = fun x v => W.eval box nativePoly (fun a => base a + integerPhysicalSite
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x v) integerFrame a) := by
    funext x v
    exact hid x v
  change ‖kernel.complexMean (fun x => law.complexMean (F x)) - _‖ ≤ _ at he
  rw [hF] at he
  exact he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {T : Type*} [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)
local notation "Domain" => (Spatial × (Output → ℝ))
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)
local notation "ShortTuple" => PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)

local notation "sides" => allocatedPrincipalSides B U basis S
local notation "hSides" => allocatedPrincipalSides_pos B U basis S
local notation "FullInput" => PrincipalTupleIndex B degree
local notation "Original" => PrincipalIntegerTuples B degree Empty sides

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]
local notation "N" => (∏ l, primes l ^ exponent l)
local instance fixedPathRecoveredNativeCRTModulusNeZero : NeZero N :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (primes l)))⟩
local notation "Long" => LayerSamplerLongVariables short G B
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)

variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
local notation "selected" => allocatedShortIntegerSelection U basis S.value
local notation "Grid" => AllocatedShortIntegerAxis U basis S.value →
  ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ

local instance fixedPathRecoveredNativeCoverNeZero : NeZero W.cover := ⟨W.cover_pos.ne'⟩

include hR hσ in
theorem allocatedFixedPath_recovered_native_rational_density_comparison
    (τ ξ : ℝ) (hτ : 0 < τ) (hξ : 0 < ξ) (box : X → ℕ) (hbox : ∀ x, 0 < box x)
    (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hframe : integerFrame ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := FullInput) budget τ ξ box) 1)
    (e : G ≃ X ⊕ (X ⊕ T))
    (h0 : (fixedSpatialKernelBlock e budget (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) false).det ≠ 0)
    (h1 : (fixedSpatialKernelBlock e budget (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) true).det ≠ 0)
    (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    {t : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
    (b : ∀ a : Active, B a.val) {η : ℝ} (hη : 0 < η)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (htail : |t| * polynomialMassC2Budget (Fintype.card Input) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card Input) (Fintype.card Active) m 1
        (unitProfilePrincipalLowerBound B) (1 / 2) A η)
    (hS : 2 ≤ S.value) (q : ℕ) [NeZero q] (hsize : q ≤ S.value)
    (hsmall : scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / S.value) < 1)
    (hm : 0 < m) (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (xref : G → IntegerScalarCubeBox Empty S.value)
    (base : X → ℤ)
    (nativePoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j a, coefficients (nativePoly j) a ∈ U j)
    (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (nativePoly j))
    (hbase : canonicalCoefficientSample U basis hb o sample =
      affineSampleCoefficientTorus U nativePoly hmem
        (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base +
          integerFrame) (k, x) : ℝ)))
    (hsmallChart : ∀ a, |coefficientSamplerAmbientPoint U basis o sample a| < 1 / 2)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hread : ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E W.cover → Prop,
      coefficientDeckChartEvent U bW basis hb o W.cover event
        (affineCoefficientCoverSample U nativePoly hmem W.cover
          (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base +
            integerFrame) (k, x) : ℝ))) ↔
        event (allocatedReadCoefficientChartResidues (fun i => (read i : ZMod W.cover))))
    (hp : ∀ l, (primes l).Prime) (hinj : Function.Injective primes)
    (hcoprime : Pairwise (fun l k => (primes l ^ exponent l).Coprime (primes k ^ exponent k)))
    (origin : ∀ l, Long → ZMod (primes l ^ exponent l))
    (hqN : q ∣ N) {gridVolume : ℝ} (hV : gridVolume ≠ 0) :
    let c := fun a => (sample (selected a).1).2 (selected a).2
    let projection := allocatedOriginalSampleCongruenceProjection B U basis S sample
    let poly := allocatedForecastPolynomial short base integerFrame (allocatedReadDeck read) projection
    let lower := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) => (0 : ℝ)
    let width := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) =>
      ((S.value : ℝ) - 1) / S.value
    let Kφ := Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U basis o R)
    let K := Kφ * allocatedOriginalSampleFullSliceLip B U basis S t
    let kernel := FiniteProbabilityWeights.pi (fun _ : G => integerScalarCubeWeights Empty S.value S.positive)
    let law := principalTupleWeights (α := Empty) B degree sides hSides
    let density := fixedSpatialKernelOriginalForecastDensity B U basis S e budget
      (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) h0 h1 hB lower width sample
    ‖kernel.complexMean (fun x => law.complexMean (fun v =>
        W.eval box nativePoly (fun a => base a + integerPhysicalSite
          (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x v) integerFrame a))) -
      (∑' grid, 𝔼 residue : Out → ZMod N,
        ((rationalInactiveForecast law
          (fun _ => crtPolynomialInputLaw primes exponent (fun _ => 0) hcoprime origin)
          (forecastInactiveFixedOutput B U basis S selected c xref)
          (fun v => integerLongPolynomialOutput poly (fun k => (v k.1 k.2 : ℤ)) N)
          N gridVolume grid residue / gridVolume : ℝ) : ℂ) *
          ∫ y, W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
            (fun a => (base a : ℝ) / box a) τ grid
            (fun j => ZMod.castHom hqN (ZMod q) (residue j)) y
            ∂realDensityMeasure volume density)‖ ≤
      ((Fintype.card Input : ℝ) * ((q : ℝ) / S.value) +
        (2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
          ∑ _j : Input, (q : ℝ) / S.value + K * (1 / S.value)) + 2 * η)) +
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + Kφ)) *
        (Fintype.card G * ((q : ℝ) / S.value)) + (Kφ : ℝ) * ξ := by
  exact allocatedFixedPath_native_rational_density_comparison B U basis hR hσ S primes exponent
    hb o bW W τ ξ hτ hξ box hbox integerFrame hframe e h0 h1 hB sample hs
    ht hσbound b hη A hA htail hS q hsize hsmall hm hperiod hcover xref base
    (allocatedReadDeck read) nativePoly hmem
    (fun x v j => by
      simpa only [Pi.add_apply, Int.cast_add] using
        allocatedRecoveredSample_site_chart_base U B bW basis hb o S W.cover
          nativePoly hdegree hmem base integerFrame sample hbase hsmallChart read hread x v j)
    hp hinj hcoprime origin hqN hV

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {T : Type*} [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)
local notation "Domain" => (Spatial × (Output → ℝ))
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)
local notation "ShortTuple" => PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)

local notation "sides" => allocatedPrincipalSides B U basis S
local notation "hSides" => allocatedPrincipalSides_pos B U basis S
local notation "FullInput" => PrincipalTupleIndex B degree
local notation "Original" => PrincipalIntegerTuples B degree Empty sides

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
local notation "selected" => allocatedShortIntegerSelection U basis S.value
local notation "Grid" => AllocatedShortIntegerAxis U basis S.value →
  ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ

local instance slicedNativeAtomCoverNeZero : NeZero W.cover := ⟨W.cover_pos.ne'⟩

variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
  (allocatedLayerWidths B U basis S j)
  (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
variable (base : X → ℤ) (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (box : X → ℕ) (hbox : ∀ a, 0 < box a) {τ : ℝ} (hτ : τ ≠ 0)
variable (q : ℕ) [NeZero q] (hm : 0 < m)
variable (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (nativePoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j a, coefficients (nativePoly j) a ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (nativePoly j))
variable (hbase : canonicalCoefficientSample U basis hb o sample =
  affineSampleCoefficientTorus U nativePoly hmem
    (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base +
      integerFrame) (k, x) : ℝ)))
variable (hsmallChart : ∀ a, |coefficientSamplerAmbientPoint U basis o sample a| < 1 / 2)
variable (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
variable (hread : ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E W.cover → Prop,
  coefficientDeckChartEvent U bW basis hb o W.cover event
    (affineCoefficientCoverSample U nativePoly hmem W.cover
      (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base +
        integerFrame) (k, x) : ℝ))) ↔
    event (allocatedReadCoefficientChartResidues (fun i => (read i : ZMod W.cover))))

include hs hbox hτ hdegree hbase hsmallChart hread in

theorem allocatedFixedPath_recovered_physical_native_atom
    (x : G → IntegerScalarCubeBox Empty S.value) (v : Original) :
    W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
      (fun a => (base a : ℝ) / box a) τ
      (forecastInactiveShortGrid B U basis S selected
        (allocatedOriginalSampleInactiveCoefficients B selected sample) (principalAxisRestrict short v))
      (allocatedJointResidueOutput B U basis S base integerFrame (allocatedReadDeck read)
        (allocatedOriginalSampleCongruenceProjection B U basis S sample) q
        (fun g => ((x g none : ℤ) : ZMod q)) (principalResidueLabel q v))
      ((fun a : Σ _ : X, Unit ⊕ Empty =>
          (integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x v)
            integerFrame a.1 : ℝ) / (τ * (box a.1 : ℝ) / 8)),
        fun a : Output => allocatedFullMixedSiteValue (R := R) U basis
          (allocatedOriginalSamplePhysicalMixedValue B U basis S sample x v) a.1.val) =
      W.eval box nativePoly (fun a => base a + integerPhysicalSite
        (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x v) integerFrame a) := by
  rw [allocatedOriginalSample_jointResidueOutput_eq_congruence]
  have hsite : base + integerPhysicalSite
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x v) integerFrame =
        fun a => base a + integerPhysicalSite
          (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x v) integerFrame a := rfl
  rw [hsite]
  have hc j := allocatedRecoveredSample_site_chart_base U B bW basis hb o S W.cover
    nativePoly hdegree hmem base integerFrame sample hbase hsmallChart read hread x v j
  simpa only [Pi.add_apply, Int.cast_add, add_sub_cancel_left] using
    W.forecastShortGridTest_originalSample_eq_eval U basis hb o bW R B S hR hσ sample hs x v
      q hm hperiod hcover base
      (fun a => base a + integerPhysicalSite
        (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x v) integerFrame a)
      box hbox hτ (allocatedOriginalSampleDeckValue B U basis S (allocatedReadDeck read) x v)
      nativePoly hmem (fun j => by simpa only [Pi.add_apply, Int.cast_add] using hc j)

include hs hbox hτ hdegree hbase hsmallChart hread in

theorem allocatedFixedPath_sliced_recovered_native_atom
    (HG : G → ℕ) (hHG : ∀ g, 0 < HG g) (cG : G → ℤ) (stepG : ℕ)
    (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (step H : Input → ℕ) (c : Input → ℤ) (hH : ∀ j, 0 < H j)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (u : ShortTuple)
    (x : ∀ g, IntegerScalarCubeBox Empty (HG g))
    (hx : (FiniteProbabilityWeights.pi
      (fun g => integerScalarCubeWeights Empty (HG g) (hHG g))).weight x ≠ 0)
    (v : ∀ j, IntegerScalarCubeBox Empty (H j))
    (hv : (FiniteProbabilityWeights.pi
      (fun j => integerScalarCubeWeights Empty (H j) (hH j))).weight v ≠ 0) :
    let embed := fun g => containedProgressionCubeMap Empty S.value (HG g) stepG (cG g)
      S.positive (hcontainedG g) (x g)
    let joined := principalAxisJoin short u (allocatedActiveContainedProgression B U basis S step H c hsubset v)
    W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
      (fun a => (base a : ℝ) / box a) τ
      (forecastInactiveShortGrid B U basis S selected
        (allocatedOriginalSampleInactiveCoefficients B selected sample) u)
      (allocatedJointResidueOutput B U basis S base integerFrame (allocatedReadDeck read)
        (allocatedOriginalSampleCongruenceProjection B U basis S sample) q
        (fun g => ((cG g + (stepG : ℤ) * (x g none : ℤ) : ℤ) : ZMod q))
        (allocatedPrincipalResidueJoin B U basis S q u
          (fun j => ((c j + (step j : ℤ) * (v j none : ℤ) : ℤ) : ZMod q))))
      ((fun a : Σ _ : X, Unit ⊕ Empty =>
          (integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) embed joined)
            integerFrame a.1 : ℝ) / (τ * (box a.1 : ℝ) / 8)),
        fun a : Output => allocatedFullMixedSiteValue (R := R) U basis
          (allocatedOriginalSamplePhysicalMixedValue B U basis S sample embed joined) a.1.val) =
      W.eval box nativePoly (fun a => base a + integerPhysicalSite
        (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) embed joined) integerFrame a) := by
  intro embed joined
  have he := allocatedFixedPath_recovered_physical_native_atom B U basis hR hσ S hb o bW W
    sample hs base integerFrame box hbox hτ q hm hperiod hcover nativePoly hmem hdegree
    hbase hsmallChart read hread embed joined
  dsimp only [embed, joined] at he
  rw [principalAxisRestrict_join_left,
    containedProgressionCubePi_residue S.value S.positive HG (fun _ => stepG) cG hHG
      hcontainedG x hx q,
    allocatedActiveContainedProgression_residue_join B U basis S step H c hH hsubset v hv q u] at he
  exact he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {T : Type*} [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)
local notation "Domain" => (Spatial × (Output → ℝ))
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)
local notation "ShortTuple" => PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)

local notation "sides" => allocatedPrincipalSides B U basis S
local notation "hSides" => allocatedPrincipalSides_pos B U basis S
local notation "FullInput" => PrincipalTupleIndex B degree
local notation "Original" => PrincipalIntegerTuples B degree Empty sides

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]
local notation "N" => (∏ l, primes l ^ exponent l)
local instance fixedPathAnchoredNativeCRTModulusNeZero : NeZero N :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (primes l)))⟩
local notation "Long" => LayerSamplerLongVariables short G B
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)

variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
local notation "selected" => allocatedShortIntegerSelection U basis S.value
local notation "Grid" => AllocatedShortIntegerAxis U basis S.value →
  ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ

local instance fixedPathAnchoredNativeCoverNeZero : NeZero W.cover := ⟨W.cover_pos.ne'⟩

include hR hσ in
theorem allocatedFixedPath_anchored_native_rational_density_comparison
    (τ ξ : ℝ) (hτ : 0 < τ) (hξ : 0 < ξ) (box : X → ℕ) (hbox : ∀ x, 0 < box x)
    (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hframe : integerFrame ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := FullInput) budget τ ξ box) 1)
    (e : G ≃ X ⊕ (X ⊕ T))
    (h0 : (fixedSpatialKernelBlock e budget (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) false).det ≠ 0)
    (h1 : (fixedSpatialKernelBlock e budget (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) true).det ≠ 0)
    (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    {t : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
    (b : ∀ a : Active, B a.val) {η : ℝ} (hη : 0 < η)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (htail : |t| * polynomialMassC2Budget (Fintype.card Input) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card Input) (Fintype.card Active) m 1
        (unitProfilePrincipalLowerBound B) (1 / 2) A η)
    (hS : 2 ≤ S.value) (q : ℕ) [NeZero q] (hsize : q ≤ S.value)
    (hsmall : scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / S.value) < 1)
    (hm : 0 < m) (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (xref : G → IntegerScalarCubeBox Empty S.value)
    (base : X → ℤ)
    (nativePoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j a, coefficients (nativePoly j) a ∈ U j)
    (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (nativePoly j))
    (hden : allocatedCoefficientDensity B U basis hb o hR hσ S
      (affineSampleCoefficientTorus U nativePoly hmem
        (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base +
          integerFrame) (k, x) : ℝ))) ≠ 0)
    (hp : ∀ l, (primes l).Prime) (hinj : Function.Injective primes)
    (hcoprime : Pairwise (fun l k => (primes l ^ exponent l).Coprime (primes k ^ exponent k)))
    (origin : ∀ l, Long → ZMod (primes l ^ exponent l))
    (hqN : q ∣ N) {gridVolume : ℝ} (hV : gridVolume ≠ 0) :
    let sample := allocatedAnchoredRecoveredSample B U bW basis hb o S hR hσ nativePoly hmem base integerFrame
    let read := allocatedAnchoredRecoveredRead B U bW basis hb o S hR hσ nativePoly hmem base integerFrame
    let c := fun a => (sample (selected a).1).2 (selected a).2
    let projection := allocatedOriginalSampleCongruenceProjection B U basis S sample
    let poly := allocatedForecastPolynomial short base integerFrame (allocatedReadDeck read) projection
    let lower := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) => (0 : ℝ)
    let width := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) =>
      ((S.value : ℝ) - 1) / S.value
    let Kφ := Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U basis o R)
    let K := Kφ * allocatedOriginalSampleFullSliceLip B U basis S t
    let kernel := FiniteProbabilityWeights.pi (fun _ : G => integerScalarCubeWeights Empty S.value S.positive)
    let law := principalTupleWeights (α := Empty) B degree sides hSides
    let density := fixedSpatialKernelOriginalForecastDensity B U basis S e budget
      (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) h0 h1 hB lower width sample
    ‖kernel.complexMean (fun x => law.complexMean (fun v =>
        W.eval box nativePoly (fun a => base a + integerPhysicalSite
          (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x v) integerFrame a))) -
      (∑' grid, 𝔼 residue : Out → ZMod N,
        ((rationalInactiveForecast law
          (fun _ => crtPolynomialInputLaw primes exponent (fun _ => 0) hcoprime origin)
          (forecastInactiveFixedOutput B U basis S selected c xref)
          (fun v => integerLongPolynomialOutput poly (fun k => (v k.1 k.2 : ℤ)) N)
          N gridVolume grid residue / gridVolume : ℝ) : ℂ) *
          ∫ y, W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
            (fun a => (base a : ℝ) / box a) τ grid
            (fun j => ZMod.castHom hqN (ZMod q) (residue j)) y
            ∂realDensityMeasure volume density)‖ ≤
      ((Fintype.card Input : ℝ) * ((q : ℝ) / S.value) +
        (2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
          ∑ _j : Input, (q : ℝ) / S.value + K * (1 / S.value)) + 2 * η)) +
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + Kφ)) *
        (Fintype.card G * ((q : ℝ) / S.value)) + (Kφ : ℝ) * ξ := by
  let sample := allocatedAnchoredRecoveredSample B U bW basis hb o S hR hσ nativePoly hmem base integerFrame
  let read := allocatedAnchoredRecoveredRead B U bW basis hb o S hR hσ nativePoly hmem base integerFrame
  have hrec := (allocatedAnchoredRecoveredSource_spec B U bW basis hb o S hR hσ
    nativePoly hmem base integerFrame).2 hden
  obtain ⟨hbase, hs, hprojection, hread⟩ := hrec
  have hsmallChart : ∀ a, |coefficientSamplerAmbientPoint U basis o sample a| < 1 / 2 := by
    intro a
    exact (hs a.1.1).1 a.1.2 a.2
  exact allocatedFixedPath_recovered_native_rational_density_comparison B U basis hR hσ S primes exponent
    hb o bW W τ ξ hτ hξ box hbox integerFrame hframe e h0 h1 hB sample (fun j => (hs j).2)
    ht hσbound b hη A hA htail hS q hsize hsmall hm hperiod hcover xref base
    nativePoly hmem hdegree hbase hsmallChart read (hread W.cover W.cover_pos)
    hp hinj hcoprime origin hqN hV

end Erdos3.VectorPolynomial

end

end OAI
