import OAI.Combinatorics.Progressions.Dynamics.AllocatedFixedPathRationalComparison
import OAI.Combinatorics.Progressions.Estimates.AllocatedActiveContainedTupleMap
import OAI.Combinatorics.Progressions.Probability.AllocatedFixedPathSlicedRationalDensityComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
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
local instance fixedPathDensityCRTModulusNeZero : NeZero N :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (primes l)))⟩
local notation "Long" => LayerSamplerLongVariables short G B
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)

include hR hσ in
theorem allocatedFixedPath_rational_density_comparison
    (z : Option G × X → ℝ) (hz : ∀ g x, |z (some g, x)| ≤ 1)
    (e : G ≃ X ⊕ (X ⊕ T))
    (h0 : (fixedSpatialKernelBlock e budget (S.value : ℝ) z false).det ≠ 0)
    (h1 : (fixedSpatialKernelBlock e budget (S.value : ℝ) z true).det ≠ 0)
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
    {Cidx : Type*} (selected : Cidx → Σ j : Fin m, Fin (n j))
    (hshort : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (xref : G → IntegerScalarCubeBox Empty S.value)
    (base : X → ℤ) (physicalNoise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis short j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (hp : ∀ l, (primes l).Prime) (hinj : Function.Injective primes)
    (hcoprime : Pairwise (fun l k => (primes l ^ exponent l).Coprime (primes k ^ exponent k)))
    (origin : ∀ l, Long → ZMod (primes l ^ exponent l))
    (hqN : q ∣ N) {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    (test : (Cidx → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ) →
      (Out → ZMod q) → Domain → ℂ) {Kφ : ℝ≥0}
    (hφ : ∀ grid residue, LipschitzWith Kφ (test grid residue))
    (hbound : ∀ grid residue y, ‖test grid residue y‖ ≤ 1) :
    let c := fun a => (sample (selected a).1).2 (selected a).2
    let poly := allocatedForecastPolynomial short base physicalNoise deck projection
    let lower := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) => (0 : ℝ)
    let width := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) =>
      ((S.value : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleFullSliceLip B U basis S t
    let kernel := FiniteProbabilityWeights.pi (fun _ : G => integerScalarCubeWeights Empty S.value S.positive)
    let law := principalTupleWeights (α := Empty) B degree sides hSides
    let density := fixedSpatialKernelOriginalForecastDensity B U basis S e budget
      (S.value : ℝ) z h0 h1 hB lower width sample
    ‖kernel.complexMean (fun x => law.complexMean (fun v =>
        test (forecastInactiveShortGrid B U basis S selected c (principalAxisRestrict short v))
          (allocatedJointResidueOutput B U basis S base physicalNoise deck projection q
            (fun g => ((x g none : ℤ) : ZMod q)) (principalResidueLabel q v))
          (fixedSpatialKernelMap budget (S.value : ℝ) z (fun g => (x g none : ℝ) / S.value),
            allocatedOriginalSampleFullSliceMap B U basis S x (principalAxisRestrict short v)
              (fun _ _ => 0) (fun _ _ => 1) sample
              (fun j => (((principalAxisRestrict (fun a => ¬short a) v) j none : ℤ) : ℝ) / S.value)))) -
      (∑' grid, 𝔼 residue : Out → ZMod N,
        ((rationalInactiveForecast law
          (fun _ => crtPolynomialInputLaw primes exponent (fun _ => 0) hcoprime origin)
          (forecastInactiveFixedOutput B U basis S selected c xref)
          (fun v => integerLongPolynomialOutput poly (fun k => (v k.1 k.2 : ℤ)) N)
          N gridVolume grid residue / gridVolume : ℝ) : ℂ) *
          ∫ y, test grid (fun j => ZMod.castHom hqN (ZMod q) (residue j)) y
            ∂realDensityMeasure volume density)‖ ≤
      ((Fintype.card Input : ℝ) * ((q : ℝ) / S.value) +
        (2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
          ∑ _j : Input, (q : ℝ) / S.value + K * (1 / S.value)) + 2 * η)) +
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + Kφ)) *
        (Fintype.card G * ((q : ℝ) / S.value)) := by
  classical
  intro c poly lower width K kernel law density
  have hSpos : (0 : ℝ) < S.value := by exact_mod_cast S.positive
  have hSreal : (2 : ℝ) ≤ S.value := by exact_mod_cast hS
  have hw : (1 / 2 : ℝ) ≤ ((S.value : ℝ) - 1) / S.value := by
    apply (le_div_iff₀ hSpos).mpr
    linarith
  have hid (grid : Cidx → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ)
      (residue : Out → ZMod q) :
      (∫ y, test grid residue y ∂realDensityMeasure volume density) =
        ∫ k, ∫ v, test grid residue (fixedSpatialKernelMap budget (S.value : ℝ) z k,
          allocatedOriginalSampleLiftMap B U basis S lower width sample v)
          ∂unitBoxMeasure Input ∂unitBoxMeasure G :=
    fixedSpatialKernelOriginalForecastDensity_iterated_test_integral B U basis hR hσ S
      e budget (S.value : ℝ) z h0 h1 hB lower width (δ := 1 / 2) (by norm_num)
      (fun _ _ => hw) (fun _ _ => le_rfl) sample hs (test grid residue)
      (hφ grid residue).continuous.measurable (hbound grid residue)
  simp_rw [hid]
  exact allocatedFixedPath_rational_forecast_comparison B U basis hR hσ S primes exponent
    z hz sample hs ht hσbound b hη A hA htail hS q hsize hsmall selected hshort xref
    base physicalNoise deck projection hp hinj hcoprime origin hqN hV test hφ hbound

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
local instance fixedPathPhysicalDensityCRTModulusNeZero : NeZero N :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (primes l)))⟩
local notation "Long" => LayerSamplerLongVariables short G B
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)

noncomputable def allocatedFixedPathKernelFrame (τ ξ : ℝ) (box : X → ℕ)
    (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    Option G × X → ℝ :=
  (fun k => (integerFrame k : ℝ) /
    narrowTrimmedSpatialWidths (G := G) (J := FullInput) budget τ ξ box k) ∘
      canonicalZeroSpatialKernelEmbedding G FullInput X

include hR hσ in
theorem allocatedFixedPath_physical_rational_density_comparison
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
    {Cidx : Type*} (selected : Cidx → Σ j : Fin m, Fin (n j))
    (hshort : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (xref : G → IntegerScalarCubeBox Empty S.value)
    (base : X → ℤ)
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis short j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (hp : ∀ l, (primes l).Prime) (hinj : Function.Injective primes)
    (hcoprime : Pairwise (fun l k => (primes l ^ exponent l).Coprime (primes k ^ exponent k)))
    (origin : ∀ l, Long → ZMod (primes l ^ exponent l))
    (hqN : q ∣ N) {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    (test : (Cidx → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ) →
      (Out → ZMod q) → Domain → ℂ) {Kφ : ℝ≥0}
    (hφ : ∀ grid residue, LipschitzWith Kφ (test grid residue))
    (hbound : ∀ grid residue y, ‖test grid residue y‖ ≤ 1) :
    let c := fun a => (sample (selected a).1).2 (selected a).2
    let poly := allocatedForecastPolynomial short base integerFrame deck projection
    let lower := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) => (0 : ℝ)
    let width := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) =>
      ((S.value : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleFullSliceLip B U basis S t
    let kernel := FiniteProbabilityWeights.pi (fun _ : G => integerScalarCubeWeights Empty S.value S.positive)
    let law := principalTupleWeights (α := Empty) B degree sides hSides
    let density := fixedSpatialKernelOriginalForecastDensity B U basis S e budget
      (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) h0 h1 hB lower width sample
    ‖kernel.complexMean (fun x => law.complexMean (fun v =>
        test (forecastInactiveShortGrid B U basis S selected c (principalAxisRestrict short v))
          (allocatedJointResidueOutput B U basis S base integerFrame deck projection q
            (fun g => ((x g none : ℤ) : ZMod q)) (principalResidueLabel q v))
          ((fun o : Σ _ : X, Unit ⊕ Empty =>
              (integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x v)
                integerFrame o.1 : ℝ) / (τ * (box o.1 : ℝ) / 8)),
            allocatedOriginalSampleFullSliceMap B U basis S x (principalAxisRestrict short v)
              (fun _ _ => 0) (fun _ _ => 1) sample
              (fun j => (((principalAxisRestrict (fun a => ¬short a) v) j none : ℤ) : ℝ) / S.value)))) -
      (∑' grid, 𝔼 residue : Out → ZMod N,
        ((rationalInactiveForecast law
          (fun _ => crtPolynomialInputLaw primes exponent (fun _ => 0) hcoprime origin)
          (forecastInactiveFixedOutput B U basis S selected c xref)
          (fun v => integerLongPolynomialOutput poly (fun k => (v k.1 k.2 : ℤ)) N)
          N gridVolume grid residue / gridVolume : ℝ) : ℂ) *
          ∫ y, test grid (fun j => ZMod.castHom hqN (ZMod q) (residue j)) y
            ∂realDensityMeasure volume density)‖ ≤
      ((Fintype.card Input : ℝ) * ((q : ℝ) / S.value) +
        (2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
          ∑ _j : Input, (q : ℝ) / S.value + K * (1 / S.value)) + 2 * η)) +
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + Kφ)) *
        (Fintype.card G * ((q : ℝ) / S.value)) + (Kφ : ℝ) * ξ := by
  classical
  intro c poly lower width K kernel law density
  let zK := allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame
  have hnorm := rectangularWeightIndices_normalized_norm_le _
    (narrowTrimmedSpatialWidths_pos
      (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)) hτ hξ box hbox) hframe
  have hzK : ∀ g x, |zK (some g, x)| ≤ 1 := by
    intro g x
    change |(integerFrame (some (Sum.inl g), x) : ℝ) /
      narrowTrimmedSpatialWidths (G := G) (J := FullInput) budget τ ξ box (some (Sum.inl g), x)| ≤ 1
    exact (Real.norm_eq_abs _).symm ▸
      (norm_le_pi_norm _ (some (Sum.inl g), x)).trans hnorm
  have hmain := allocatedFixedPath_rational_density_comparison B U basis hR hσ S primes exponent
    zK hzK e h0 h1 hB sample hs ht hσbound b hη A hA htail hS q hsize hsmall
    selected hshort xref base integerFrame deck projection hp hinj hcoprime origin hqN hV
    test hφ hbound
  let F := fun (x : G → IntegerScalarCubeBox Empty S.value) (v : Original) =>
    test (forecastInactiveShortGrid B U basis S selected c (principalAxisRestrict short v))
      (allocatedJointResidueOutput B U basis S base integerFrame deck projection q
        (fun g => ((x g none : ℤ) : ZMod q)) (principalResidueLabel q v))
      ((fun o : Σ _ : X, Unit ⊕ Empty =>
              (integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x v)
                integerFrame o.1 : ℝ) / (τ * (box o.1 : ℝ) / 8)),
        allocatedOriginalSampleFullSliceMap B U basis S x (principalAxisRestrict short v)
          (fun _ _ => 0) (fun _ _ => 1) sample
          (fun j => (((principalAxisRestrict (fun a => ¬short a) v) j none : ℤ) : ℝ) / S.value))
  let H := fun (x : G → IntegerScalarCubeBox Empty S.value) (v : Original) =>
    test (forecastInactiveShortGrid B U basis S selected c (principalAxisRestrict short v))
      (allocatedJointResidueOutput B U basis S base integerFrame deck projection q
        (fun g => ((x g none : ℤ) : ZMod q)) (principalResidueLabel q v))
      (fixedSpatialKernelMap budget (S.value : ℝ) zK (fun g => (x g none : ℝ) / S.value),
        allocatedOriginalSampleFullSliceMap B U basis S x (principalAxisRestrict short v)
          (fun _ _ => 0) (fun _ _ => 1) sample
          (fun j => (((principalAxisRestrict (fun a => ¬short a) v) j none : ℤ) : ℝ) / S.value))
  have hpoint (x : G → IntegerScalarCubeBox Empty S.value) (v : Original) :
      ‖F x v - H x v‖ ≤ (Kφ : ℝ) * ξ := by
    dsimp only [F, H]
    rw [← dist_eq_norm]
    apply le_trans ((hφ _ _).dist_le_mul _ _)
    rw [dist_prod_same_right]
    exact mul_le_mul_of_nonneg_left
      (allocatedFixedSpatialKernelMap_supported_narrow_physical_dist
        B U basis S x v hτ hξ box hbox integerFrame hframe) Kφ.coe_nonneg
  have hinner (x : G → IntegerScalarCubeBox Empty S.value) :
      ‖law.complexMean (F x) - law.complexMean (H x)‖ ≤ (Kφ : ℝ) * ξ :=
    (law.norm_complexMean_sub_le (F x) (H x) (fun _ => (Kφ : ℝ) * ξ)
      (fun v _ => hpoint x v)).trans_eq (law.mean_const _)
  have hchange := (kernel.norm_complexMean_sub_le
    (fun x => law.complexMean (F x)) (fun x => law.complexMean (H x))
    (fun _ => (Kφ : ℝ) * ξ) (fun x _ => hinner x)).trans_eq (kernel.mean_const _)
  change ‖kernel.complexMean (fun x => law.complexMean (F x)) - _‖ ≤ _
  have he := (norm_sub_le_norm_sub_add_norm_sub
    (kernel.complexMean (fun x => law.complexMean (F x)))
    (kernel.complexMean (fun x => law.complexMean (H x))) _).trans (add_le_add hchange hmain)
  simpa only [add_comm ((Kφ : ℝ) * ξ)] using he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype T] [Fintype G] [DecidableEq G] [Fintype X]
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

variable (u : PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))

local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)
local notation "Domain" => Spatial × (Output → ℝ)
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)

include hR hσ in
theorem allocatedFixedPath_sliced_physical_density_residue_comparison
    (τ ξ : ℝ) (hτ : 0 < τ) (hξ : 0 < ξ) (box : X → ℕ) (hbox : ∀ x, 0 < box x)
    (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hframe : integerFrame ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B degree) budget τ ξ box) 1)
    (HG : G → ℕ) (hHG : ∀ g, 2 ≤ HG g) (cG : G → ℤ)
    (stepG : ℕ) (hstepG : 0 < stepG)
    (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (e : G ≃ X ⊕ (X ⊕ T))
    (h0 : (fixedSpatialKernelBlock e budget (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) false).det ≠ 0)
    (h1 : (fixedSpatialKernelBlock e budget (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) true).det ≠ 0)
    (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    {t : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
    (step H : Input → ℕ) (c : Input → ℤ)
    (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (q : ℕ) [NeZero q]
    (hsizeG : ∀ g, q ≤ HG g)
    (hsmallG : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HG g) < 1) (hsize : ∀ j, q ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / S.value ≤ ε)
    (hδone : δ ≤ 1) (b : ∀ a : Active, B a.val)
    {η : ℝ} (hη : 0 < η)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (htail : |t| * polynomialMassC2Budget (Fintype.card Input) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card Input) (Fintype.card Active) m 1
        (unitProfilePrincipalLowerBound B) (δ / 2) A η)
    (φ : (G → ZMod q) → (Input → ZMod q) → Domain → ℂ) {Kφ : ℝ≥0}
    (hφ : ∀ rG r, LipschitzWith Kφ (φ rG r)) (hφone : ∀ rG r y, ‖φ rG r y‖ ≤ 1) :
    let lower := fun (a : Active) (p : B a.val × Fin (degree a.val)) => (c ⟨a, p⟩ : ℝ) / S.value
    let width := fun (a : Active) (p : B a.val × Fin (degree a.val)) =>
      (step ⟨a, p⟩ : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleFullSliceLip B U basis S t
    let kernel := FiniteProbabilityWeights.pi (fun g => integerScalarCubeWeights Empty (HG g) (by have := hHG g; omega))
    let active := FiniteProbabilityWeights.pi (fun j : Input => integerScalarCubeWeights Empty (H j)
      (by have := hH j; omega))
    let embed := fun (x : ∀ g, IntegerScalarCubeBox Empty (HG g)) g =>
      containedProgressionCubeMap Empty S.value (HG g) stepG (cG g) S.positive (hcontainedG g) (x g)
    let activeEmbed := allocatedActiveContainedProgression B U basis S step H c hsubset
    let joined := fun v => principalAxisJoin short u (activeEmbed v)
    let density := fixedSpatialKernelSliceOriginalForecastDensity B U basis S e budget
      (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) (fun g => (cG g : ℝ) / S.value)
      (fun g => (stepG : ℝ) * ((HG g - 1 : ℕ) : ℝ) / S.value) h0 h1
      (fun g => ne_of_gt (fixedSpatialKernelProgression_width_pos S.positive
        (show (0 : ℤ) < stepG by exact_mod_cast hstepG) (hHG g))) hB lower width sample
    ‖kernel.complexMean (fun x => active.complexMean (fun v =>
        φ (fun g => ((cG g + (stepG : ℤ) * (x g none : ℤ) : ℤ) : ZMod q))
          (fun j => ((c j + (step j : ℤ) * (v j none : ℤ) : ℤ) : ZMod q))
          ((fun o : Σ _ : X, Unit ⊕ Empty =>
              (integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0)
                (embed x) (joined v)) integerFrame o.1 : ℝ) / (τ * (box o.1 : ℝ) / 8)),
            (fun o : Output => allocatedFullMixedSiteValue (R := R) U basis
              (allocatedOriginalSamplePhysicalMixedValue B U basis S sample (embed x) (joined v))
                o.1.val)))) -
      (FiniteProbabilityWeights.uniform (Input → ZMod q)).complexMean (fun rA =>
        (FiniteProbabilityWeights.uniform (G → ZMod q)).complexMean (fun rG =>
          ∫ y, φ (fun g => (cG g : ZMod q) + (stepG : ZMod q) * rG g)
            (fun j => (c j : ZMod q) + (step j : ZMod q) * rA j) y
            ∂realDensityMeasure volume density))‖ ≤
      ((∑ j, (q : ℝ) / H j) +
        (2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
          ∑ j, (q : ℝ) / H j + K * ε) + 2 * η)) +
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + Kφ) + Kφ) * ∑ g, (q : ℝ) / HG g + (Kφ : ℝ) * ξ := by
  classical
  intro lower width K kernel active embed activeEmbed joined density
  let zK := allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame
  have hnorm := rectangularWeightIndices_normalized_norm_le _
    (narrowTrimmedSpatialWidths_pos
      (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)) hτ hξ box hbox) hframe
  have hzK : ∀ g x, |zK (some g, x)| ≤ 1 := by
    intro g x
    change |(integerFrame (some (Sum.inl g), x) : ℝ) /
      narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B degree)
        budget τ ξ box (some (Sum.inl g), x)| ≤ 1
    exact (Real.norm_eq_abs _).symm ▸
      (norm_le_pi_norm _ (some (Sum.inl g), x)).trans hnorm
  have hmain := allocatedFixedPath_sliced_density_residue_comparison B U basis hR hσ S u
    zK hzK HG hHG cG stepG hstepG hcontainedG e h0 h1 hB sample hs ht hσbound
    step H c hstep hH hδ hsubset hdense q hsizeG hsmallG hsize hsmall hε hmesh
    hδone b hη A hA htail φ hφ hφone
  let F := fun (x : ∀ g, IntegerScalarCubeBox Empty (HG g))
      (v : ∀ j : Input, IntegerScalarCubeBox Empty (H j)) =>
    φ (fun g => ((cG g + (stepG : ℤ) * (x g none : ℤ) : ℤ) : ZMod q))
      (fun j => ((c j + (step j : ℤ) * (v j none : ℤ) : ℤ) : ZMod q))
      ((fun o : Σ _ : X, Unit ⊕ Empty =>
          (integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0)
            (embed x) (joined v)) integerFrame o.1 : ℝ) / (τ * (box o.1 : ℝ) / 8)),
        (fun o : Output => allocatedFullMixedSiteValue (R := R) U basis
          (allocatedOriginalSamplePhysicalMixedValue B U basis S sample (embed x) (joined v)) o.1.val))
  let Fideal := fun (x : ∀ g, IntegerScalarCubeBox Empty (HG g))
      (v : ∀ j : Input, IntegerScalarCubeBox Empty (H j)) =>
    φ (fun g => ((cG g + (stepG : ℤ) * (x g none : ℤ) : ℤ) : ZMod q))
      (fun j => ((c j + (step j : ℤ) * (v j none : ℤ) : ℤ) : ZMod q))
      (fixedSpatialKernelMap budget (S.value : ℝ) zK
        (fun g => ((cG g : ℝ) + (stepG : ℝ) * (x g none : ℝ)) / S.value),
        allocatedOriginalSampleFullSliceMap B U basis S (embed x) u (fun _ _ => 0) (fun _ _ => 1)
          sample (fun j => ((c j : ℝ) + (step j : ℝ) * (v j none : ℝ)) / S.value))
  have hpoint (x : ∀ g, IntegerScalarCubeBox Empty (HG g)) (hx : kernel.weight x ≠ 0)
      (v : ∀ j : Input, IntegerScalarCubeBox Empty (H j)) (hv : active.weight v ≠ 0) :
      ‖F x v - Fideal x v‖ ≤ (Kφ : ℝ) * ξ := by
    have hid := allocatedOriginalSampleFullSliceMap_contained_physical B U basis S
      step H c (fun j => by have := hH j; omega) hsubset v hv sample (embed x) u
    dsimp only [F, Fideal]
    rw [hid, ← dist_eq_norm]
    apply le_trans ((hφ _ _).dist_le_mul _ _)
    rw [dist_prod_same_right]
    exact mul_le_mul_of_nonneg_left
      (allocatedContainedKernel_supported_narrow_physical_dist B U basis S
        HG (fun _ => stepG) cG (fun g => by have := hHG g; omega) hcontainedG x hx
        (joined v) hτ hξ box hbox integerFrame hframe) Kφ.coe_nonneg
  have hinner (x : ∀ g, IntegerScalarCubeBox Empty (HG g)) (hx : kernel.weight x ≠ 0) :
      ‖active.complexMean (F x) - active.complexMean (Fideal x)‖ ≤ (Kφ : ℝ) * ξ :=
    (active.norm_complexMean_sub_le (F x) (Fideal x) (fun _ => (Kφ : ℝ) * ξ)
      (fun v hv => hpoint x hx v hv)).trans_eq (active.mean_const _)
  have hchange := (kernel.norm_complexMean_sub_le
    (fun x => active.complexMean (F x)) (fun x => active.complexMean (Fideal x))
    (fun _ => (Kφ : ℝ) * ξ) hinner).trans_eq (kernel.mean_const _)
  change ‖kernel.complexMean (fun x => active.complexMean (F x)) - _‖ ≤ _
  have he := (norm_sub_le_norm_sub_add_norm_sub
    (kernel.complexMean (fun x => active.complexMean (F x)))
    (kernel.complexMean (fun x => active.complexMean (Fideal x))) _).trans (add_le_add hchange hmain)
  simpa only [add_comm ((Kφ : ℝ) * ξ)] using he

end Erdos3.VectorPolynomial

end

end OAI
