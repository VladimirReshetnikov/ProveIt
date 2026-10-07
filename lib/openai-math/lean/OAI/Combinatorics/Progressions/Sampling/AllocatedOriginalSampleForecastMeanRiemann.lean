import OAI.Combinatorics.Progressions.Probability.GenericProbabilityProductMapIntegral
import OAI.Combinatorics.Progressions.Probability.GenericSampleExpectation
import OAI.Combinatorics.Progressions.Sampling.AllocatedOriginalSampleForecastAtom

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X Zsp : Type*} [Fintype G] [Fintype X]
  [Fintype Zsp] [DecidableEq Zsp]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
  (hp : (selectedSpatialPivot root D s).det ≠ 0)
  {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Output" => (Σ _a : Active, Unit)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Input" => (Σ a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis S.value a}, B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a)))
local notation "Domain" => ((Spatial → ℝ) × (Output → ℝ))
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short
local notation "amin" => unitProfilePrincipalLowerBound B
local notation "hamin" => unitProfilePrincipalLowerBound_pos B

variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
  {δ : ℝ} (hδ : 0 < δ)

noncomputable def allocatedOriginalSampleForecastSource (sample : Sample) : Measure Domain :=
  (sigmaAxisMeasure (fun _ : X => Measure.map
    (canonicalSpatialKernelMap s root D (W := W) (L := L))
    (realDensityMeasure volume (smoothSplitProfile (UnselectedColumn s) (Unit ⊕ Empty))))).prod
      ((unitBoxMeasure Input).map (allocatedOriginalSampleLiftMap B U basis S lower width sample))

variable (hw : ∀ a p, δ ≤ width a p) (hl : ∀ a p, 0 ≤ lower a p)

include hR hσ hδ hw hl in
theorem allocatedOriginalSampleForecastSource_ae_density
    (hroot : ∀ j, |(root j : ℝ)| ≤ 1 + W) :
    ∀ᵐ sample ∂allocatedCoefficientSource B U basis hR hσ S,
      allocatedOriginalSampleForecastSource (X := X) (W := W) (L := L) B U basis S s root D lower width sample =
        realDensityMeasure volume (allocatedOriginalSampleForecastDensity (X := X)
          B U basis S s root D hp hW hL hB lower width sample) := by
  filter_upwards [allocatedSampleRestrictedProfileNoise_short_ae_abs_le B U basis hR hσ S]
    with sample hr
  have he := allocatedFixedPathForecastDensity_image_law (X := X)
    B short R σ s root D hp hW hL (fun j => (hR j).ne') hB lower width hamin hδ
    (fun a => unitProfilePrincipalLowerBound_le B a.val) hw hl (noise sample) hr
    zero_lt_one hroot (by simp only [Matrix.det_isEmpty, abs_one, le_refl])
  simpa only [allocatedOriginalSampleForecastSource, allocatedOriginalSampleForecastDensity,
    allocatedOriginalSampleLiftMap_eq_fixedPath B U basis S lower width hR hσ sample] using he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X Zsp : Type*} [Fintype G] [Fintype X]
  [Fintype Zsp] [DecidableEq Zsp]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
  (hp : (selectedSpatialPivot root D s).det ≠ 0)
  {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Output" => (Σ _a : Active, Unit)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Input" => (Σ a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis S.value a}, B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a)))
local notation "Domain" => ((Spatial → ℝ) × (Output → ℝ))
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short
local notation "amin" => unitProfilePrincipalLowerBound B
local notation "hamin" => unitProfilePrincipalLowerBound_pos B

variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
  {δ : ℝ} (hδ : 0 < δ)

variable (hw : ∀ a p, δ ≤ width a p) (hl : ∀ a p, 0 ≤ lower a p)

include hδ hw hl in
theorem allocatedOriginalSampleForecastSource_density_of_supported
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hroot : ∀ j, |(root j : ℝ)| ≤ 1 + W) :
    allocatedOriginalSampleForecastSource (X := X) (W := W) (L := L)
      B U basis S s root D lower width sample =
      realDensityMeasure volume (allocatedOriginalSampleForecastDensity (X := X)
        B U basis S s root D hp hW hL hB lower width sample) := by
  have hr := allocatedSampleRestrictedProfileNoise_short_abs_le B U basis hR hσ S sample hs
  have he := allocatedFixedPathForecastDensity_image_law (X := X)
    B short R σ s root D hp hW hL (fun j => (hR j).ne') hB lower width hamin hδ
    (fun a => unitProfilePrincipalLowerBound_le B a.val) hw hl (noise sample) hr
    zero_lt_one hroot (by simp only [Matrix.det_isEmpty, abs_one, le_refl])
  simpa only [allocatedOriginalSampleForecastSource, allocatedOriginalSampleForecastDensity,
    allocatedOriginalSampleLiftMap_eq_fixedPath B U basis S lower width hR hσ sample] using he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

noncomputable def canonicalZeroSpatialLaw
    {X Zsp : Type*} [Fintype X] [Fintype Zsp] [DecidableEq Zsp]
    (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ) (W L : ℝ) :
    Measure ((Σ _ : X, Unit ⊕ Empty) → ℝ) :=
  sigmaAxisMeasure (fun _ : X => Measure.map
    (canonicalSpatialKernelMap s root D (W := W) (L := L))
    (realDensityMeasure volume (smoothSplitProfile (UnselectedColumn s) (Unit ⊕ Empty))))

theorem canonicalZeroSpatialLaw_eq_density
    {X Zsp : Type*} [Fintype X] [Fintype Zsp] [DecidableEq Zsp]
    (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L) :
    canonicalZeroSpatialLaw (X := X) s root D W L =
      realDensityMeasure volume
        (canonicalZeroSpatialJointDensity (X := X) s root D hp hW hL) :=
  canonicalZeroSpatialJointDensity_image_law s root D hp hW hL

theorem canonicalZeroSpatialLaw_probability
    {X Zsp : Type*} [Fintype X] [Fintype Zsp] [DecidableEq Zsp]
    (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L) :
    IsProbabilityMeasure (canonicalZeroSpatialLaw (X := X) s root D W L) := by
  rw [canonicalZeroSpatialLaw_eq_density s root D hp hW hL]
  have hd := canonicalZeroSpatialJointDensity_probability_data (X := X) s root D hp hW hL
  exact realDensityMeasure_probability volume _ hd.2.1 hd.1 hd.2.2

namespace VectorPolynomial

variable {m : ℕ} {G X Zsp : Type*} [Fintype G] [Fintype X]
  [Fintype Zsp] [DecidableEq Zsp]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Domain" => ((Spatial → ℝ) × (Output → ℝ))

variable (lower width : ∀ a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

theorem allocatedOriginalSampleLiftMap_fixed_measurable (sample : Sample) :
    Measurable (allocatedOriginalSampleLiftMap B U basis S lower width sample) :=
  (allocatedOriginalSampleLiftMap_measurable B U basis S lower width).comp
    (measurable_const.prodMk measurable_id)

variable (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
  (hp : (selectedSpatialPivot root D s).det ≠ 0)
  {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)

include hp hW hL in
theorem allocatedOriginalSampleForecastSource_probability (sample : Sample) :
    IsProbabilityMeasure (allocatedOriginalSampleForecastSource (X := X) (W := W) (L := L)
      B U basis S s root D lower width sample) := by
  let :=  canonicalZeroSpatialLaw_probability (X := X) s root D hp hW hL
  let : IsProbabilityMeasure ((unitBoxMeasure Input).map
      (allocatedOriginalSampleLiftMap B U basis S lower width sample)) :=
    inferInstance
  change IsProbabilityMeasure ((canonicalZeroSpatialLaw (X := X) s root D W L).prod _)
  infer_instance

include hp hW hL in
theorem allocatedOriginalSampleForecastSource_integral
    (sample : Sample) (φ : Domain → ℂ) (hφ : Measurable φ)
    {C : ℝ} (hC : ∀ p, ‖φ p‖ ≤ C) :
    (∫ p, φ p ∂allocatedOriginalSampleForecastSource (X := X) (W := W) (L := L)
      B U basis S s root D lower width sample) =
      ∫ z, ∫ x, φ (z, allocatedOriginalSampleLiftMap B U basis S lower width sample x)
        ∂unitBoxMeasure Input ∂canonicalZeroSpatialLaw (X := X) s root D W L := by
  let :=  canonicalZeroSpatialLaw_probability (X := X) s root D hp hW hL
  exact probability_prod_map_integral (canonicalZeroSpatialLaw (X := X) s root D W L)
    (unitBoxMeasure Input) (allocatedOriginalSampleLiftMap B U basis S lower width sample)
    (allocatedOriginalSampleLiftMap_fixed_measurable B U basis S lower width sample) φ hφ hC

include hp hW hL in
theorem allocatedOriginalSampleForecastSource_real_integral
    (sample : Sample) (φ : Domain → ℝ) (hφ : Measurable φ)
    {C : ℝ} (hC : ∀ p, ‖φ p‖ ≤ C) :
    (∫ p, φ p ∂allocatedOriginalSampleForecastSource (X := X) (W := W) (L := L)
      B U basis S s root D lower width sample) =
      ∫ z, ∫ x, φ (z, allocatedOriginalSampleLiftMap B U basis S lower width sample x)
        ∂unitBoxMeasure Input ∂canonicalZeroSpatialLaw (X := X) s root D W L := by
  let :=  canonicalZeroSpatialLaw_probability (X := X) s root D hp hW hL
  exact probability_prod_map_real_integral (canonicalZeroSpatialLaw (X := X) s root D W L)
    (unitBoxMeasure Input) (allocatedOriginalSampleLiftMap B U basis S lower width sample)
    (allocatedOriginalSampleLiftMap_fixed_measurable B U basis S lower width sample) φ hφ hC

omit [Fintype X] in
theorem allocatedOriginalSampleForecastPartial_measurable
    (sample : Sample) (φ : Domain → ℂ) (hφ : Measurable φ) :
    Measurable (fun z => ∫ x, φ (z, allocatedOriginalSampleLiftMap B U basis S lower width sample x)
      ∂unitBoxMeasure Input) := by
  exact probability_partial_map_integral_measurable (unitBoxMeasure Input)
    (allocatedOriginalSampleLiftMap B U basis S lower width sample)
    (allocatedOriginalSampleLiftMap_fixed_measurable B U basis S lower width sample) φ hφ

omit [Fintype X] in
theorem allocatedOriginalSampleForecastPartial_norm_le
    (sample : Sample) (φ : Domain → ℂ) {C : ℝ} (hC : ∀ p, ‖φ p‖ ≤ C)
    (z : Spatial → ℝ) :
    ‖∫ x, φ (z, allocatedOriginalSampleLiftMap B U basis S lower width sample x)
      ∂unitBoxMeasure Input‖ ≤ C := by
  exact probability_partial_map_integral_norm_le (unitBoxMeasure Input)
    (allocatedOriginalSampleLiftMap B U basis S lower width sample) φ hC z

include hp hW hL in
theorem allocatedOriginalSampleForecastPartial_integrable
    (sample : Sample) (φ : Domain → ℂ) (hφ : Measurable φ)
    {C : ℝ} (hC : ∀ p, ‖φ p‖ ≤ C) :
    Integrable (fun z => ∫ x, φ (z, allocatedOriginalSampleLiftMap B U basis S lower width sample x)
      ∂unitBoxMeasure Input) (canonicalZeroSpatialLaw (X := X) s root D W L) := by
  let :=  canonicalZeroSpatialLaw_probability (X := X) s root D hp hW hL
  exact probability_partial_map_integral_integrable (canonicalZeroSpatialLaw (X := X) s root D W L)
    (unitBoxMeasure Input) (allocatedOriginalSampleLiftMap B U basis S lower width sample)
    (allocatedOriginalSampleLiftMap_fixed_measurable B U basis S lower width sample) φ hφ hC

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X Zsp : Type*} [Fintype G] [Fintype X] [Fintype Zsp] [DecidableEq Zsp]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "activeB" => (fun a : Active => B (Subtype.val a))
local notation "activeDegree" => (fun a : Active => degree (Subtype.val a))
local notation "Input" => PrincipalTupleIndex activeB activeDegree
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

theorem allocatedOriginalSampleForecastSource_progression_density
    (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)
    (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (hroot : ∀ j, |(root j : ℝ)| ≤ 1 + W)
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (step H : Input → ℕ) (c : Input → ℤ)
    (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    :
    let lower := fun (a : Active) (p : B a.val × Fin (degree a.val)) => (c ⟨a, p⟩ : ℝ) / S.value
    let width := fun (a : Active) (p : B a.val × Fin (degree a.val)) =>
      (step ⟨a, p⟩ : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
    allocatedOriginalSampleForecastSource (X := X) (W := W) (L := L)
      B U basis S s root D lower width sample =
    realDensityMeasure volume (allocatedOriginalSampleForecastDensity (X := X)
      B U basis S s root D hp hW hL hB lower width sample) := by
  intro lower width
  have hgeom (j : Input) := progression_slice_endpoint_geometry (c j) S.positive
    (hstep j) (hH j) hδ (hsubset j) (hdense j)
  exact allocatedOriginalSampleForecastSource_density_of_supported (X := X) B U basis hR hσ S
    s root D hp hW hL hB lower width (half_pos hδ)
    (fun a p => (hgeom ⟨a, p⟩).2.1) (fun a p => (hgeom ⟨a, p⟩).1) sample hs hroot

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X Zsp : Type*} [Fintype G] [Fintype X]
  [Fintype Zsp] [DecidableEq Zsp]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Domain" => ((Spatial → ℝ) × (Output → ℝ))

variable (lower width : ∀ a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
variable (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
  (hp : (selectedSpatialPivot root D s).det ≠ 0)
  {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)

include hp hW hL in
theorem allocatedOriginalSampleForecastExpectation_eq_iterated
    (φ : Sample × Domain → ℂ) (hφ : Measurable φ)
    (hφ1 : ∀ p, ‖φ p‖ ≤ 1) (sample : Sample) :
    (∫ z, φ (sample, z) ∂allocatedOriginalSampleForecastSource (X := X) (W := W) (L := L)
      B U basis S s root D lower width sample) =
      ∫ z, ∫ x, φ (sample, (z, allocatedOriginalSampleLiftMap B U basis S lower width sample x))
        ∂unitBoxMeasure Input ∂canonicalZeroSpatialLaw (X := X) s root D W L := by
  exact allocatedOriginalSampleForecastSource_integral B U basis S lower width s root D hp hW hL
    sample (fun z => φ (sample, z))
    (hφ.comp (measurable_const.prodMk measurable_id)) (fun z => hφ1 (sample, z))

include hp hW hL in
theorem allocatedOriginalSampleForecastExpectation_norm_le
    (φ : Sample × Domain → ℂ) (hφ1 : ∀ p, ‖φ p‖ ≤ 1) (sample : Sample) :
    ‖∫ z, φ (sample, z) ∂allocatedOriginalSampleForecastSource (X := X) (W := W) (L := L)
      B U basis S s root D lower width sample‖ ≤ 1 := by
  let := allocatedOriginalSampleForecastSource_probability (X := X)
    B U basis S lower width s root D hp hW hL sample
  simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const
    (μ := allocatedOriginalSampleForecastSource (X := X) (W := W) (L := L)
      B U basis S s root D lower width sample)
    (ae_of_all _ (fun z => hφ1 (sample, z)))

include hp hW hL in
theorem allocatedOriginalSampleFiniteExpectation_measurable
    {T : Type*} [Fintype T] (p : FiniteProbabilityWeights T) (input : T → Input → ℝ)
    (φ : Sample × Domain → ℂ) (hφ : Measurable φ) :
    Measurable (fun sample => ∫ z, p.complexMean (fun t =>
      φ (sample, (z, allocatedOriginalSampleLiftMap B U basis S lower width sample (input t))))
      ∂canonicalZeroSpatialLaw (X := X) s root D W L) := by
  let := canonicalZeroSpatialLaw_probability (X := X) s root D hp hW hL
  exact genericSampleFiniteExpectation_measurable
    (canonicalZeroSpatialLaw (X := X) s root D W L) p input
    (fun q : Sample × (Input → ℝ) => allocatedOriginalSampleLiftMap B U basis S lower width q.1 q.2)
    (allocatedOriginalSampleLiftMap_measurable B U basis S lower width) φ hφ

include hp hW hL in
theorem allocatedOriginalSampleFiniteExpectation_norm_le
    {T : Type*} [Fintype T] (p : FiniteProbabilityWeights T) (input : T → Input → ℝ)
    (φ : Sample × Domain → ℂ) (hφ1 : ∀ q, ‖φ q‖ ≤ 1) (sample : Sample) :
    ‖∫ z, p.complexMean (fun t =>
      φ (sample, (z, allocatedOriginalSampleLiftMap B U basis S lower width sample (input t))))
      ∂canonicalZeroSpatialLaw (X := X) s root D W L‖ ≤ 1 := by
  let := canonicalZeroSpatialLaw_probability (X := X) s root D hp hW hL
  exact genericSampleFiniteExpectation_norm_le
    (canonicalZeroSpatialLaw (X := X) s root D W L) p input
    (fun q : Sample × (Input → ℝ) => allocatedOriginalSampleLiftMap B U basis S lower width q.1 q.2)
    φ hφ1 sample

include hp hW hL in
theorem allocatedOriginalSampleForecastExpectation_measurable
    (φ : Sample × Domain → ℂ) (hφ : Measurable φ) (hφ1 : ∀ p, ‖φ p‖ ≤ 1) :
    Measurable (fun sample => ∫ z, φ (sample, z)
      ∂allocatedOriginalSampleForecastSource (X := X) (W := W) (L := L)
        B U basis S s root D lower width sample) := by
  let := canonicalZeroSpatialLaw_probability (X := X) s root D hp hW hL
  have h := genericSampleDoubleExpectation_measurable
    (canonicalZeroSpatialLaw (X := X) s root D W L) (unitBoxMeasure Input)
    (fun q : Sample × (Input → ℝ) => allocatedOriginalSampleLiftMap B U basis S lower width q.1 q.2)
    (allocatedOriginalSampleLiftMap_measurable B U basis S lower width) φ hφ
  convert h using 1
  funext sample
  exact allocatedOriginalSampleForecastExpectation_eq_iterated B U basis S lower width
    s root D hp hW hL φ hφ hφ1 sample

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X Zsp : Type*} [Fintype G] [Fintype X] [Fintype Zsp] [DecidableEq Zsp]
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
local notation "activeB" => (fun a : Active => B (Subtype.val a))
local notation "activeDegree" => (fun a : Active => degree (Subtype.val a))
local notation "Input" => PrincipalTupleIndex activeB activeDegree
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

theorem allocatedOriginalSampleForecast_contained_residue_riemann
    (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (step H : Input → ℕ) (c : Input → ℤ)
    (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (q : ℕ) (hq : 0 < q) (residue : Input → Option Empty → ZMod q)
    (hsize : ∀ j, q ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / S.value ≤ ε)
    (φ : (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ)) → ℝ) {Kφ : ℝ≥0}
    (hφ : LipschitzWith Kφ φ) (hφone : ∀ y, ‖φ y‖ ≤ 1) :
    let lower := fun (a : Active) (p : B a.val × Fin (degree a.val)) => (c ⟨a, p⟩ : ℝ) / S.value
    let width := fun (a : Active) (p : B a.val × Fin (degree a.val)) =>
      (step ⟨a, p⟩ : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleLiftLip B U basis S
    |(∫ z, (containedProgressionResidueLaw activeB activeDegree (fun _ => S.value) H step c
        (fun _ => S.positive) (fun j => by have := hH j; omega) hsubset q hq residue
        (fun j => by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize j)).mean
        (fun v => φ (z, allocatedOriginalSampleLiftMap B U basis S (fun _ _ => 0) (fun _ _ => 1)
          sample (fun j => (v j none : ℝ) / S.value)))
          ∂canonicalZeroSpatialLaw (X := X) s root D W L) -
      ∫ y, φ y ∂allocatedOriginalSampleForecastSource (X := X) (W := W) (L := L)
        B U basis S s root D lower width sample| ≤
      (2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ j, (q : ℝ) / H j + K * ε := by
  classical
  intro lower width K
  let := canonicalZeroSpatialLaw_probability (X := X) s root D hp hW hL
  rw [allocatedOriginalSampleForecastSource_real_integral B U basis S lower width
    s root D hp hW hL sample φ hφ.continuous.measurable hφone]
  apply finiteProbability_tensor_comparison
    (canonicalZeroSpatialLaw (X := X) s root D W L) _ (unitBoxMeasure Input) _ _
    (allocatedOriginalSampleLiftMap_fixed_measurable B U basis S lower width sample)
    φ hφ.continuous.measurable hφone
  intro z
  have hφz : LipschitzWith Kφ (fun y : Output → ℝ => φ (z, y)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using hφ.dist_le_mul (z, x) (z, y)
  exact allocatedOriginalSampleLift_contained_residue_riemann_of_supported
    B U basis hR hσ S sample hs step H c hstep hH hδ hsubset hdense
    q hq residue hsize hsmall hε hmesh (fun y => φ (z, y)) hφz (fun y => hφone (z, y))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X Zsp : Type*} [Fintype G] [Fintype X] [Fintype Zsp] [DecidableEq Zsp]
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
local notation "activeB" => (fun a : Active => B (Subtype.val a))
local notation "activeDegree" => (fun a : Active => degree (Subtype.val a))
local notation "Input" => PrincipalTupleIndex activeB activeDegree
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

theorem allocatedOriginalSampleForecast_contained_residue_complex_riemann
    (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (step H : Input → ℕ) (c : Input → ℤ)
    (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (q : ℕ) (hq : 0 < q) (residue : Input → Option Empty → ZMod q)
    (hsize : ∀ j, q ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / S.value ≤ ε)
    (φ : (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ)) → ℂ) {Kφ : ℝ≥0}
    (hφ : LipschitzWith Kφ φ) (hφone : ∀ y, ‖φ y‖ ≤ 1) :
    let lower := fun (a : Active) (p : B a.val × Fin (degree a.val)) => (c ⟨a, p⟩ : ℝ) / S.value
    let width := fun (a : Active) (p : B a.val × Fin (degree a.val)) =>
      (step ⟨a, p⟩ : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleLiftLip B U basis S
    ‖(∫ z, (containedProgressionResidueLaw activeB activeDegree (fun _ => S.value) H step c
        (fun _ => S.positive) (fun j => by have := hH j; omega) hsubset q hq residue
        (fun j => by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize j)).complexMean
        (fun v => φ (z, allocatedOriginalSampleLiftMap B U basis S (fun _ _ => 0) (fun _ _ => 1)
          sample (fun j => (v j none : ℝ) / S.value)))
          ∂canonicalZeroSpatialLaw (X := X) s root D W L) -
      ∫ y, φ y ∂allocatedOriginalSampleForecastSource (X := X) (W := W) (L := L)
        B U basis S s root D lower width sample‖ ≤
      2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ j, (q : ℝ) / H j + K * ε) := by
  classical
  intro lower width K
  let μ := canonicalZeroSpatialLaw (X := X) s root D W L
  let ν := allocatedOriginalSampleForecastSource (X := X) (W := W) (L := L)
    B U basis S s root D lower width sample
  let p := containedProgressionResidueLaw activeB activeDegree (fun _ => S.value) H step c
    (fun _ => S.positive) (fun j => by have := hH j; omega) hsubset q hq residue
    (fun j => by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize j)
  let F := allocatedOriginalSampleLiftMap B U basis S (fun _ _ => 0) (fun _ _ => 1) sample
  let f := fun (z : (Σ _ : X, Unit ⊕ Empty) → ℝ)
      (v : PrincipalIntegerTuples activeB activeDegree Empty (fun _ => S.value)) =>
    φ (z, F (fun j => (v j none : ℝ) / S.value))
  let : IsProbabilityMeasure μ := canonicalZeroSpatialLaw_probability s root D hp hW hL
  let : IsProbabilityMeasure ν := allocatedOriginalSampleForecastSource_probability
    B U basis S lower width s root D hp hW hL sample
  have hiφ : Integrable φ ν :=
    Integrable.mono' (integrable_const (1 : ℝ)) hφ.continuous.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall hφone)
  have hif : Integrable (fun z => p.complexMean (f z)) μ := by
    apply p.complexMean_integrable μ f
    intro v
    apply Integrable.mono' (integrable_const (1 : ℝ))
      (hφ.continuous.measurable.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun z => hφone _)
  have hφre : LipschitzWith Kφ (fun y => (φ y).re) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, ← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans (by simpa only [dist_eq_norm] using hφ.dist_le_mul x y)
  have hφim : LipschitzWith Kφ (fun y => (φ y).im) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, ← Complex.sub_im]
    exact (Complex.abs_im_le_norm _).trans (by simpa only [dist_eq_norm] using hφ.dist_le_mul x y)
  have hre := allocatedOriginalSampleForecast_contained_residue_riemann
    B U basis hR hσ S s root D hp hW hL sample hs step H c hstep hH hδ hsubset hdense
    q hq residue hsize hsmall hε hmesh (fun y => (φ y).re) hφre
    (fun y => (Complex.abs_re_le_norm (φ y)).trans (hφone y))
  have him := allocatedOriginalSampleForecast_contained_residue_riemann
    B U basis hR hσ S s root D hp hW hL sample hs step H c hstep hH hδ hsubset hdense
    q hq residue hsize hsmall hε hmesh (fun y => (φ y).im) hφim
    (fun y => (Complex.abs_im_le_norm (φ y)).trans (hφone y))
  have hfre : (∫ z, p.complexMean (f z) ∂μ).re =
      ∫ z, p.mean (fun v => (f z v).re) ∂μ := by
    simpa only [RCLike.re_eq_complex_re, FiniteProbabilityWeights.complexMean_re] using
      (integral_re hif).symm
  have hfim : (∫ z, p.complexMean (f z) ∂μ).im =
      ∫ z, p.mean (fun v => (f z v).im) ∂μ := by
    simpa only [RCLike.im_eq_complex_im, FiniteProbabilityWeights.complexMean_im] using
      (integral_im hif).symm
  have hνre : (∫ y, φ y ∂ν).re = ∫ y, (φ y).re ∂ν := by
    simpa only [RCLike.re_eq_complex_re] using (integral_re hiφ).symm
  have hνim : (∫ y, φ y ∂ν).im = ∫ y, (φ y).im ∂ν := by
    simpa only [RCLike.im_eq_complex_im] using (integral_im hiφ).symm
  change ‖(∫ z, p.complexMean (f z) ∂μ) - ∫ y, φ y ∂ν‖ ≤ _
  calc
    _ ≤ |((∫ z, p.complexMean (f z) ∂μ) - ∫ y, φ y ∂ν).re| +
        |((∫ z, p.complexMean (f z) ∂μ) - ∫ y, φ y ∂ν).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
          ∑ j, (q : ℝ) / H j + K * ε) +
        ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
          ∑ j, (q : ℝ) / H j + K * ε) := by
      apply add_le_add
      · rw [Complex.sub_re, hfre, hνre]
        exact hre
      · rw [Complex.sub_im, hfim, hνim]
        exact him
    _ = _ := by ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X Zsp : Type*} [Fintype G] [Fintype X] [Fintype Zsp] [DecidableEq Zsp]
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
local notation "activeB" => (fun a : Active => B (Subtype.val a))
local notation "activeDegree" => (fun a : Active => degree (Subtype.val a))
local notation "Input" => PrincipalTupleIndex activeB activeDegree
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

theorem allocatedOriginalSampleForecast_contained_residue_ae_complex_riemann
    (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)
    (step H : Input → ℕ) (c : Input → ℤ)
    (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (q : ℕ) (hq : 0 < q) (residue : Input → Option Empty → ZMod q)
    (hsize : ∀ j, q ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / S.value ≤ ε)
    (φ : Sample → (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ)) → ℂ) {Kφ : ℝ≥0}
    (hφ : ∀ sample, LipschitzWith Kφ (φ sample))
    (hφone : ∀ sample y, ‖φ sample y‖ ≤ 1) :
    ∀ᵐ sample ∂allocatedCoefficientSource B U basis hR hσ S,
    let lower := fun (a : Active) (p : B a.val × Fin (degree a.val)) => (c ⟨a, p⟩ : ℝ) / S.value
    let width := fun (a : Active) (p : B a.val × Fin (degree a.val)) =>
      (step ⟨a, p⟩ : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleLiftLip B U basis S
    ‖(∫ z, (containedProgressionResidueLaw activeB activeDegree (fun _ => S.value) H step c
        (fun _ => S.positive) (fun j => by have := hH j; omega) hsubset q hq residue
        (fun j => by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize j)).complexMean
        (fun v => φ sample (z, allocatedOriginalSampleLiftMap B U basis S (fun _ _ => 0) (fun _ _ => 1)
          sample (fun j => (v j none : ℝ) / S.value)))
          ∂canonicalZeroSpatialLaw (X := X) s root D W L) -
      ∫ y, φ sample y ∂allocatedOriginalSampleForecastSource (X := X) (W := W) (L := L)
        B U basis S s root D lower width sample‖ ≤
      2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ j, (q : ℝ) / H j + K * ε) := by
  filter_upwards [allocatedCoefficientSource_supported B U basis hR hσ S] with sample hs
  exact allocatedOriginalSampleForecast_contained_residue_complex_riemann B U basis hR hσ S
    s root D hp hW hL sample hs step H c hstep hH hδ hsubset hdense
    q hq residue hsize hsmall hε hmesh (φ sample) (hφ sample) (hφone sample)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X Zsp : Type*} [Fintype G] [Fintype X] [Fintype Zsp] [DecidableEq Zsp]
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
local notation "activeB" => (fun a : Active => B (Subtype.val a))
local notation "activeDegree" => (fun a : Active => degree (Subtype.val a))
local notation "Input" => PrincipalTupleIndex activeB activeDegree
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

theorem allocatedOriginalSampleForecast_contained_residue_mean_complex_riemann
    (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)
    (step H : Input → ℕ) (c : Input → ℤ)
    (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (q : ℕ) (hq : 0 < q) (residue : Input → Option Empty → ZMod q)
    (hsize : ∀ j, q ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / S.value ≤ ε)
    (φ : Sample × (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ)) → ℂ)
    (hφm : Measurable φ) {Kφ : ℝ≥0}
    (hφ : ∀ sample, LipschitzWith Kφ (fun y => φ (sample, y)))
    (hφone : ∀ p, ‖φ p‖ ≤ 1) :
    let lower := fun (a : Active) (p : B a.val × Fin (degree a.val)) => (c ⟨a, p⟩ : ℝ) / S.value
    let width := fun (a : Active) (p : B a.val × Fin (degree a.val)) =>
      (step ⟨a, p⟩ : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleLiftLip B U basis S
    (∫ sample, ‖(∫ z, (containedProgressionResidueLaw activeB activeDegree (fun _ => S.value) H step c
        (fun _ => S.positive) (fun j => by have := hH j; omega) hsubset q hq residue
        (fun j => by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize j)).complexMean
        (fun v => φ (sample, (z, allocatedOriginalSampleLiftMap B U basis S (fun _ _ => 0) (fun _ _ => 1)
          sample (fun j => (v j none : ℝ) / S.value))))
          ∂canonicalZeroSpatialLaw (X := X) s root D W L) -
      ∫ y, φ (sample, y) ∂allocatedOriginalSampleForecastSource (X := X) (W := W) (L := L)
        B U basis S s root D lower width sample‖
        ∂allocatedCoefficientSource B U basis hR hσ S) ≤
      2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ j, (q : ℝ) / H j + K * ε) := by
  classical
  intro lower width K
  let μ := allocatedCoefficientSource B U basis hR hσ S
  let : IsProbabilityMeasure μ := allocatedCoefficientSource_probability B U basis hR hσ S
  let p := containedProgressionResidueLaw activeB activeDegree (fun _ => S.value) H step c
    (fun _ => S.positive) (fun j => by have := hH j; omega) hsubset q hq residue
    (fun j => by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize j)
  let input := fun (v : PrincipalIntegerTuples activeB activeDegree Empty (fun _ => S.value))
    (j : Input) => (v j none : ℝ) / S.value
  let actual := fun sample => ∫ z, p.complexMean (fun v =>
    φ (sample, (z, allocatedOriginalSampleLiftMap B U basis S (fun _ _ => 0) (fun _ _ => 1)
      sample (input v)))) ∂canonicalZeroSpatialLaw (X := X) s root D W L
  let forecast := fun sample => ∫ y, φ (sample, y)
    ∂allocatedOriginalSampleForecastSource (X := X) (W := W) (L := L)
      B U basis S s root D lower width sample
  let bound := 2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
    ∑ j, (q : ℝ) / H j + K * ε)
  have hactual : Measurable actual :=
    allocatedOriginalSampleFiniteExpectation_measurable B U basis S
      (fun _ _ => 0) (fun _ _ => 1) s root D hp hW hL p input φ hφm
  have hforecast : Measurable forecast :=
    allocatedOriginalSampleForecastExpectation_measurable B U basis S lower width
      s root D hp hW hL φ hφm hφone
  have herror : Measurable (fun sample => ‖actual sample - forecast sample‖) :=
    (hactual.sub hforecast).norm
  have hbound : ∀ᵐ sample ∂μ, ‖actual sample - forecast sample‖ ≤ bound :=
    allocatedOriginalSampleForecast_contained_residue_ae_complex_riemann
      B U basis hR hσ S s root D hp hW hL step H c hstep hH hδ hsubset hdense
      q hq residue hsize hsmall hε hmesh (fun sample y => φ (sample, y)) hφ
      (fun sample y => hφone (sample, y))
  have hi : Integrable (fun sample => ‖actual sample - forecast sample‖) μ := by
    apply Integrable.mono' (integrable_const bound) herror.aestronglyMeasurable
    filter_upwards [hbound] with sample hs
    simpa only [Real.norm_of_nonneg (norm_nonneg _)] using hs
  change (∫ sample, ‖actual sample - forecast sample‖ ∂μ) ≤ bound
  calc
    _ ≤ ∫ _sample, bound ∂μ := integral_mono_ae hi (integrable_const bound) hbound
    _ = bound := by simp only [integral_const, probReal_univ, one_smul]

end Erdos3.VectorPolynomial

end

end OAI
