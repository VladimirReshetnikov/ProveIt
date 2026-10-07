import OAI.Combinatorics.Progressions.Sampling.AllocatedOriginalSampleForecastMeanRiemann

namespace OAI

section

namespace Erdos3
open MeasureTheory

theorem forecast_real_integral_error_transport {Y : Type*} [MeasurableSpace Y]
    {μ ν : Measure Y} (h : μ = ν) (φ : Y → ℝ) {a ε : ℝ}
    (ha : |a - ∫ y, φ y ∂μ| ≤ ε) : |a - ∫ y, φ y ∂ν| ≤ ε := by
  cases h
  exact ha

theorem forecast_complex_integral_error_transport {Y : Type*} [MeasurableSpace Y]
    {μ ν : Measure Y} (h : μ = ν) (φ : Y → ℂ) {a : ℂ} {ε : ℝ}
    (ha : ‖a - ∫ y, φ y ∂μ‖ ≤ ε) : ‖a - ∫ y, φ y ∂ν‖ ≤ ε := by
  cases h
  exact ha

end Erdos3

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

theorem allocatedOriginalSampleForecastDensity_contained_residue_riemann
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
      ∫ y, φ y ∂realDensityMeasure volume (allocatedOriginalSampleForecastDensity (X := X)
        B U basis S s root D hp hW hL hB lower width sample)| ≤
      (2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ j, (q : ℝ) / H j + K * ε := by
  classical
  intro lower width K
  have he := allocatedOriginalSampleForecastSource_progression_density (X := X) B U basis hR hσ S
    s root D hp hW hL hB hroot sample hs step H c hstep hH hδ hsubset hdense
  have hc := allocatedOriginalSampleForecast_contained_residue_riemann B U basis hR hσ S
    s root D hp hW hL sample hs step H c hstep hH hδ hsubset hdense
    q hq residue hsize hsmall hε hmesh φ hφ hφone
  exact forecast_real_integral_error_transport he φ hc

theorem allocatedOriginalSampleForecastDensity_contained_residue_complex_riemann
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
      ∫ y, φ y ∂realDensityMeasure volume (allocatedOriginalSampleForecastDensity (X := X)
        B U basis S s root D hp hW hL hB lower width sample)‖ ≤
      2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ j, (q : ℝ) / H j + K * ε) := by
  classical
  intro lower width K
  have he := allocatedOriginalSampleForecastSource_progression_density (X := X) B U basis hR hσ S
    s root D hp hW hL hB hroot sample hs step H c hstep hH hδ hsubset hdense
  have hc := allocatedOriginalSampleForecast_contained_residue_complex_riemann B U basis hR hσ S
    s root D hp hW hL sample hs step H c hstep hH hδ hsubset hdense
    q hq residue hsize hsmall hε hmesh φ hφ hφone
  exact forecast_complex_integral_error_transport he φ hc

end Erdos3.VectorPolynomial

end

end OAI
