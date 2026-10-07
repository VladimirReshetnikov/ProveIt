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

variable (hw : ∀ a p, δ ≤ width a p) (hl : ∀ a p, 0 ≤ lower a p)

variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
  (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
    (allocatedLayerWidths B U basis S j)
    (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))

local notation "density" => allocatedOriginalSampleForecastDensity (X := X)
  B U basis S s root D hp hW hL hB lower width sample

include hδ hw hl hs in

theorem allocatedOriginalSampleForecastDensity_continuous_of_supported
    (hroot : ∀ j, |(root j : ℝ)| ≤ 1 + W) :
    Continuous density := by
  have hr := allocatedSampleRestrictedProfileNoise_short_abs_le B U basis hR hσ S sample hs
  exact (allocatedFixedPathForecastDensity_cap_lipschitz (X := X)
    B short R σ s root D hp hW hL (fun j => (hR j).ne') hB lower width hamin hδ
    (fun a => unitProfilePrincipalLowerBound_le B a.val) hw hl (noise sample) hr
    zero_lt_one hroot (by simp only [Matrix.det_isEmpty, abs_one, le_refl])).2.continuous

include hδ hw hl hs in

theorem allocatedOriginalSampleForecastDensity_active_bound_two_of_supported
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    (y : Domain) (hne : density y ≠ 0) (a : Output) : |y.2 a| ≤ 2 := by
  have hr := allocatedSampleRestrictedProfileNoise_short_abs_le B U basis hR hσ S sample hs
  have hnorm : ‖y.2‖ ≤ 2 := by
    by_contra hn
    have hz := allocatedFixedPathLiftDensity_zero_off_ball B short R σ
      (fun j => (hR j).ne') hB lower width hwidth hamin hδ
      (fun a => unitProfilePrincipalLowerBound_le B a.val) hw hl (noise sample) hr y.2
      (lt_of_not_ge hn)
    apply hne
    change canonicalZeroSpatialJointDensity (X := X) s root D hp hW hL y.1 *
      allocatedFixedPathLiftDensity B short R σ hB lower width (noise sample) y.2 = 0
    rw [hz, mul_zero]
  have hcoord : |y.2 a| ≤ ‖y.2‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm y.2 a
  exact hcoord.trans hnorm

include hδ hw hl hs in
theorem allocatedOriginalSampleForecastDensity_active_bound_three_of_supported
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    (y : Domain) (hne : density y ≠ 0) (a : Output) : |y.2 a| ≤ 3 :=
  (allocatedOriginalSampleForecastDensity_active_bound_two_of_supported
    B U basis hR hσ S s root D hp hW hL hB lower width hδ hw hl sample hs hwidth y hne a).trans
      (by norm_num)

end Erdos3.VectorPolynomial

end

end OAI
