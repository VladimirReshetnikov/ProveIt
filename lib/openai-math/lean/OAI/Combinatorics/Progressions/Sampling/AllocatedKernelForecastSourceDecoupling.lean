import OAI.Combinatorics.Progressions.Lattices.AllocatedKernelCanonicalResidueComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [DecidableEq G] [Fintype X]
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
local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)
local notation "Domain" => (Spatial × (Output → ℝ))
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)

variable (lower width : ∀ a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

omit [DecidableEq G] in

theorem allocatedOriginalSampleForecastPartial_lipschitz
    (sample : Sample) (φ : Domain → ℂ) {K : ℝ≥0}
    (hφ : LipschitzWith K φ) (hbound : ∀ y, ‖φ y‖ ≤ 1) :
    LipschitzWith K (fun z : Spatial =>
      ∫ v, φ (z, allocatedOriginalSampleLiftMap B U basis S lower width sample v)
        ∂unitBoxMeasure Input) := by
  let F := allocatedOriginalSampleLiftMap B U basis S lower width sample
  have hi (z : Spatial) : Integrable (fun v => φ (z, F v)) (unitBoxMeasure Input) :=
    ⟨(hφ.continuous.measurable.comp (measurable_const.prodMk
      (allocatedOriginalSampleLiftMap_fixed_measurable B U basis S lower width sample))).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall (fun v => hbound _))⟩
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [dist_eq_norm, ← integral_sub (hi z) (hi w)]
  have hb : ∀ᵐ v ∂unitBoxMeasure Input,
      ‖φ (z, F v) - φ (w, F v)‖ ≤ (K : ℝ) * dist z w := by
    apply Filter.Eventually.of_forall
    intro v
    have hd := hφ.dist_le_mul (z, F v) (w, F v)
    rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg] at hd
    simpa only [dist_eq_norm] using hd
  simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hb

theorem allocatedKernel_forecastSource_residue_decoupling
    (s : Empty ↪ G) (sample : Sample)
    (q : ℕ) [NeZero q] (hsize : q ≤ S.value)
    (hsmall : scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / S.value) < 1)
    (φ : (G → ZMod q) → Domain → ℂ) {K : ℝ≥0}
    (hφ : ∀ r, LipschitzWith K (φ r)) (hbound : ∀ r y, ‖φ r y‖ ≤ 1) :
    ‖(FiniteProbabilityWeights.pi (fun _ : G => integerScalarCubeWeights Empty S.value S.positive)).complexMean
        (fun x => ∫ y, φ (fun g => ((x g none : ℤ) : ZMod q)) y
          ∂allocatedOriginalSampleForecastSource (X := X) (W := budget) (L := (S.value : ℝ))
            B U basis S s (fun g => (x g none : ℤ)) (scalarCubeDifferenceMatrix x)
            lower width sample) -
      𝔼 r : G → ZMod q,
        (FiniteProbabilityWeights.pi (fun _ : G => integerScalarCubeWeights Empty S.value S.positive)).complexMean
          (fun x => ∫ y, φ r y
            ∂allocatedOriginalSampleForecastSource (X := X) (W := budget) (L := (S.value : ℝ))
              B U basis S s (fun g => (x g none : ℤ)) (scalarCubeDifferenceMatrix x)
              lower width sample)‖ ≤
      2 * ((1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + K)) *
        (Fintype.card G * ((q : ℝ) / S.value))) := by
  classical
  let Ψ := fun (r : G → ZMod q) (z : Spatial) =>
    ∫ v, φ r (z, allocatedOriginalSampleLiftMap B U basis S lower width sample v)
      ∂unitBoxMeasure Input
  have hΨ (r : G → ZMod q) : LipschitzWith K (Ψ r) :=
    allocatedOriginalSampleForecastPartial_lipschitz B U basis S lower width sample
      (φ r) (hφ r) (hbound r)
  have hb (r : G → ZMod q) (z : Spatial) : ‖Ψ r z‖ ≤ 1 :=
    allocatedOriginalSampleForecastPartial_norm_le B U basis S lower width sample
      (φ r) (hbound r) z
  have hid (x : G → IntegerScalarCubeBox Empty S.value) (r : G → ZMod q) :
      (∫ y, φ r y
        ∂allocatedOriginalSampleForecastSource (X := X) (W := budget) (L := (S.value : ℝ))
          B U basis S s (fun g => (x g none : ℤ)) (scalarCubeDifferenceMatrix x)
          lower width sample) =
        ∫ z, Ψ r z ∂canonicalZeroSpatialLaw s (fun g => (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) budget (S.value : ℝ) := by
    have hp : (selectedSpatialPivot (fun g => (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) s).det ≠ 0 := by
      simp only [selectedSpatialPivot, rootDifferenceMatrix_det, Matrix.det_isEmpty, ne_eq,
        Int.one_ne_zero, not_false_eq_true]
    exact allocatedOriginalSampleForecastSource_integral B U basis S lower width
      s (fun g => (x g none : ℤ)) (scalarCubeDifferenceMatrix x) hp
      (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0))
      (by exact_mod_cast S.positive : (0 : ℝ) < S.value)
      sample (φ r) (hφ r).continuous.measurable (hbound r)
  simp_rw [hid]
  exact allocatedKernel_canonical_residue_decoupling B U basis S s q hsize hsmall Ψ hΨ hb

end Erdos3.VectorPolynomial

end

end OAI
