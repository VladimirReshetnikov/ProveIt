import OAI.Combinatorics.Progressions.Lattices.AllocatedChildActiveResidueComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [DecidableEq G] [Fintype X]
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
theorem allocatedFixedPath_sliced_joint_residue_comparison
    (z : Option G × X → ℝ) (hz : ∀ g x, |z (some g, x)| ≤ 1)
    (HG : G → ℕ) (hHG : ∀ g, 0 < HG g) (cG : G → ℤ)
    (stepG : ℕ) (hstepG : 0 < stepG)
    (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
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
    let kernel := FiniteProbabilityWeights.pi (fun g => integerScalarCubeWeights Empty (HG g) (hHG g))
    let active := FiniteProbabilityWeights.pi (fun j : Input => integerScalarCubeWeights Empty (H j)
      (by have := hH j; omega))
    let embed := fun (x : ∀ g, IntegerScalarCubeBox Empty (HG g)) g =>
      containedProgressionCubeMap Empty S.value (HG g) stepG (cG g) S.positive (hcontainedG g) (x g)
    ‖kernel.complexMean (fun x => active.complexMean (fun v =>
        φ (fun g => ((cG g + (stepG : ℤ) * (x g none : ℤ) : ℤ) : ZMod q))
          (fun j => ((c j + (step j : ℤ) * (v j none : ℤ) : ℤ) : ZMod q))
          (fixedSpatialKernelMap budget (S.value : ℝ) z
            (fun g => ((cG g : ℝ) + (stepG : ℝ) * (x g none : ℝ)) / S.value),
            allocatedOriginalSampleFullSliceMap B U basis S (embed x) u (fun _ _ => 0) (fun _ _ => 1)
              sample (fun j => ((c j : ℝ) + (step j : ℝ) * (v j none : ℝ)) / S.value)))) -
      (FiniteProbabilityWeights.uniform (Input → ZMod q)).complexMean (fun rA =>
        (FiniteProbabilityWeights.uniform (G → ZMod q)).complexMean (fun rG =>
          ∫ k, ∫ v, φ (fun g => (cG g : ZMod q) + (stepG : ZMod q) * rG g)
            (fun j => (c j : ZMod q) + (step j : ZMod q) * rA j)
            (fixedSpatialKernelMap budget (S.value : ℝ) z
              (fun g => ((cG g : ℝ) + (stepG : ℝ) * ((HG g - 1 : ℕ) : ℝ) * k g) / S.value),
              allocatedOriginalSampleLiftMap B U basis S lower width sample v)
            ∂unitBoxMeasure Input ∂unitBoxMeasure G))‖ ≤
      ((∑ j, (q : ℝ) / H j) +
        (2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
          ∑ j, (q : ℝ) / H j + K * ε) + 2 * η)) +
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + Kφ) + Kφ) * ∑ g, (q : ℝ) / HG g := by
  classical
  intro lower width K kernel active embed
  let residues := FiniteProbabilityWeights.uniform (Input → ZMod q)
  let EA := (∑ j, (q : ℝ) / H j) +
    (2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
      ∑ j, (q : ℝ) / H j + K * ε) + 2 * η)
  let EG := (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + Kφ) + Kφ) *
    ∑ g, (q : ℝ) / HG g
  let rkernel := fun (x : ∀ g, IntegerScalarCubeBox Empty (HG g)) g =>
    ((cG g + (stepG : ℤ) * (x g none : ℤ) : ℤ) : ZMod q)
  let point := fun (x : ∀ g, IntegerScalarCubeBox Empty (HG g)) =>
    fixedSpatialKernelMap budget (S.value : ℝ) z
      (fun g => ((cG g : ℝ) + (stepG : ℝ) * (x g none : ℝ)) / S.value)
  let source := fun (x : ∀ g, IntegerScalarCubeBox Empty (HG g)) =>
    active.complexMean (fun v =>
      φ (rkernel x) (fun j => ((c j + (step j : ℤ) * (v j none : ℤ) : ℤ) : ZMod q))
        (point x, allocatedOriginalSampleFullSliceMap B U basis S (embed x) u
          (fun _ _ => 0) (fun _ _ => 1) sample
          (fun j => ((c j : ℝ) + (step j : ℝ) * (v j none : ℝ)) / S.value)))
  let reference := fun (x : ∀ g, IntegerScalarCubeBox Empty (HG g)) (rA : Input → ZMod q) =>
    ∫ v, φ (rkernel x) (fun j => (c j : ZMod q) + (step j : ZMod q) * rA j)
      (point x, allocatedOriginalSampleLiftMap B U basis S lower width sample v) ∂unitBoxMeasure Input
  have hfirst0 (x : ∀ g, IntegerScalarCubeBox Empty (HG g)) :
      ‖source x - residues.complexMean (reference x)‖ ≤ EA := by
    let test := fun (rA : Input → ZMod q) (y : Output → ℝ) => φ (rkernel x) rA (point x, y)
    have htest (rA : Input → ZMod q) : LipschitzWith Kφ (test rA) := by
      apply LipschitzWith.of_dist_le_mul
      intro v w
      simpa only [test, Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using
        (hφ (rkernel x) rA).dist_le_mul (point x, v) (point x, w)
    simpa only [source, reference, EA, K, lower, width, active, test, residues,
      FiniteProbabilityWeights.uniform_complexMean] using
      allocatedOriginalSample_sliced_affine_residue_comparison B U basis hR hσ S (embed x) u
        sample hs ht hσbound step H c hstep hH hδ hsubset hdense q hsize hsmall hε hmesh
        hδone b hη A hA htail test htest (fun rA y => hφone _ _ _)
  have hfirst := (kernel.norm_complexMean_sub_le source
    (fun x => residues.complexMean (reference x)) (fun _ => EA)
      (fun x _ => hfirst0 x)).trans_eq (kernel.mean_const EA)
  have hlast := (residues.norm_complexMean_sub_le
    (fun rA => kernel.complexMean (fun x => reference x rA))
    (fun rA => (FiniteProbabilityWeights.uniform (G → ZMod q)).complexMean (fun rG =>
      ∫ k, ∫ v, φ (fun g => (cG g : ZMod q) + (stepG : ZMod q) * rG g)
        (fun j => (c j : ZMod q) + (step j : ZMod q) * rA j)
        (fixedSpatialKernelMap budget (S.value : ℝ) z
          (fun g => ((cG g : ℝ) + (stepG : ℝ) * ((HG g - 1 : ℕ) : ℝ) * k g) / S.value),
          allocatedOriginalSampleLiftMap B U basis S lower width sample v)
        ∂unitBoxMeasure Input ∂unitBoxMeasure G)) (fun _ => EG) (fun rA _ =>
      allocatedFixedPath_sliced_kernel_residue_riemann B U basis S z hz sample lower width
        HG hHG cG stepG hstepG hcontainedG q hsizeG hsmallG
        (fun rG => φ rG (fun j => (c j : ZMod q) + (step j : ZMod q) * rA j))
        (fun rG => hφ rG _) (fun rG y => hφone rG _ y))).trans_eq (residues.mean_const EG)
  rw [← FiniteProbabilityWeights.complexMean_commute kernel residues] at hlast
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hfirst hlast)

end Erdos3.VectorPolynomial

end

end OAI
