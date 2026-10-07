import OAI.Combinatorics.Progressions.Lattices.AllocatedFixedPathSlicedKernelResidueRiemann

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
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

variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (u : PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))

include hR hσ in
theorem allocatedOriginalSampleFullSlice_sliced_residue_complex_riemann (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    {t : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
    (step H M : Input → ℕ) (c : Input → ℤ)
    (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (modulus : Input → Option Empty → ℕ) (residue : ∀ j i, ZMod (modulus j i))
    (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
    (hsize : ∀ j, M j ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((M j : ℝ) / H j) < 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / S.value ≤ ε)
    (φ : (Output → ℝ) → ℂ) {Kφ : ℝ≥0}
    (hφ : LipschitzWith Kφ φ) (hφone : ∀ y, ‖φ y‖ ≤ 1) :
    let lower := fun (a : Active) (p : B a.val × Fin (degree a.val)) => (c ⟨a, p⟩ : ℝ) / S.value
    let width := fun (a : Active) (p : B a.val × Fin (degree a.val)) =>
      (step ⟨a, p⟩ : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleFullSliceLip B U basis S t
    ‖(FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights Empty (H j) (M j)
        (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j)
        (by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize j))).complexMean
        (fun z => φ (allocatedOriginalSampleFullSliceMap B U basis S x u (fun _ _ => 0) (fun _ _ => 1)
          sample (fun j => ((c j : ℝ) + (step j : ℝ) * (z j none : ℝ)) / S.value))) -
      ∫ y, φ (allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample y)
        ∂unitBoxMeasure Input‖ ≤
      2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ j, (M j : ℝ) / H j + K * ε) := by
  classical
  intro lower width K
  let p := FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights Empty (H j) (M j)
    (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j)
    (by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize j))
  let F := allocatedOriginalSampleFullSliceMap B U basis S x u (fun _ _ => 0) (fun _ _ => 1) sample
  let f := fun (z : ∀ j : Input, IntegerScalarCubeBox Empty (H j)) => φ (F (fun j => ((c j : ℝ) + (step j : ℝ) * (z j none : ℝ)) / S.value))
  let g := fun y => φ (allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample y)
  have hig : Integrable g (unitBoxMeasure Input) :=
    ⟨(hφ.continuous.measurable.comp
      (allocatedOriginalSampleFullSliceMap_measurable B U basis S x u lower width sample)).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall (fun y => hφone _))⟩
  have hφre : LipschitzWith Kφ (fun y => (φ y).re) := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    rw [Real.dist_eq, ← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans (by simpa only [dist_eq_norm] using hφ.dist_le_mul v w)
  have hφim : LipschitzWith Kφ (fun y => (φ y).im) := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    rw [Real.dist_eq, ← Complex.sub_im]
    exact (Complex.abs_im_le_norm _).trans (by simpa only [dist_eq_norm] using hφ.dist_le_mul v w)
  have hre := allocatedOriginalSampleFullSlice_residue_riemann B U basis hR hσ S x u
    sample hs ht hσbound step H M c hstep hH hδ hsubset hdense modulus residue hm hmM
    hsize hsmall hε hmesh (fun y => (φ y).re) hφre
    (fun y => (Complex.abs_re_le_norm _).trans (hφone y))
  have him := allocatedOriginalSampleFullSlice_residue_riemann B U basis hR hσ S x u
    sample hs ht hσbound step H M c hstep hH hδ hsubset hdense modulus residue hm hmM
    hsize hsmall hε hmesh (fun y => (φ y).im) hφim
    (fun y => (Complex.abs_im_le_norm _).trans (hφone y))
  have hgre : (∫ y, g y ∂unitBoxMeasure Input).re = ∫ y, (g y).re ∂unitBoxMeasure Input := by
    simpa only [RCLike.re_eq_complex_re] using (integral_re hig).symm
  have hgim : (∫ y, g y ∂unitBoxMeasure Input).im = ∫ y, (g y).im ∂unitBoxMeasure Input := by
    simpa only [RCLike.im_eq_complex_im] using (integral_im hig).symm
  change ‖p.complexMean f - ∫ y, g y ∂unitBoxMeasure Input‖ ≤ _
  calc
    _ ≤ |(p.complexMean f - ∫ y, g y ∂unitBoxMeasure Input).re| +
        |(p.complexMean f - ∫ y, g y ∂unitBoxMeasure Input).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ j, (M j : ℝ) / H j + K * ε) +
        ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ j, (M j : ℝ) / H j + K * ε) := by
      apply add_le_add
      · rw [Complex.sub_re, FiniteProbabilityWeights.complexMean_re, hgre]
        exact hre
      · rw [Complex.sub_im, FiniteProbabilityWeights.complexMean_im, hgim]
        exact him
    _ = _ := by ring

include hR hσ in
theorem allocatedOriginalSample_sliced_residue_perturbed_riemann (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    {t : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
    (step H M : Input → ℕ) (c : Input → ℤ)
    (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (modulus : Input → Option Empty → ℕ) (residue : ∀ j i, ZMod (modulus j i))
    (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
    (hsize : ∀ j, M j ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((M j : ℝ) / H j) < 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / S.value ≤ ε)
    (hδone : δ ≤ 1) (b : ∀ a : Active, B a.val)
    {η : ℝ} (hη : 0 < η)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (htail : |t| * polynomialMassC2Budget (Fintype.card Input) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card Input) (Fintype.card Active) m 1
        (unitProfilePrincipalLowerBound B) (δ / 2) A η)
    (φ : (Output → ℝ) → ℂ) {Kφ : ℝ≥0}
    (hφ : LipschitzWith Kφ φ) (hφone : ∀ y, ‖φ y‖ ≤ 1) :
    let lower := fun (a : Active) (p : B a.val × Fin (degree a.val)) => (c ⟨a, p⟩ : ℝ) / S.value
    let width := fun (a : Active) (p : B a.val × Fin (degree a.val)) =>
      (step ⟨a, p⟩ : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleFullSliceLip B U basis S t
    ‖(FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights Empty (H j) (M j)
        (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j)
        (by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize j))).complexMean
        (fun z => φ (allocatedOriginalSampleFullSliceMap B U basis S x u (fun _ _ => 0) (fun _ _ => 1)
          sample (fun j => ((c j : ℝ) + (step j : ℝ) * (z j none : ℝ)) / S.value))) -
      ∫ y, φ (allocatedOriginalSampleLiftMap B U basis S lower width sample y)
        ∂unitBoxMeasure Input‖ ≤
      2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ j, (M j : ℝ) / H j + K * ε) + 2 * η := by
  classical
  intro lower width K
  have hg (a : Active) (p : B a.val × Fin (degree a.val)) :=
    progression_slice_endpoint_geometry (c ⟨a,p⟩) S.positive (hstep _) (hH _)
      hδ (hsubset _) (hdense _)
  have hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1 := fun a p => (hg a p).2.2.1
  have hp := allocatedOriginalSample_slice_complex_perturbation B U basis hR hσ S x u lower width
    sample hs hwidth b (δ := δ / 2) (half_pos hδ) (by linarith) hη
    (fun a i => (hg a (b a, i)).2.1) (fun a i => (hg a (b a, i)).1)
    A hA ht hσbound htail φ hφ.continuous.measurable hφone
  have hq := allocatedOriginalSampleFullSlice_sliced_residue_complex_riemann
    B U basis hR hσ S x u sample hs ht hσbound step H M c hstep hH hδ hsubset hdense
    modulus residue hm hmM hsize hsmall hε hmesh φ hφ hφone
  exact (norm_sub_le_norm_sub_add_norm_sub _
    (∫ y, φ (allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample y)
      ∂unitBoxMeasure Input) _).trans (add_le_add hq ((norm_sub_rev _ _).trans_le hp))

end Erdos3.VectorPolynomial

end

end OAI
