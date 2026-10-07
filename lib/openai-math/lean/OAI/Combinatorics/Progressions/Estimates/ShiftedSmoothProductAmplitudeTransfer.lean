import OAI.Combinatorics.Progressions.Geometry.NormalizedSpatialAmplitudeShift
import OAI.Combinatorics.Progressions.Probability.ShiftedSmoothProductLaw

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem shiftedSmoothProductPMF_translation_test_le {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hS1 : ∀ i, 1 ≤ S i)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ i, 1 / S i ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card I *
      ((Fintype.card I : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    (φ : (I → ℤ) → ℂ) (hφ : ∀ x, ‖φ x‖ ≤ 1) (v : I → ℤ) :
    ‖(∑' x, ((shiftedSmoothProductPMF a S hS hZ x).toReal : ℂ) * φ (x + v)) -
      ∑' x, ((shiftedSmoothProductPMF a S hS hZ x).toReal : ℂ) * φ x‖ ≤
        4 * (3 : ℝ) ^ Fintype.card I *
          (((Fintype.card I : ℝ) * probabilityProfileLipschitz) * ‖rectangularLatticePoint 0 S v‖) := by
  have ht := normalized_rectangular_translation_test_le (smoothProductProfile I)
    (smoothProductProfile_lipschitz I) a S hS1 zero_le_one
    (smoothProductProfile_zero_outside I)
    (shiftedSmoothProductMass_lower a S hS hδ hδ1 hmesh hsmall) φ hφ v
  simpa only [shiftedSmoothProductPMF_toReal, NNReal.coe_mul, NNReal.coe_natCast,
    show 2 * (1 : ℝ) + 1 = 3 by norm_num] using ht

theorem shiftedSmoothProductPMF_shift_transfer {I X : Type*}
    [Fintype I] [Fintype X] [Nonempty X]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hS1 : ∀ i, 1 ≤ S i)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ i, 1 / S i ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card I *
      ((Fintype.card I : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    (shift : X → I → ℤ) {r B : ℝ}
    (hshift : ∀ u, ‖rectangularLatticePoint 0 S (shift u)‖ ≤ r)
    (f : (I → ℤ) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (hlocal : ∀ x, ‖𝔼 u, f (x + shift u)‖ ≤ B) :
    ‖∑' x, ((shiftedSmoothProductPMF a S hS hZ x).toReal : ℂ) * f x‖ ≤
      4 * (3 : ℝ) ^ Fintype.card I * ((Fintype.card I : ℝ) * probabilityProfileLipschitz) * r + B := by
  apply finite_probability_shift_transfer (fun x => (shiftedSmoothProductPMF a S hS hZ x).toReal)
    (rectangularWeightIndices a S 1) (shiftedSmoothProductPMF_toReal_zero_off a S hS hZ)
    (fun _ => ENNReal.toReal_nonneg) (shiftedSmoothProductPMF_toReal_sum a S hS hZ) shift f _ hlocal
  intro u
  apply (shiftedSmoothProductPMF_translation_test_le a S hS hZ hS1 hδ hδ1 hmesh hsmall f hf (shift u)).trans
  calc
    _ ≤ 4 * (3 : ℝ) ^ Fintype.card I *
        (((Fintype.card I : ℝ) * probabilityProfileLipschitz) * r) := by
      gcongr
      exact hshift u
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators NNReal

theorem shiftedSmoothProductPMF_shift_transfer_amplitude {I X : Type*}
    [Fintype I] [Fintype X] [Nonempty X]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hS1 : ∀ i, 1 ≤ S i)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ i, 1 / S i ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card I *
      ((Fintype.card I : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    (shift : X → I → ℤ) {r β : ℝ}
    (hshift : ∀ u, ‖rectangularLatticePoint 0 S (shift u)‖ ≤ r)
    (f : (I → ℤ) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (hlocal : ∀ x, ‖𝔼 u, f (x + shift u)‖ ≤ β)
    (F : (I → ℤ) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    {η : ℝ} (hvariation : ∀ x u, ‖F (x + shift u) - F x‖ ≤ η) :
    ‖∑' x, ((shiftedSmoothProductPMF a S hS hZ x).toReal : ℂ) * (F x * f x)‖ ≤
      4 * (3 : ℝ) ^ Fintype.card I * ((Fintype.card I : ℝ) * probabilityProfileLipschitz) * r + η + β := by
  have hproduct (x) : ‖F x * f x‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul (hF x) (hf x) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hlocalProduct (x) : ‖𝔼 u, F (x + shift u) * f (x + shift u)‖ ≤ η + β :=
    norm_local_average_amplitude_le (fun u => x + shift u) f F x hf (hF x) (hvariation x) (hlocal x)
  simpa only [add_assoc] using shiftedSmoothProductPMF_shift_transfer a S hS hZ hS1
    hδ hδ1 hmesh hsmall shift hshift (fun x => F x * f x) hproduct hlocalProduct

theorem shiftedSmoothProductPMF_shift_transfer_lipschitz_amplitude {I X : Type*}
    [Fintype I] [Fintype X] [Nonempty X]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hS1 : ∀ i, 1 ≤ S i)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ i, 1 / S i ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card I *
      ((Fintype.card I : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    (shift : X → I → ℤ) {r β : ℝ}
    (hshift : ∀ u, ‖rectangularLatticePoint 0 S (shift u)‖ ≤ r)
    (f : (I → ℤ) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (hlocal : ∀ x, ‖𝔼 u, f (x + shift u)‖ ≤ β)
    (F : (I → ℝ) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    {Lip : ℝ≥0} (hLip : LipschitzWith Lip F) :
    ‖∑' x, ((shiftedSmoothProductPMF a S hS hZ x).toReal : ℂ) *
      (F (rectangularLatticePoint a S x) * f x)‖ ≤
      4 * (3 : ℝ) ^ Fintype.card I * ((Fintype.card I : ℝ) * probabilityProfileLipschitz) * r +
        (Lip : ℝ) * r + β := by
  exact shiftedSmoothProductPMF_shift_transfer_amplitude a S hS hZ hS1 hδ hδ1 hmesh hsmall
    shift hshift f hf hlocal (fun x => F (rectangularLatticePoint a S x)) (fun _ => hF _)
    (fun x u => normalizedSpatialAmplitude_shift_le_of_norm_le F hLip a S x (shift u) (hshift u))

end Erdos3

end

end OAI
