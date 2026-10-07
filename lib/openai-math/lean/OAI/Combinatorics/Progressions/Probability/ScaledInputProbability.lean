import OAI.Combinatorics.Progressions.Estimates.RealWeightPMF
import OAI.Combinatorics.Progressions.Estimates.SplitSmoothProductProfile

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Matrix BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

theorem scaledInputWeightSum_pos (f : (J → ℝ) × (I → ℝ) → ℝ) (S : I → ℝ) (T : J → ℝ)
    (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j) (hM : 0 < scaledInputMass f S T) :
    0 < scaledInputWeightSum f S T := by
  have hp : 0 < (∏ i, S i) * (∏ j, T j) :=
    mul_pos (Finset.prod_pos fun i _ => hS i) (Finset.prod_pos fun j _ => hT j)
  have h := mul_pos hM hp
  rwa [scaledInputMass, div_mul_cancel₀ _ hp.ne'] at h

noncomputable def scaledInputPMF (f : (J → ℝ) × (I → ℝ) → ℝ) (hf0 : ∀ p, 0 ≤ f p)
    (S : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j)
    {R : ℝ} (hsupport : ∀ p, R < ‖p‖ → f p = 0) (hM : 0 < scaledInputMass f S T) :
    PMF ((I → ℤ) × (J → ℤ)) :=
  realWeightPMF (scaledIntegerWeight f S T) (fun _ => hf0 _)
    (scaledIntegerWeight_summable f S T hS hT hsupport) (scaledInputWeightSum_pos f S T hS hT hM)

theorem scaledInputPMF_apply (f : (J → ℝ) × (I → ℝ) → ℝ) (hf0 : ∀ p, 0 ≤ f p)
    (S : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j)
    {R : ℝ} (hsupport : ∀ p, R < ‖p‖ → f p = 0) (hM : 0 < scaledInputMass f S T)
    (p : (I → ℤ) × (J → ℤ)) :
    (scaledInputPMF f hf0 S T hS hT hsupport hM p).toReal =
      scaledIntegerWeight f S T p / scaledInputWeightSum f S T :=
  realWeightPMF_apply _ _ _ _ p

noncomputable def integerImagePMF (A : Matrix I I ℤ) (B : Matrix I J ℤ)
    (f : (J → ℝ) × (I → ℝ) → ℝ) (hf0 : ∀ p, 0 ≤ f p)
    (S : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j)
    {R : ℝ} (hsupport : ∀ p, R < ‖p‖ → f p = 0) (hM : 0 < scaledInputMass f S T) :
    PMF (I → ℤ) :=
  (scaledInputPMF f hf0 S T hS hT hsupport hM).map (fun p => A *ᵥ p.1 + B *ᵥ p.2)

theorem integerImagePMF_apply (A : Matrix I I ℤ) (B : Matrix I J ℤ)
    (f : (J → ℝ) × (I → ℝ) → ℝ) (hf0 : ∀ p, 0 ≤ f p)
    (S : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j)
    {R : ℝ} (hsupport : ∀ p, R < ‖p‖ → f p = 0) (hM : 0 < scaledInputMass f S T) (v : I → ℤ) :
    (integerImagePMF A B f hf0 S T hS hT hsupport hM v).toReal =
      (∑' p : {p : (I → ℤ) × (J → ℤ) // A *ᵥ p.1 + B *ᵥ p.2 = v},
        scaledIntegerWeight f S T p.val) / scaledInputWeightSum f S T :=
  realWeightPMF_map_fiber _ _ _ _ _ v

theorem integerImagePMF_scaled (A : Matrix I I ℤ) (B : Matrix I J ℤ)
    (f : (J → ℝ) × (I → ℝ) → ℝ) (hf0 : ∀ p, 0 ≤ f p)
    (S P : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j)
    {R : ℝ} (hsupport : ∀ p, R < ‖p‖ → f p = 0) (hM : 0 < scaledInputMass f S T) (v : I → ℤ) :
    (∏ i, P i) * (integerImagePMF A B f hf0 S T hS hT hsupport hM v).toReal =
      scaledIntegerFiberOutputMass A B S P T f v / scaledInputMass f S T := by
  rw [integerImagePMF_apply]
  have hSp : (∏ i, S i) ≠ 0 := (Finset.prod_pos fun i _ => hS i).ne'
  have hTp : (∏ j, T j) ≠ 0 := (Finset.prod_pos fun j _ => hT j).ne'
  have hZ : (∑' p, scaledIntegerWeight f S T p) ≠ 0 :=
    (scaledInputWeightSum_pos f S T hS hT hM).ne'
  unfold scaledIntegerFiberOutputMass scaledInputMass scaledInputWeightSum
  field_simp [hSp, hTp, hZ]

end Erdos3

end

end OAI
