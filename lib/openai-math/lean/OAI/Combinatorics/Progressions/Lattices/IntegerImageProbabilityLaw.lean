import OAI.Combinatorics.Progressions.Estimates.PointwiseNormalization
import OAI.Combinatorics.Progressions.Probability.PivotDensityCap
import OAI.Combinatorics.Progressions.Probability.ScaledInputProbability

namespace OAI


namespace Erdos3

open MeasureTheory
open scoped Matrix NNReal BigOperators

noncomputable def normalizedIntegerFiberOutputMass {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (S P : I → ℝ) (T : J → ℝ)
    (f : (J → ℝ) × (I → ℝ) → ℝ) (v : I → ℤ) : ℝ :=
  scaledIntegerFiberOutputMass A B S P T f v / scaledInputMass f S T

noncomputable def normalizedFiberErrorConstant (j d : ℕ) (G U V R H : ℝ) (K : ℝ≥0) : ℝ :=
  2 * integerFiberErrorConstant j d G U V R K +
    2 * (G * (j.factorial * U ^ j) * H * (2 * R) ^ d) * ((2 * R + 2) ^ (j + d) * K)

theorem normalizedIntegerFiberOutputMass_pmf {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (f : (J → ℝ) × (I → ℝ) → ℝ)
    (hf0 : ∀ p, 0 ≤ f p) (S P : I → ℝ) (T : J → ℝ)
    (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j) {R : ℝ}
    (hsupport : ∀ p, R < ‖p‖ → f p = 0) (hM : 0 < scaledInputMass f S T) (v : I → ℤ) :
    normalizedIntegerFiberOutputMass A B S P T f v =
      (∏ i, P i) * (integerImagePMF A B f hf0 S T hS hT hsupport hM v).toReal :=
  (integerImagePMF_scaled A B f hf0 S P T hS hT hsupport hM v).symm

theorem normalizedIntegerFiber_uniform_error {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (v : I → ℤ) (hv : v ∈ pivotFullImage A B) {m : ℤ} (hm : 0 < m) (hdiv : A.det ∣ m)
    (S P : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) (hT : ∀ j, 0 < T j)
    (f : (J → ℝ) × (I → ℝ) → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    {R δ G U V H : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hH : 0 ≤ H)
    (hmeshS : ∀ i, 1 / S i ≤ δ) (hmeshT : ∀ j, (m : ℝ) / T j ≤ δ)
    (hsupport : ∀ p, R < ‖p‖ → f p = 0) (hmass : (∫ p, f p) = 1)
    (hsmall : (2 * R + 2) ^ (Fintype.card I + Fintype.card J) * K * δ ≤ 1 / 2)
    (hbound : ∀ p, ‖f p‖ ≤ H)
    (hindex : ((pivotFullImage A B).toAddSubgroup.index : ℝ) ≤ G)
    (hinv : ‖(normalizedPivotEquiv A hA S P hS hP).symm.toContinuousLinearMap‖ ≤ U)
    (hcol : ‖matrixSupCLM (normalizedIntegerColumns B T P)‖ ≤ V) :
    0 < scaledInputMass f S T ∧
      |normalizedIntegerFiberOutputMass A B S P T f v -
        ((pivotFullImage A B).toAddSubgroup.index : ℝ) *
          normalizedFiberDensity A hA B S P T hS hP f (fun i => (v i : ℝ) / P i)| ≤
      normalizedFiberErrorConstant (Fintype.card I) (Fintype.card J) G U V R H K * δ := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show (1 : ℤ) ≤ m by omega)
  have hmeshT' (j) : 1 / T j ≤ δ :=
    (div_le_div_of_nonneg_right hm1 (hT j).le).trans (hmeshT j)
  have hM := (scaledInputMass_bounds f hf S T hS hT hR hδ hδ1 hmeshS hmeshT' hsupport hmass hsmall).1
  have hMpos : 0 < scaledInputMass f S T := by linarith
  refine ⟨hMpos, ?_⟩
  have hmassError := scaledInputMass_error f hf S T hS hT hR hδ hδ1 hmeshS hmeshT' hsupport
  rw [hmass] at hmassError
  have herror := integerFiber_uniform_quadrature A hA B v hv hm hdiv S P T hS hP hT f hf
    hR hδ hδ1 hmeshT hsupport hindex hinv hcol
  have hcapDensity := pivotOutputDensity_abs_le_uniform (normalizedPivotEquiv A hA S P hS hP)
    (matrixSupCLM (normalizedIntegerColumns B T P)) f hR hH hsupport hbound hinv
    (fun i => (v i : ℝ) / P i)
  have hG : 0 ≤ G := (Nat.cast_nonneg _).trans hindex
  have hcap : |((pivotFullImage A B).toAddSubgroup.index : ℝ) *
      normalizedFiberDensity A hA B S P T hS hP f (fun i => (v i : ℝ) / P i)| ≤
      G * ((Fintype.card I).factorial * U ^ Fintype.card I) * H * (2 * R) ^ Fintype.card J := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    exact (mul_le_mul hindex hcapDensity (abs_nonneg _) hG).trans_eq (by ring)
  have h := pointwise_normalization_error hM herror hmassError hcap
  exact h.trans_eq (by unfold normalizedFiberErrorConstant; ring)

end Erdos3


namespace Erdos3

open MeasureTheory
open scoped Matrix

variable {I J : Type*} [Fintype I] [Fintype J]

theorem integerImagePMF_measure_map (A : Matrix I I ℤ) (B : Matrix I J ℤ)
    (f : (J → ℝ) × (I → ℝ) → ℝ) (hf0 : ∀ p, 0 ≤ f p)
    (S : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j)
    {R : ℝ} (hsupport : ∀ p, R < ‖p‖ → f p = 0) (hM : 0 < scaledInputMass f S T) :
    (scaledInputPMF f hf0 S T hS hT hsupport hM).toMeasure.map
      (fun p => A *ᵥ p.1 + B *ᵥ p.2) =
        (integerImagePMF A B f hf0 S T hS hT hsupport hM).toMeasure :=
  PMF.toMeasure_map (fun p : (I → ℤ) × (J → ℤ) => A *ᵥ p.1 + B *ᵥ p.2)
    _ (measurable_of_countable _)

theorem integerImagePMF_singleton (A : Matrix I I ℤ) (B : Matrix I J ℤ)
    (f : (J → ℝ) × (I → ℝ) → ℝ) (hf0 : ∀ p, 0 ≤ f p)
    (S : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j)
    {R : ℝ} (hsupport : ∀ p, R < ‖p‖ → f p = 0) (hM : 0 < scaledInputMass f S T) (v : I → ℤ) :
    (integerImagePMF A B f hf0 S T hS hT hsupport hM).toMeasure.real {v} =
      (∑' p : {p : (I → ℤ) × (J → ℤ) // A *ᵥ p.1 + B *ᵥ p.2 = v},
        scaledIntegerWeight f S T p.val) / scaledInputWeightSum f S T := by
  rw [measureReal_def, PMF.toMeasure_apply_singleton _ v (measurableSet_singleton v)]
  exact integerImagePMF_apply A B f hf0 S T hS hT hsupport hM v

theorem integerImagePMF_zero_off_image (A : Matrix I I ℤ) (B : Matrix I J ℤ)
    (f : (J → ℝ) × (I → ℝ) → ℝ) (hf0 : ∀ p, 0 ≤ f p)
    (S : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j)
    {R : ℝ} (hsupport : ∀ p, R < ‖p‖ → f p = 0) (hM : 0 < scaledInputMass f S T)
    (v : I → ℤ) (hv : v ∉ pivotFullImage A B) :
    integerImagePMF A B f hf0 S T hS hT hsupport hM v = 0 := by
  apply (PMF.apply_eq_zero_iff _ v).mpr
  intro hmem
  obtain ⟨p, _, hp⟩ := (PMF.mem_support_map_iff _ _ _).mp hmem
  exact hv ((pivotFullImage_iff A B v).mpr ⟨p.1, p.2, hp⟩)

theorem normalizedIntegerFiberOutputMass_zero_off_image (A : Matrix I I ℤ) (B : Matrix I J ℤ)
    (S P : I → ℝ) (T : J → ℝ) (f : (J → ℝ) × (I → ℝ) → ℝ) (v : I → ℤ)
    (hv : v ∉ pivotFullImage A B) : normalizedIntegerFiberOutputMass A B S P T f v = 0 := by
  rw [normalizedIntegerFiberOutputMass, scaledIntegerFiberOutputMass_zero_off_image A B S P T f v hv,
    zero_div]

end Erdos3

end OAI
