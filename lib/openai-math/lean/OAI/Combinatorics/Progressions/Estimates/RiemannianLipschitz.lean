import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength

namespace OAI

section

namespace Erdos3

open Manifold MeasureTheory Set
open scoped Manifold ContDiff ENNReal

variable {E F H K M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace K N]
  [∀ x : M, ENorm (TangentSpace I x)] [∀ x : N, ENorm (TangentSpace J x)]

theorem pathELength_comp_le_of_mfderiv_norm_le {φ : M → N}
    (hφ : ContMDiff I J 1 φ)
    (hbound : ∀ (x : M) (v : TangentSpace I x), ‖mfderiv I J φ x v‖ₑ ≤ ‖v‖ₑ)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ) I 1 γ) (a b : ℝ) :
    pathELength J (φ ∘ γ) a b ≤ pathELength I γ a b := by
  rw [pathELength_eq_lintegral_mfderiv_Icc, pathELength_eq_lintegral_mfderiv_Icc]
  apply lintegral_mono
  intro t
  exact (congrArg (fun v : TangentSpace J (φ (γ t)) => ‖v‖ₑ)
    (mfderiv_comp_apply t (hφ.mdifferentiableAt one_ne_zero)
      (hγ.mdifferentiableAt one_ne_zero) 1)).trans_le (hbound (γ t) _)

variable [∀ x : M, ENormSMulClass ℝ (TangentSpace I x)]
  [∀ x : N, ENormSMulClass ℝ (TangentSpace J x)]

theorem riemannianEDist_le_of_mfderiv_norm_le {φ : M → N}
    (hφ : ContMDiff I J 1 φ)
    (hbound : ∀ (x : M) (v : TangentSpace I x), ‖mfderiv I J φ x v‖ₑ ≤ ‖v‖ₑ)
    (x y : M) : riemannianEDist J (φ x) (φ y) ≤ riemannianEDist I x y := by
  apply le_of_forall_gt
  intro r hr
  obtain ⟨γ, hγ0, hγ1, hγ, hlen, _⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hr zero_lt_one
  have hends : riemannianEDist J (φ x) (φ y) ≤ pathELength J (φ ∘ γ) 0 1 :=
    riemannianEDist_le_pathELength (hφ.comp hγ).contMDiffOn
      (by simp only [Function.comp_apply, hγ0])
      (by simp only [Function.comp_apply, hγ1]) zero_le_one
  exact (hends.trans (pathELength_comp_le_of_mfderiv_norm_le hφ hbound hγ 0 1)).trans_lt hlen

end Erdos3

end

section

namespace Erdos3

open Manifold MeasureTheory Set
open scoped Manifold ContDiff ENNReal NNReal Bundle

variable {E F H K M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace K N]
  [∀ x : M, ENorm (TangentSpace I x)] [∀ x : N, ENorm (TangentSpace J x)]

theorem pathELength_comp_le_mul_of_mfderiv_bound {φ : M → N} {C : ℝ≥0}
    (hφ : ContMDiff I J 1 φ)
    (hbound : ∀ (x : M) (v : TangentSpace I x), ‖mfderiv I J φ x v‖ₑ ≤ C * ‖v‖ₑ)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ) I 1 γ) (a b : ℝ) :
    pathELength J (φ ∘ γ) a b ≤ C * pathELength I γ a b := by
  rw [pathELength_eq_lintegral_mfderiv_Icc, pathELength_eq_lintegral_mfderiv_Icc,
    ← lintegral_const_mul' (C : ℝ≥0∞) _ (by simp)]
  apply lintegral_mono
  intro t
  exact (congrArg (fun v : TangentSpace J (φ (γ t)) => ‖v‖ₑ)
    (mfderiv_comp_apply t (hφ.mdifferentiableAt one_ne_zero)
      (hγ.mdifferentiableAt one_ne_zero) 1)).trans_le (hbound (γ t) _)

variable [∀ x : M, ENormSMulClass ℝ (TangentSpace I x)]
  [∀ x : N, ENormSMulClass ℝ (TangentSpace J x)]

theorem riemannianEDist_le_mul_of_mfderiv_bound {φ : M → N} {C : ℝ≥0}
    (hC : 0 < C) (hφ : ContMDiff I J 1 φ)
    (hbound : ∀ (x : M) (v : TangentSpace I x), ‖mfderiv I J φ x v‖ₑ ≤ C * ‖v‖ₑ)
    (x y : M) : riemannianEDist J (φ x) (φ y) ≤ C * riemannianEDist I x y := by
  have hC0 : (C : ℝ≥0∞) ≠ 0 := by exact_mod_cast hC.ne'
  have hCt : (C : ℝ≥0∞) ≠ ⊤ := by simp
  apply le_of_forall_gt
  intro r hr
  have hinput : riemannianEDist I x y < r / C := by
    apply (ENNReal.lt_div_iff_mul_lt (.inl hC0) (.inl hCt)).mpr
    simpa only [mul_comm] using hr
  obtain ⟨γ, hγ0, hγ1, hγ, hlen, _⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hinput zero_lt_one
  have hends : riemannianEDist J (φ x) (φ y) ≤ pathELength J (φ ∘ γ) 0 1 :=
    riemannianEDist_le_pathELength (hφ.comp hγ).contMDiffOn
      (by simp only [Function.comp_apply, hγ0])
      (by simp only [Function.comp_apply, hγ1]) zero_le_one
  have hmul : (C : ℝ≥0∞) * pathELength I γ 0 1 < r := by
    simpa only [mul_comm] using
      (ENNReal.lt_div_iff_mul_lt (.inl hC0) (.inl hCt)).mp hlen
  exact (hends.trans (pathELength_comp_le_mul_of_mfderiv_bound hφ hbound hγ 0 1)).trans_lt hmul

end Erdos3

end

end OAI
