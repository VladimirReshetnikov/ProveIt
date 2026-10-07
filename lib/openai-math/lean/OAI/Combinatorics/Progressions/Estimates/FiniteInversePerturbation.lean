import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_le_twice_mul_of_inverse_perturbation
    (A B : E →L[ℝ] E) (hA : A.IsInvertible) (K : ℝ≥0)
    (hK : ‖A.inverse‖ ≤ K) (hsmall : (K : ℝ) * ‖B - A‖ ≤ 1 / 2) (v : E) :
    ‖v‖ ≤ 2 * (K : ℝ) * ‖B v‖ := by
  have hid : v = A.inverse (B v) - A.inverse ((B - A) v) := by
    rw [← map_sub]
    simp only [sub_apply, sub_sub_cancel, hA.inverse_apply_self]
  have hmain : ‖A.inverse (B v)‖ ≤ (K : ℝ) * ‖B v‖ :=
    (A.inverse.le_opNorm _).trans (mul_le_mul_of_nonneg_right hK (norm_nonneg _))
  have herr : ‖A.inverse ((B - A) v)‖ ≤ (1 / 2 : ℝ) * ‖v‖ := by
    calc
      _ ≤ ‖A.inverse‖ * ‖(B - A) v‖ := A.inverse.le_opNorm _
      _ ≤ (K : ℝ) * (‖B - A‖ * ‖v‖) :=
        mul_le_mul hK ((B - A).le_opNorm _) (norm_nonneg _) K.coe_nonneg
      _ = ((K : ℝ) * ‖B - A‖) * ‖v‖ := by ring
      _ ≤ (1 / 2 : ℝ) * ‖v‖ := mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
  have hnorm : ‖v‖ ≤ (K : ℝ) * ‖B v‖ + (1 / 2 : ℝ) * ‖v‖ := by
    calc
      ‖v‖ = ‖A.inverse (B v) - A.inverse ((B - A) v)‖ := congrArg norm hid
      _ ≤ ‖A.inverse (B v)‖ + ‖A.inverse ((B - A) v)‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add hmain herr
  linarith

theorem inverse_perturbation_bound [FiniteDimensional ℝ E]
    (A B : E →L[ℝ] E) (hA : A.IsInvertible) (K : ℝ≥0)
    (hK : ‖A.inverse‖ ≤ K) (hsmall : (K : ℝ) * ‖B - A‖ ≤ 1 / 2) :
    B.IsInvertible ∧ ‖B.inverse‖ ≤ 2 * (K : ℝ) := by
  have hlower := norm_le_twice_mul_of_inverse_perturbation A B hA K hK hsmall
  have hinj : Function.Injective B := by
    intro x y hxy
    have h := hlower (x - y)
    rw [map_sub, hxy, sub_self, norm_zero, mul_zero] at h
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))
  have hbij : Function.Bijective B :=
    ⟨hinj, LinearMap.surjective_of_injective (f := B.toLinearMap) hinj⟩
  have hB : B.IsInvertible :=
    ⟨(LinearEquiv.ofBijective B.toLinearMap hbij).toContinuousLinearEquiv, rfl⟩
  refine ⟨hB, B.inverse.opNorm_le_bound (by positivity) ?_⟩
  intro v
  simpa only [hB.self_apply_inverse] using hlower (B.inverse v)

end Erdos3

end

end OAI
