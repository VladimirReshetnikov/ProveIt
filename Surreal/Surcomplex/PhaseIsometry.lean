import Surreal.Surcomplex.InfinitesimalExponentialLeading
import Surreal.Surcomplex.TrigonometricTaylor

/-!
# Local valuation isometry of finite phase

The phase difference has the exact complex linear factor with residue one.
This proves the relative equivalence, exact valuation and complex quotient
claims in `trigonometry:eq:phaseisometry`.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- On an infinitesimal real angle the finite phase is exactly the imaginary strong exponential. -/
theorem finitePhase_of_isInfinitesimal (θ : SignSequence.FiniteElement.{u})
    (hi : SignSequence.IsInfinitesimal θ.val) :
    finitePhase θ = infExp (ofReal θ.val * I) (infinitesimal_ofReal_mul_I _ hi) :=
  finiteExp_of_isInfinitesimal _ _

/-- Every finite phase has valuation zero. -/
@[simp] theorem valuation_finitePhase (θ : SignSequence.FiniteElement.{u}) :
    valuation (finitePhase θ) = 0 := by
  rw [valuation_eq_modulus, modulus_finitePhase, SignSequence.valuation_one]

private theorem phase_linear_factor_ne_zero (θ φ : SignSequence.FiniteElement.{u})
    (hne : θ.val - φ.val ≠ 0) : I * finitePhase φ * ofReal (θ.val - φ.val) ≠ 0 := by
  apply mul_ne_zero
  · apply mul_ne_zero
    · intro h
      have he := modulus_I.{u}
      rw [h, modulus_zero] at he
      exact zero_ne_one he
    · exact finiteExp_ne_zero _
  · exact (map_ne_zero ofReal).mpr hne

/-- Phase differences have the exact linear complex factor times a finite residue-one factor. -/
theorem finitePhase_sub_leading_factor (θ φ : SignSequence.FiniteElement.{u})
    (hi : SignSequence.IsInfinitesimal (θ.val - φ.val)) :
    ∃ R : Surcomplex.{u}, IsFinite R ∧ standardPart R = 1 ∧
      finitePhase θ - finitePhase φ = I * finitePhase φ * ofReal (θ.val - φ.val) * R := by
  obtain ⟨R, hR, hr, he⟩ := infExp_sub_one_leading_factor
    (ofReal (θ.val - φ.val) * I) (infinitesimal_ofReal_mul_I _ hi)
  have hp := finitePhase_of_isInfinitesimal (θ - φ) hi
  change finitePhase (θ - φ) = infExp (ofReal (θ.val - φ.val) * I) _ at hp
  rw [← hp] at he
  refine ⟨R, hR, hr, ?_⟩
  calc
    finitePhase θ - finitePhase φ = finitePhase φ * (finitePhase (θ - φ) - 1) := by
      rw [mul_sub, mul_one, mul_comm, ← finitePhase_add, sub_add_cancel]
    _ = _ := by rw [he]; ring

/-- Infinitesimal angular differences and their phase displacements have exactly the same valuation. -/
theorem valuation_finitePhase_sub (θ φ : SignSequence.FiniteElement.{u})
    (hi : SignSequence.IsInfinitesimal (θ.val - φ.val)) :
    valuation (finitePhase θ - finitePhase φ) = SignSequence.valuation (θ.val - φ.val) := by
  obtain ⟨R, hR, hr, he⟩ := finitePhase_sub_leading_factor θ φ hi
  have hv := (valuation_eq_zero_iff_standardPart_ne_zero hR).mpr (by rw [hr]; norm_num)
  have hI : valuation (I : Surcomplex.{u}) = 0 := by
    rw [valuation_eq_modulus, modulus_I, SignSequence.valuation_one]
  simp only [he, valuation_mul, hI, valuation_finitePhase, valuation_ofReal, hv, zero_add, add_zero]

/-- The source complex quotient is one plus an actual infinitesimal. -/
theorem infinitesimal_phase_difference_relative_error (θ φ : SignSequence.FiniteElement.{u})
    (hi : SignSequence.IsInfinitesimal (θ.val - φ.val)) (hne : θ.val - φ.val ≠ 0) :
    IsInfinitesimal ((finitePhase θ - finitePhase φ) /
      (I * finitePhase φ * ofReal (θ.val - φ.val)) - 1) := by
  obtain ⟨R, hR, hr, he⟩ := finitePhase_sub_leading_factor θ φ hi
  rw [he, mul_div_cancel_left₀ _ (phase_linear_factor_ne_zero θ φ hne)]
  simpa only [hr, map_one] using infinitesimal_sub_standardPart hR

/-- The phase displacement modulus is relatively equivalent to the absolute angular difference. -/
theorem infinitesimal_phase_modulus_relative_error (θ φ : SignSequence.FiniteElement.{u})
    (hi : SignSequence.IsInfinitesimal (θ.val - φ.val)) (hne : θ.val - φ.val ≠ 0) :
    SignSequence.IsInfinitesimal
      (modulus (finitePhase θ - finitePhase φ) / |θ.val - φ.val| - 1) := by
  obtain ⟨R, hR, hr, he⟩ := finitePhase_sub_leading_factor θ φ hi
  rw [he, modulus_mul, modulus_mul, modulus_mul, modulus_I, modulus_finitePhase,
    modulus_ofReal, one_mul, one_mul, mul_div_cancel_left₀ _ (abs_ne_zero.mpr hne)]
  have hf := (isFinite_iff_modulus R).mp hR
  have hs : SignSequence.standardPart (modulus R) = 1 := by
    rw [standardPart_modulus hR, hr, norm_one]
  simpa only [hs, map_one] using SignSequence.infinitesimal_sub_standardPart hf

end
end Surreal.Surcomplex
