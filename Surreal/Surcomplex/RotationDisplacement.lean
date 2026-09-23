import Surreal.Surcomplex.PhaseIsometry
import Surreal.Surcomplex.TrigonometricLeading

/-!
# Rotation displacement at arbitrary surreal radii

The exact chord formula and infinitesimal relative equivalence prove
`trigonometry:eq:rotdisplacement`, completing `trigonometry:cor:phaseisometry`.
The following examples distinguish an infinitesimal angle from the size
of its displacement at radii omega and omega squared.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- The chord from one to any finite phase is twice the absolute half-angle sine. -/
theorem modulus_finitePhase_sub_one (θ : SignSequence.FiniteElement.{u}) :
    modulus (finitePhase θ - 1) = 2 * |finiteSin (finiteHalf θ)| := by
  apply (sq_eq_sq₀ (modulus_nonneg _) (mul_nonneg (by norm_num) (abs_nonneg _))).mp
  rw [modulus_sq, normSq_eq, mul_pow, sq_abs]
  change (finiteCos θ - 1) ^ 2 + (finiteSin θ - 0) ^ 2 = 2 ^ 2 * finiteSin (finiteHalf θ) ^ 2
  have ht := finiteCos_sq_add_finiteSin_sq θ
  have hh := finiteSin_finiteHalf_sq θ
  nlinarith only [ht, hh]

/-- Multiplication by the initial vector scales the unit-circle displacement exactly. -/
theorem modulus_rotation_displacement_factor (θ : SignSequence.FiniteElement.{u})
    (z : Surcomplex.{u}) :
    modulus (finitePhase θ * z - z) = modulus z * modulus (finitePhase θ - 1) := by
  rw [show finitePhase θ * z - z = z * (finitePhase θ - 1) by ring, modulus_mul]

/-- The exact rotation chord formula holds at arbitrary radii and every finite real angle. -/
theorem modulus_rotation_displacement (θ : SignSequence.FiniteElement.{u}) (z : Surcomplex.{u}) :
    modulus (finitePhase θ * z - z) = 2 * modulus z * |finiteSin (finiteHalf θ)| := by
  rw [modulus_rotation_displacement_factor, modulus_finitePhase_sub_one]
  ring

/-- For a nonzero infinitesimal rotation, displacement is relatively equivalent to radius times angle. -/
theorem infinitesimal_rotation_modulus_relative_error (θ : SignSequence.FiniteElement.{u})
    (z : Surcomplex.{u}) (hz : z ≠ 0) (hi : SignSequence.IsInfinitesimal θ.val) (hne : θ.val ≠ 0) :
    SignSequence.IsInfinitesimal
      (modulus (finitePhase θ * z - z) / (modulus z * |θ.val|) - 1) := by
  rw [modulus_rotation_displacement_factor, mul_div_mul_left _ _ (modulus_pos hz).ne']
  simpa only [ArchimedeanClass.FiniteElement.val_zero, sub_zero, finitePhase_zero] using
    infinitesimal_phase_modulus_relative_error θ 0 (by simpa using hi) (by simpa using hne)

/-- The displacement valuation is exactly that of radius times the infinitesimal angle. -/
theorem valuation_rotation_displacement_scale (θ : SignSequence.FiniteElement.{u})
    (z : Surcomplex.{u}) (hi : SignSequence.IsInfinitesimal θ.val) :
    valuation (finitePhase θ * z - z) = SignSequence.valuation (modulus z * |θ.val|) := by
  have hv : valuation (finitePhase θ - 1) = SignSequence.valuation θ.val := by
    simpa only [ArchimedeanClass.FiniteElement.val_zero, sub_zero, finitePhase_zero] using
      valuation_finitePhase_sub θ 0 (by simpa using hi)
  rw [valuation_eq_modulus, modulus_rotation_displacement_factor, SignSequence.valuation_mul,
    SignSequence.valuation_mul, SignSequence.valuation_abs]
  exact congrArg (fun a => SignSequence.valuation (modulus z) + a) hv

/-- A concrete finite angle with actual value omega inverse. -/
def inverseOmegaAngle : SignSequence.FiniteElement.{u} :=
  ⟨(SignSequence.ofOrdinal Ordinal.omega0)⁻¹,
    SignSequence.finite_of_infinitesimal SignSequence.infinitesimal_inv_omega0⟩

@[simp] theorem val_inverseOmegaAngle :
    inverseOmegaAngle.val = (SignSequence.ofOrdinal Ordinal.omega0 : SignSequence.{u})⁻¹ := rfl

/-- At radius omega, rotation through omega inverse moves the endpoint by a length equivalent to one. -/
theorem rotation_omega_displacement_sub_one_infinitesimal :
    SignSequence.IsInfinitesimal
      (modulus (finitePhase inverseOmegaAngle * ofReal (SignSequence.ofOrdinal Ordinal.omega0) -
        ofReal (SignSequence.ofOrdinal Ordinal.omega0) : Surcomplex.{u}) - 1) := by
  have hz : (ofReal (SignSequence.ofOrdinal Ordinal.omega0) : Surcomplex.{u}) ≠ 0 :=
    (map_ne_zero ofReal).mpr SignSequence.omega0_pos.ne'
  have h := infinitesimal_rotation_modulus_relative_error inverseOmegaAngle _ hz
    SignSequence.infinitesimal_inv_omega0 SignSequence.inv_omega0_pos.ne'
  simpa only [val_inverseOmegaAngle, modulus_ofReal, abs_of_pos SignSequence.omega0_pos,
    abs_of_pos SignSequence.inv_omega0_pos, mul_inv_cancel₀ SignSequence.omega0_pos.ne', div_one] using h

/-- At radius omega squared, the same infinitesimal rotation has infinite displacement. -/
theorem rotation_omega_sq_displacement_not_finite :
    ¬ IsFinite (finitePhase inverseOmegaAngle * ofReal ((SignSequence.ofOrdinal Ordinal.omega0) ^ 2) -
      ofReal ((SignSequence.ofOrdinal Ordinal.omega0) ^ 2) : Surcomplex.{u}) := by
  have hv := valuation_rotation_displacement_scale inverseOmegaAngle
    (ofReal ((SignSequence.ofOrdinal Ordinal.omega0) ^ 2) : Surcomplex.{u})
    SignSequence.infinitesimal_inv_omega0
  have hs : (SignSequence.ofOrdinal Ordinal.omega0 : SignSequence.{u}) ^ 2 *
      (SignSequence.ofOrdinal Ordinal.omega0)⁻¹ = SignSequence.ofOrdinal Ordinal.omega0 := by
    rw [pow_two, mul_assoc, mul_inv_cancel₀ SignSequence.omega0_pos.ne', mul_one]
  simp only [val_inverseOmegaAngle, modulus_ofReal, abs_of_pos (pow_pos SignSequence.omega0_pos 2),
    abs_of_pos SignSequence.inv_omega0_pos, hs] at hv
  intro hf
  have hn := (isFinite_iff_valuation_nonneg _).mp hf
  rw [hv] at hn
  exact ((SignSequence.infinitesimal_inv_iff_not_finite SignSequence.omega0_pos.ne').mp
    SignSequence.infinitesimal_inv_omega0) ((SignSequence.isFinite_iff_valuation_nonneg _).mpr hn)

end
end Surreal.Surcomplex
