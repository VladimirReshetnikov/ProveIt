import Surreal.Surcomplex.ReciprocalLegTriangle
import Surreal.Foundations.SignSequenceHypotenuseExpansion
import Surreal.Surcomplex.ArcsinSeries

/-!
# Reciprocal legs at infinite actual scales

The analytic and scale clauses of `trigonometry:ex:infinite` apply to every positive infinite
actual surreal leg. The inradius has an exact finite seventh-order remainder, and the
circumradius is relatively equivalent to half the infinite leg. The ordinary area and
infinitesimal acute angle belong to the actual triangle, including its companion with the
right angle at zero. The final specialization uses the actual ordinal omega.
-/

universe u

namespace Surreal.Surcomplex.ReciprocalLegTriangle

open Foundations

noncomputable section

private theorem finite_half : SignSequence.IsFinite ((1 : SignSequence.{u}) / 2) := by
  simpa only [map_div₀, map_one, map_ofNat] using SignSequence.finite_ofReal (1 / 2 : ℝ)

private theorem finite_two : SignSequence.IsFinite (2 : SignSequence.{u}) := by
  simpa only [map_ofNat] using SignSequence.finite_ofReal (2 : ℝ)

private theorem finite_sixteenth : SignSequence.IsFinite ((1 : SignSequence.{u}) / 16) := by
  simpa only [map_div₀, map_one, map_ofNat] using SignSequence.finite_ofReal (1 / 16 : ℝ)

private theorem standardPart_sixteenth :
    SignSequence.standardPart ((1 : SignSequence.{u}) / 16) = 1 / 16 := by
  simpa only [map_div₀, map_one, map_ofNat] using SignSequence.standardPart_ofReal (1 / 16 : ℝ)

variable (L : SignSequence.{u}) (hL : 0 < L)

include hL in
/-- The short leg is a positive infinitesimal at every positive infinite long-leg scale. -/
theorem inverse_infinitesimal (hInf : ¬ SignSequence.IsFinite L) :
    SignSequence.IsInfinitesimal L⁻¹ :=
  (SignSequence.infinitesimal_inv_iff_not_finite hL.ne').mpr hInf

include hL in
private theorem inverse_fourth_infinitesimal (hInf : ¬ SignSequence.IsFinite L) :
    SignSequence.IsInfinitesimal ((L⁻¹) ^ 4) := by
  have h := (SignSequence.infinitesimal_sq_iff ((L⁻¹) ^ 2)).mpr
    ((SignSequence.infinitesimal_sq_iff L⁻¹).mpr (inverse_infinitesimal L hL hInf))
  simpa only [← pow_mul] using h

include hL in
private theorem root_correction_infinitesimal (hInf : ¬ SignSequence.IsFinite L) :
    SignSequence.IsInfinitesimal (SignSequence.sqrt (1 + (L⁻¹) ^ 4) - 1) := by
  apply SignSequence.infinitesimal_sqrt_sub_one (by positivity)
  simpa only [add_sub_cancel_left] using inverse_fourth_infinitesimal L hL hInf

/-- The exact hypotenuse factorization is on the actual side opposite the right angle. -/
theorem sideB_factor : (triangle L hL).sideB =
    L * SignSequence.sqrt (1 + (L⁻¹) ^ 4) := by
  rw [sideB, hypotenuse_factor L hL]

/-- The actual hypotenuse is relatively equivalent to the infinite long leg. -/
theorem hypotenuse_asymptotic (hInf : ¬ SignSequence.IsFinite L) :
    SignSequence.IsInfinitesimal ((triangle L hL).sideB / L - 1) := by
  rw [sideB_factor, mul_div_cancel_left₀ _ hL.ne']
  exact root_correction_infinitesimal L hL hInf

/-- The circumradius has the ordinary factor one half at the infinite leg's scale. -/
theorem circumradius_asymptotic (hInf : ¬ SignSequence.IsFinite L) :
    SignSequence.IsInfinitesimal ((triangle L hL).circumradius / (L / 2) - 1) := by
  have he : (triangle L hL).circumradius / (L / 2) =
      SignSequence.sqrt (1 + (L⁻¹) ^ 4) := by
    rw [circumradius, hypotenuse_factor L hL]
    field_simp [hL.ne']
  rw [he]
  exact root_correction_infinitesimal L hL hInf

/-- The exact inradius expansion retains a finite seventh-order tail with residue `1/16`. -/
theorem inradius_expansion (hInf : ¬ SignSequence.IsFinite L) :
    ∃ E : SignSequence.{u}, SignSequence.IsFinite E ∧ SignSequence.standardPart E = 1 / 16 ∧
      (triangle L hL).inradius = 1 / (2 * L) - 1 / (4 * L ^ 3) + (L⁻¹) ^ 7 * E := by
  have ht := inverse_fourth_infinitesimal L hL hInf
  obtain ⟨E, hE, _, he⟩ := SignSequence.sqrt_one_add_expansion ((L⁻¹) ^ 4) ht
  have hrem : SignSequence.IsInfinitesimal (((L⁻¹) ^ 4 * E) * (1 / 2)) :=
    SignSequence.infinitesimal_mul_finite (SignSequence.infinitesimal_mul_finite ht hE) finite_half
  have hremf := SignSequence.finite_of_infinitesimal hrem
  refine ⟨1 / 16 - ((L⁻¹) ^ 4 * E) * (1 / 2),
    SignSequence.finite_sub finite_sixteenth hremf, ?_, ?_⟩
  · rw [SignSequence.standardPart_sub finite_sixteenth hremf, standardPart_sixteenth,
      (SignSequence.standardPart_eq_zero_iff hremf).mpr hrem, sub_zero]
  · rw [inradius, hypotenuse_factor L hL, he]
    field_simp [hL.ne']
    ring

/-- The inradius is relatively equivalent to half the reciprocal leg. -/
theorem inradius_asymptotic (hInf : ¬ SignSequence.IsFinite L) :
    SignSequence.IsInfinitesimal ((triangle L hL).inradius / (1 / (2 * L)) - 1) := by
  obtain ⟨E, hE, _, he⟩ := inradius_expansion L hL hInf
  have hi := inverse_infinitesimal L hL hInf
  have hf := SignSequence.finite_of_infinitesimal hi
  have hcoef : SignSequence.IsFinite (-(1 / 2) + 2 * (L⁻¹) ^ 4 * E) :=
    SignSequence.finite_add (SignSequence.finite_neg finite_half)
      (SignSequence.finite_mul (SignSequence.finite_mul finite_two
        (SignSequence.finite_pow hf 4)) hE)
  have hn : (triangle L hL).inradius / (1 / (2 * L)) - 1 =
      (L⁻¹) ^ 2 * (-(1 / 2) + 2 * (L⁻¹) ^ 4 * E) := by
    rw [he]
    field_simp [hL.ne']
    ring
  rw [hn]
  exact SignSequence.infinitesimal_mul_finite ((SignSequence.infinitesimal_sq_iff _).mpr hi) hcoef

/-- The actual short side is infinitesimal. -/
theorem sideA_infinitesimal (hInf : ¬ SignSequence.IsFinite L) :
    SignSequence.IsInfinitesimal (triangle L hL).sideA := by
  rw [sideA]
  exact inverse_infinitesimal L hL hInf

/-- The actual long side is infinite. -/
theorem sideC_not_finite (hInf : ¬ SignSequence.IsFinite L) :
    ¬ SignSequence.IsFinite (triangle L hL).sideC := by
  rwa [sideC]

/-- The actual hypotenuse is infinite. -/
theorem hypotenuse_not_finite (hInf : ¬ SignSequence.IsFinite L) :
    ¬ SignSequence.IsFinite (triangle L hL).sideB :=
  (SignSequence.finite_iff_of_infinitesimal_div_sub_one hL.ne'
    (hypotenuse_asymptotic L hL hInf)).not.mpr hInf

/-- The actual circumradius is infinite. -/
theorem circumradius_not_finite (hInf : ¬ SignSequence.IsFinite L) :
    ¬ SignSequence.IsFinite (triangle L hL).circumradius := by
  have hn : ¬ SignSequence.IsFinite (L / 2) := by
    intro hf
    have h := SignSequence.finite_mul finite_two hf
    have he : (2 : SignSequence.{u}) * (L / 2) = L := by ring
    exact hInf (he ▸ h)
  exact (SignSequence.finite_iff_of_infinitesimal_div_sub_one
    (div_ne_zero hL.ne' (by norm_num)) (circumradius_asymptotic L hL hInf)).not.mpr hn

/-- The positive area is the finite ordinary number one half. -/
theorem area_finite : SignSequence.IsFinite (triangle L hL).area := by
  rw [area]
  exact finite_half

/-- The acute angle opposite the reciprocal leg is infinitesimal. -/
theorem angleA_infinitesimal (hInf : ¬ SignSequence.IsFinite L) :
    SignSequence.IsInfinitesimal (triangle L hL).angleA.val := by
  rw [angleA]
  exact infinitesimal_arctanFunction _
    ((SignSequence.infinitesimal_sq_iff _).mpr (inverse_infinitesimal L hL hInf))

/-- The small angle retains the exact inverse-square scale before taking any standard part. -/
theorem angleA_asymptotic (hInf : ¬ SignSequence.IsFinite L) :
    SignSequence.IsInfinitesimal ((triangle L hL).angleA.val / (L⁻¹) ^ 2 - 1) := by
  rw [angleA]
  exact infinitesimal_arctanFunction_div_sub_one _
    ((SignSequence.infinitesimal_sq_iff _).mpr (inverse_infinitesimal L hL hInf))
    (pow_ne_zero _ (inv_ne_zero hL.ne'))

/-- The inradius is infinitesimal although the long leg and circumradius are infinite. -/
theorem inradius_infinitesimal (hInf : ¬ SignSequence.IsFinite L) :
    SignSequence.IsInfinitesimal (triangle L hL).inradius := by
  have hi : SignSequence.IsInfinitesimal (1 / (2 * L)) := by
    have h := SignSequence.infinitesimal_mul_finite (inverse_infinitesimal L hL hInf) finite_half
    convert h using 1
    ring
  exact (SignSequence.infinitesimal_iff_of_infinitesimal_div_sub_one
    (one_div_ne_zero (mul_ne_zero (by norm_num) hL.ne'))
    (inradius_asymptotic L hL hInf)).mpr hi

/-- The right-at-zero companion has the same infinite circumradius scale. -/
theorem companion_circumradius_asymptotic (hInf : ¬ SignSequence.IsFinite L) :
    SignSequence.IsInfinitesimal ((companion L hL).circumradius / (L / 2) - 1) := by
  rw [companion_circumradius, ← circumradius L hL]
  exact circumradius_asymptotic L hL hInf

/-- The companion's infinitesimal angle is at the long leg's endpoint, with the correct label. -/
theorem companion_angleB_infinitesimal (hInf : ¬ SignSequence.IsFinite L) :
    SignSequence.IsInfinitesimal (companion L hL).angleB.val := by
  rw [companion_angleB, ← angleA L hL]
  exact angleA_infinitesimal L hL hInf

/-- The source's displayed ordinal-omega companion has an infinitesimal angle at omega. -/
theorem omega_companion_angleB_infinitesimal :
    SignSequence.IsInfinitesimal
      (companion (SignSequence.ofOrdinal Ordinal.omega0) SignSequence.omega0_pos).angleB.val := by
  apply companion_angleB_infinitesimal
  exact (SignSequence.infinitesimal_inv_iff_not_finite SignSequence.omega0_pos.ne').mp
    SignSequence.infinitesimal_inv_omega0

/-- The circumradius of the actual companion `0, omega, i/omega` is equivalent to omega over two. -/
theorem omega_companion_circumradius_asymptotic :
    SignSequence.IsInfinitesimal
      ((companion (SignSequence.ofOrdinal Ordinal.omega0) SignSequence.omega0_pos).circumradius /
        ((SignSequence.ofOrdinal Ordinal.omega0 : SignSequence.{u}) / 2) - 1) := by
  apply companion_circumradius_asymptotic
  exact (SignSequence.infinitesimal_inv_iff_not_finite SignSequence.omega0_pos.ne').mp
    SignSequence.infinitesimal_inv_omega0

/-- The ordinal-omega companion's hypotenuse is the literal factored square root in the source. -/
theorem omega_companion_hypotenuse :
    (companion (SignSequence.ofOrdinal Ordinal.omega0) SignSequence.omega0_pos).sideA =
      (SignSequence.ofOrdinal Ordinal.omega0 : SignSequence.{u}) *
        SignSequence.sqrt (1 + ((SignSequence.ofOrdinal Ordinal.omega0)⁻¹) ^ 4) := by
  rw [companion_sideA, hypotenuse_factor _ SignSequence.omega0_pos]

end
end Surreal.Surcomplex.ReciprocalLegTriangle
