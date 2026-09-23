import Surreal.Surcomplex.ArcsinSeries
import Surreal.Foundations.SignSequenceRelativeAsymptotics

/-!
# Inverse-tangent expansions with a finite unit denominator

The small slopes in `trigonometry:thm:flat` have appreciable denominators.
Their cubic expansions have an exact fifth-order finite remainder, and
positive leading residues prevent cancellation when the base angles are added.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

/-- An infinitesimal numerator over a finite unit gives the literal cubic slope expansion. -/
theorem arctanFunction_div_cubic_expansion (p y : SignSequence.{u})
    (hp : SignSequence.IsFinite p) (hs : SignSequence.standardPart p ≠ 0)
    (hy : SignSequence.IsInfinitesimal y) :
    ∃ R : SignSequence.{u}, SignSequence.IsFinite R ∧
      arctanFunction (y / p) = y / p - y ^ 3 / (3 * p ^ 3) + y ^ 5 * R := by
  have hi := SignSequence.finite_inv_of_standardPart_ne_zero hp hs
  have ht : SignSequence.IsInfinitesimal (y / p) := by
    simpa only [div_eq_mul_inv] using SignSequence.infinitesimal_mul_finite hy hi
  obtain ⟨R, hR, _, he⟩ := SignSequence.exists_finite_powerSeries_remainder (y / p) ht
    (Analytic.taylorSeries Real.arctan 0) 5
  rw [← arctanFunction_eq_powerSeries (y / p) ht] at he
  simp_rw [Analytic.coeff_taylorSeries_arctan_zero] at he
  norm_num [Finset.sum_range_succ, map_div₀, map_neg, map_ofNat] at he
  refine ⟨p⁻¹ ^ 5 * R, SignSequence.finite_mul (SignSequence.finite_pow hi 5) hR, ?_⟩
  rw [he]
  simp only [div_eq_mul_inv, mul_pow, mul_inv_rev, inv_pow]
  ring

/-- The height coefficient of a small slope has the reciprocal denominator as its residue. -/
theorem arctanFunction_div_leading_factor (p y : SignSequence.{u})
    (hp : SignSequence.IsFinite p) (hs : SignSequence.standardPart p ≠ 0)
    (hy : SignSequence.IsInfinitesimal y) :
    ∃ F : SignSequence.{u}, SignSequence.IsFinite F ∧
      SignSequence.standardPart F = (SignSequence.standardPart p)⁻¹ ∧
      arctanFunction (y / p) = y * F := by
  have hi := SignSequence.finite_inv_of_standardPart_ne_zero hp hs
  have ht : SignSequence.IsInfinitesimal (y / p) := by
    simpa only [div_eq_mul_inv] using SignSequence.infinitesimal_mul_finite hy hi
  obtain ⟨F, hF, hFs, he⟩ := arctanFunction_leading_factor (y / p) ht
  refine ⟨p⁻¹ * F, SignSequence.finite_mul hi hF, ?_, ?_⟩
  · rw [SignSequence.standardPart_mul hi hF,
      SignSequence.standardPart_inv_of_ne_zero hp hs, hFs, mul_one]
  · rw [he, div_eq_mul_inv, mul_assoc]

end Surreal.Surcomplex
