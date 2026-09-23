import Surreal.Foundations.SignSequenceRelativeAsymptotics

/-!
# Finite remainders for reciprocals of quadratic perturbations

A finite actual unit plus an infinitesimal quadratic perturbation remains a finite unit.
Exact field algebra gives its first-order reciprocal expansion with a finite second-order
remainder. This supplies geometric inversion in `trigonometry:thm:flat`, including the
normalized inradius bracket in `trigonometry:eq:flatslack`.
-/

universe u

namespace Surreal.Foundations.SignSequence

/-- A quadratic infinitesimal perturbation of a finite actual surreal remains finite. -/
theorem finite_quadratic_perturbation (q c d t : SignSequence.{u})
    (hq : IsFinite q) (hc : IsFinite c) (hd : IsFinite d) (ht : IsInfinitesimal t) :
    IsFinite (q + t * c + t ^ 2 * d) :=
  finite_add (finite_add hq (finite_mul (finite_of_infinitesimal ht) hc))
    (finite_mul (finite_pow (finite_of_infinitesimal ht) 2) hd)

/-- The perturbation leaves the ordinary standard part unchanged. -/
theorem standardPart_quadratic_perturbation (q c d t : SignSequence.{u})
    (hq : IsFinite q) (hc : IsFinite c) (hd : IsFinite d) (ht : IsInfinitesimal t) :
    standardPart (q + t * c + t ^ 2 * d) = standardPart q := by
  have htc := infinitesimal_mul_finite ht hc
  have htd := infinitesimal_mul_finite ((infinitesimal_sq_iff t).mpr ht) hd
  have htcf := finite_of_infinitesimal htc
  have htdf := finite_of_infinitesimal htd
  rw [standardPart_add (finite_add hq htcf) htdf, standardPart_add hq htcf,
    (standardPart_eq_zero_iff htcf).mpr htc, (standardPart_eq_zero_iff htdf).mpr htd]
  simp only [_root_.add_zero]

/-- A nonzero residue prevents the perturbed denominator from vanishing. -/
theorem quadratic_perturbation_ne_zero (q c d t : SignSequence.{u})
    (hq : IsFinite q) (hq0 : standardPart q ≠ 0)
    (hc : IsFinite c) (hd : IsFinite d) (ht : IsInfinitesimal t) :
    q + t * c + t ^ 2 * d ≠ 0 := by
  intro he
  have hs := standardPart_quadratic_perturbation q c d t hq hc hd ht
  rw [he, standardPart_zero] at hs
  exact hq0 hs.symm

/-- The reciprocal of the perturbed denominator is finite. -/
theorem finite_inv_quadratic_perturbation (q c d t : SignSequence.{u})
    (hq : IsFinite q) (hq0 : standardPart q ≠ 0)
    (hc : IsFinite c) (hd : IsFinite d) (ht : IsInfinitesimal t) :
    IsFinite (q + t * c + t ^ 2 * d)⁻¹ := by
  apply finite_inv_of_standardPart_ne_zero (finite_quadratic_perturbation q c d t hq hc hd ht)
  rwa [standardPart_quadratic_perturbation q c d t hq hc hd ht]

/-- The reciprocal expansion is an exact identity with its full rational remainder displayed. -/
theorem reciprocal_quadratic_perturbation (q c d t : SignSequence.{u})
    (hq : q ≠ 0) (hden : q + t * c + t ^ 2 * d ≠ 0) :
    (q + t * c + t ^ 2 * d)⁻¹ = q⁻¹ - t * c / q ^ 2 +
      t ^ 2 * ((c ^ 2 - q * d + t * c * d) /
        (q ^ 2 * (q + t * c + t ^ 2 * d))) := by
  field_simp [hq, hden]
  ring

/-- The explicit second-order reciprocal remainder is finite for finite coefficients and an
infinitesimal parameter; the base is only required to have nonzero ordinary residue. -/
theorem finite_reciprocal_quadratic_remainder (q c d t : SignSequence.{u})
    (hq : IsFinite q) (hq0 : standardPart q ≠ 0)
    (hc : IsFinite c) (hd : IsFinite d) (ht : IsInfinitesimal t) :
    IsFinite ((c ^ 2 - q * d + t * c * d) /
      (q ^ 2 * (q + t * c + t ^ 2 * d))) := by
  have hnum := finite_add (finite_sub (finite_pow hc 2) (finite_mul hq hd))
    (finite_mul (finite_mul (finite_of_infinitesimal ht) hc) hd)
  have hqi := finite_inv_of_standardPart_ne_zero hq hq0
  have hdeni := finite_inv_quadratic_perturbation q c d t hq hq0 hc hd ht
  rw [div_eq_mul_inv, mul_inv_rev, ← inv_pow]
  exact finite_mul hnum (finite_mul hdeni (finite_pow hqi 2))

/-- Exact first-order reciprocal expansion with a finite normalized second-order remainder. -/
theorem exists_finite_reciprocal_expansion (q c d t : SignSequence.{u})
    (hq : IsFinite q) (hq0 : standardPart q ≠ 0)
    (hc : IsFinite c) (hd : IsFinite d) (ht : IsInfinitesimal t) :
    ∃ E : SignSequence.{u}, IsFinite E ∧
      (q + t * c + t ^ 2 * d)⁻¹ = q⁻¹ - t * c / q ^ 2 + t ^ 2 * E := by
  have hqne : q ≠ 0 := by intro he; exact hq0 (by simp [he])
  exact ⟨_, finite_reciprocal_quadratic_remainder q c d t hq hq0 hc hd ht,
    reciprocal_quadratic_perturbation q c d t hqne
      (quadratic_perturbation_ne_zero q c d t hq hq0 hc hd ht)⟩

end Surreal.Foundations.SignSequence
