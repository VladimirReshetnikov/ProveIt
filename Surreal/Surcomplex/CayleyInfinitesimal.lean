import Surreal.Surcomplex.Cayley

/-!
# Infinite affine parameters near the projective half-turn

An infinite actual surreal parameter has infinitesimal reciprocal. The
rational chart commutes with standard part at finite parameters and inverts
by negative conjugation, so infinite parameters give directions near `-1`.
The converse distinguishes an infinite scalar parameter from the projective
point itself, which is not an actual surreal scalar.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

/-- Every actual Cayley value has finite coordinates. -/
theorem isFinite_cayley (t : SignSequence.{u}) : IsFinite (cayley t) := by
  apply (isFinite_iff_modulus _).mpr
  rw [modulus_cayley]
  exact SignSequence.finite_one

/-- At finite parameters, standard part acts on the rational coordinates coefficientwise. -/
theorem standardPart_cayley (t : SignSequence.{u}) (ht : SignSequence.IsFinite t) :
    standardPart (cayley t) =
      ⟨(1 - SignSequence.standardPart t ^ 2) / (1 + SignSequence.standardPart t ^ 2),
        2 * SignSequence.standardPart t / (1 + SignSequence.standardPart t ^ 2)⟩ := by
  have ht2 := SignSequence.finite_pow ht 2
  have hs2 : SignSequence.standardPart (t ^ 2) = SignSequence.standardPart t ^ 2 := by
    rw [pow_two, SignSequence.standardPart_mul ht ht, pow_two]
  have hd := SignSequence.finite_add SignSequence.finite_one ht2
  have hds : SignSequence.standardPart (1 + t ^ 2) = 1 + SignSequence.standardPart t ^ 2 := by
    rw [SignSequence.standardPart_add SignSequence.finite_one ht2, SignSequence.standardPart_one, hs2]
  have hn : SignSequence.standardPart (1 + t ^ 2) ≠ 0 := by rw [hds]; positivity
  have hi := SignSequence.finite_inv_of_standardPart_ne_zero hd hn
  have his := SignSequence.standardPart_inv_of_ne_zero hd hn
  have htwo : SignSequence.IsFinite (2 : SignSequence.{u}) := by
    simpa only [map_ofNat] using SignSequence.finite_ofReal (2 : ℝ)
  have htwos : SignSequence.standardPart (2 : SignSequence.{u}) = 2 := by
    simpa only [map_ofNat] using SignSequence.standardPart_ofReal (2 : ℝ)
  apply Complex.ext
  · change SignSequence.standardPart ((1 - t ^ 2) / (1 + t ^ 2)) = _
    rw [div_eq_mul_inv, SignSequence.standardPart_mul
      (SignSequence.finite_sub SignSequence.finite_one ht2) hi,
      SignSequence.standardPart_sub SignSequence.finite_one ht2,
      SignSequence.standardPart_one, hs2, his, hds]
    rfl
  · change SignSequence.standardPart (2 * t / (1 + t ^ 2)) = _
    rw [div_eq_mul_inv, SignSequence.standardPart_mul (SignSequence.finite_mul htwo ht) hi,
      SignSequence.standardPart_mul htwo ht, htwos, his, hds]
    rfl

/-- An infinitesimal affine parameter gives a direction with ordinary part one. -/
theorem standardPart_cayley_of_infinitesimal (t : SignSequence.{u})
    (ht : SignSequence.IsInfinitesimal t) : standardPart (cayley t) = 1 := by
  have hf := SignSequence.finite_of_infinitesimal ht
  have hs := (SignSequence.standardPart_eq_zero_iff hf).mpr ht
  convert standardPart_cayley t hf using 1
  simp [hs, Complex.ext_iff]

/-- Reciprocal parameters exchange the two real-axis directions by negative conjugation. -/
theorem cayley_inv (t : SignSequence.{u}) (ht : t ≠ 0) :
    cayley t⁻¹ = -conj (cayley t) := by
  have hd := (Complexify.circleParam_den_pos t).ne'
  have hdi := (Complexify.circleParam_den_pos t⁻¹).ne'
  apply QuadraticAlgebra.ext <;>
    simp only [cayley_re, cayley_im, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg,
      conj_re, conj_im, neg_neg] <;> field_simp <;> ring

/-- Every infinite actual parameter has ordinary Cayley direction `-1`. -/
theorem standardPart_cayley_of_not_finite (t : SignSequence.{u})
    (ht : ¬ SignSequence.IsFinite t) : standardPart (cayley t) = -1 := by
  have hn : t ≠ 0 := by intro h; exact ht (h ▸ SignSequence.finite_zero)
  have hi := (SignSequence.infinitesimal_inv_iff_not_finite hn).mpr ht
  have he := cayley_inv t⁻¹ (inv_ne_zero hn)
  rw [inv_inv] at he
  rw [he, standardPart_neg, standardPart_conj, standardPart_cayley_of_infinitesimal _ hi, star_one]

/-- An infinite scalar parameter gives a point infinitesimally close to the omitted half-turn. -/
theorem infinitesimal_cayley_add_one (t : SignSequence.{u})
    (ht : ¬ SignSequence.IsFinite t) : IsInfinitesimal (cayley t + 1) := by
  apply (standardPart_eq_zero_iff (finiteSubring.add_mem (isFinite_cayley t) finiteSubring.one_mem)).mp
  change standardPartHom (⟨cayley t, isFinite_cayley t⟩ + 1) = 0
  rw [map_add, map_one]
  change standardPart (cayley t) + 1 = 0
  rw [standardPart_cayley_of_not_finite t ht, neg_add_cancel]

/-- Conversely, a finite chart parameter cannot give a direction infinitesimally close to `-1`. -/
theorem infinitesimal_cayley_add_one_iff (t : SignSequence.{u}) :
    IsInfinitesimal (cayley t + 1) ↔ ¬ SignSequence.IsFinite t := by
  refine ⟨?_, infinitesimal_cayley_add_one t⟩
  intro hi ht
  have hr := congrArg Complex.re (standardPart_cayley t ht)
  have hp : 0 < 1 + SignSequence.standardPart (cayley t).re := by
    change 0 < 1 + (standardPart (cayley t)).re
    rw [hr]
    change 0 < 1 + (Complexify.circleParam (SignSequence.standardPart t)).re
    rw [Complexify.one_add_circleParam_re]
    exact div_pos (by norm_num) (Complexify.circleParam_den_pos _)
  have hs := (SignSequence.standardPart_eq_zero_iff
    (SignSequence.finite_add (isFinite_cayley t).1 SignSequence.finite_one)).mpr hi.1
  change SignSequence.standardPart ((cayley t).re + 1) = 0 at hs
  rw [SignSequence.standardPart_add (isFinite_cayley t).1 SignSequence.finite_one,
    SignSequence.standardPart_one] at hs
  linarith

/-- The explicit omega parameter is near `-1`, while remaining in the affine chart. -/
theorem infinitesimal_cayley_omega_add_one :
    IsInfinitesimal (cayley (SignSequence.ofOrdinal Ordinal.omega0 : SignSequence.{u}) + 1) := by
  apply infinitesimal_cayley_add_one
  have hn : (SignSequence.ofOrdinal Ordinal.omega0 : SignSequence.{u}) ≠ 0 := by
    intro h
    have hi := SignSequence.inv_omega0_pos.{u}
    rw [h, inv_zero] at hi
    exact lt_irrefl _ hi
  exact (SignSequence.infinitesimal_inv_iff_not_finite hn).mp SignSequence.infinitesimal_inv_omega0

end Surreal.Surcomplex
