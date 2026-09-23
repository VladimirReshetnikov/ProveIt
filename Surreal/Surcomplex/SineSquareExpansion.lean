import Surreal.Surcomplex.TrigonometricLeading
import Surreal.Foundations.SignSequenceRelativeAsymptotics

/-!
# A unit quadratic remainder for the sine-square stability examples

The family used in `trigonometry:prop:sharp` has an exact expansion
`sin²(a+h) = sin²(a) + sin(2a) h + h² Q`, with finite `Q` of residue one
when both angles are infinitesimal. This gives exact valuations of the
second-order error without an Archimedean convergence argument.
-/

universe u

namespace Surreal.Surcomplex.SineSquare

open Foundations

noncomputable section

/-- The source's sine-square family, with a fixed constant subtracted. -/
def function (b x : SignSequence.{u}) : SignSequence.{u} := sinFunction x ^ 2 - b

/-- Its angular derivative, written using the double-angle identity. -/
def slope (a : SignSequence.FiniteElement.{u}) : SignSequence.{u} := finiteSin (2 * a)

@[simp] theorem function_eval (b : SignSequence.{u}) (a : SignSequence.FiniteElement.{u}) :
    function b a.val = finiteSin a ^ 2 - b := by
  rw [function, sinFunction_eq_finiteSin]

/-- The derivative is a native fine derivative of the actual sine-square function. -/
theorem fineHasDerivAt_function (b : SignSequence.{u}) (a : SignSequence.FiniteElement.{u}) :
    FineHasDerivAt (function b) (slope a) a.val := by
  unfold function
  have hd := ((fineHasDerivAt_sinFunction a.val a.property).pow 2).sub
    (FineHasDerivAt.const b a.val)
  simpa only [slope, finiteSin_two_mul, sinFunction_eq_finiteSin,
    cosFunction_eq_finiteCos, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, sub_zero] using hd

/-- The slope of an infinitesimal sine-square root has exactly the angle's valuation. -/
theorem valuation_slope (a : SignSequence.FiniteElement.{u})
    (ha : SignSequence.IsInfinitesimal a.val) :
    SignSequence.valuation (slope a) = SignSequence.valuation a.val := by
  have h2f : SignSequence.IsFinite (2 : SignSequence.{u}) := by
    simpa only [map_ofNat] using SignSequence.finite_ofReal (2 : ℝ)
  have h2v : SignSequence.valuation (2 : SignSequence.{u}) = 0 := by
    apply (SignSequence.valuation_eq_zero_iff_standardPart_ne_zero h2f).mpr
    have hs : SignSequence.standardPart (2 : SignSequence.{u}) = 2 := by
      simpa only [map_ofNat] using SignSequence.standardPart_ofReal (2 : ℝ)
    rw [hs]
    norm_num
  have hcv : SignSequence.valuation (finiteCos a) = 0 := by
    apply (SignSequence.valuation_eq_zero_iff_standardPart_ne_zero (isFinite_finiteCos a)).mpr
    rw [standardPart_finiteCos_of_isInfinitesimal a ha]
    exact one_ne_zero
  rw [slope, finiteSin_two_mul, SignSequence.valuation_mul, SignSequence.valuation_mul,
    h2v, hcv, zero_add, add_zero, valuation_finiteSin_of_isInfinitesimal a ha]

/-- The exact addition law isolates the linear sine-square term. -/
theorem add_identity (a h : SignSequence.FiniteElement.{u}) :
    finiteSin (a + h) ^ 2 = finiteSin a ^ 2 +
      slope a * finiteSin h * finiteCos h + finiteCos (2 * a) * finiteSin h ^ 2 := by
  rw [finiteSin_add, slope, finiteSin_two_mul, finiteCos_two_mul]
  linear_combination finiteSin a ^ 2 * (finiteCos_sq_add_finiteSin_sq h)

/-- Sine has a finite cubic remainder after its linear term. -/
theorem sin_cubic_remainder (h : SignSequence.FiniteElement.{u})
    (hh : SignSequence.IsInfinitesimal h.val) :
    ∃ S : SignSequence.{u}, SignSequence.IsFinite S ∧ finiteSin h = h.val + h.val ^ 3 * S := by
  obtain ⟨S, hS, _, he⟩ := SignSequence.exists_finite_powerSeries_remainder h.val hh
    (Analytic.taylorSeries Real.sin 0) 3
  rw [← finiteSin_eq_powerSeries_of_isInfinitesimal h hh] at he
  norm_num [Finset.sum_range_succ, Analytic.coeff_taylorSeries_sin_zero] at he
  exact ⟨S, hS, he⟩

/-- The quadratic remainder is a finite unit with residue one at every infinitesimal center. -/
theorem quadratic_remainder (a h : SignSequence.FiniteElement.{u})
    (ha : SignSequence.IsInfinitesimal a.val) (hh : SignSequence.IsInfinitesimal h.val) :
    ∃ Q : SignSequence.{u}, SignSequence.IsFinite Q ∧ SignSequence.standardPart Q = 1 ∧
      finiteSin (a + h) ^ 2 = finiteSin a ^ 2 + slope a * h.val + h.val ^ 2 * Q := by
  obtain ⟨S, hS, hs⟩ := sin_cubic_remainder h hh
  obtain ⟨C, hC, _, hc⟩ := one_sub_finiteCos_leading_factor h hh
  obtain ⟨R, hR, hr, he⟩ := finiteSin_leading_factor h hh
  let S' : SignSequence.FiniteElement.{u} := ⟨S, hS⟩
  let C' : SignSequence.FiniteElement.{u} := ⟨C, hC⟩
  let R' : SignSequence.FiniteElement.{u} := ⟨R, hR⟩
  let A' : SignSequence.FiniteElement.{u} := ⟨slope a, isFinite_finiteSin (2 * a)⟩
  let ch : SignSequence.FiniteElement.{u} := ⟨finiteCos h, isFinite_finiteCos h⟩
  let ca : SignSequence.FiniteElement.{u} := ⟨finiteCos (2 * a), isFinite_finiteCos (2 * a)⟩
  let Q : SignSequence.FiniteElement.{u} := A' * h * (S' * ch - C') + ca * R' ^ 2
  have h2a : SignSequence.IsInfinitesimal (2 * a).val := by
    rw [two_mul, ArchimedeanClass.FiniteElement.val_add]
    exact SignSequence.infinitesimal_add ha ha
  have hstdh : SignSequence.standardPartHom h = 0 :=
    (SignSequence.standardPart_eq_zero_iff h.property).mpr hh
  have hstdca : SignSequence.standardPartHom ca = 1 :=
    standardPart_finiteCos_of_isInfinitesimal (2 * a) h2a
  have hstdR : SignSequence.standardPartHom R' = 1 := hr
  refine ⟨Q.val, Q.property, ?_, ?_⟩
  · change SignSequence.standardPartHom Q = 1
    simp only [Q, map_add, map_mul, map_sub, map_pow, hstdh, hstdca, hstdR,
      mul_zero, zero_mul, zero_add, one_pow, one_mul]
  · change finiteSin (a + h) ^ 2 = finiteSin a ^ 2 + slope a * h.val +
      h.val ^ 2 * (slope a * h.val * (S * finiteCos h - C) + finiteCos (2 * a) * R ^ 2)
    have hlinear : finiteSin h * finiteCos h = h.val + h.val ^ 3 * (S * finiteCos h - C) := by
      linear_combination finiteCos h * hs - h.val * hc
    rw [add_identity, mul_assoc (slope a), hlinear, he]
    ring

end
end Surreal.Surcomplex.SineSquare
