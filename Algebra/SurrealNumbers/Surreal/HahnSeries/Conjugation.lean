import Surreal.HahnSeries.Complexify

/-!
# Coefficientwise conjugation of complexified Hahn series

This proves the conjugation and fixed-subring claims underlying the fixed-field
clause of `polynomial:prop:workspace`. Conjugation preserves support and Hahn
order and agrees with conjugation of the real/imaginary pair. When the
coefficient field has characteristic zero, its fixed series are precisely the
embedded series over that field.

These are generic algebraic claims. They do not assert algebraic closedness,
real closedness, or a surreal embedding of either Hahn series ring.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

variable {Γ R : Type*} [AddCommMonoid Γ] [LinearOrder Γ]
  [IsOrderedCancelAddMonoid Γ]

section Ring

variable [CommRing R]

/-- Conjugate each quadratic coefficient. This is an involutive ring
automorphism, as used in `polynomial:prop:workspace`. -/
def conjugation : (Complexify R)⟦Γ⟧ ≃+* (Complexify R)⟦Γ⟧ where
  toFun z := z.map (starRingEnd (Complexify R))
  invFun z := z.map (starRingEnd (Complexify R))
  left_inv z := by
    apply _root_.HahnSeries.ext
    funext g
    exact star_star (z.coeff g)
  right_inv z := by
    apply _root_.HahnSeries.ext
    funext g
    exact star_star (z.coeff g)
  map_add' _ _ := _root_.HahnSeries.map_add
    (starRingEnd (Complexify R)).toAddMonoidHom
  map_mul' _ _ := _root_.HahnSeries.map_mul
    (starRingEnd (Complexify R)).toNonUnitalRingHom

@[simp] theorem coeff_conjugation (z : (Complexify R)⟦Γ⟧) (g : Γ) :
    (conjugation z).coeff g = star (z.coeff g) := rfl

@[simp] theorem conjugation_conjugation (z : (Complexify R)⟦Γ⟧) :
    conjugation (conjugation z) = z := by
  apply _root_.HahnSeries.ext
  funext g
  simp

/-- The Hahn/pair bridge respects conjugation in
`polynomial:prop:workspace`. -/
@[simp] theorem conjugation_complexifyToHahn (z : Complexify (R⟦Γ⟧)) :
    conjugation (complexifyToHahn z) = complexifyToHahn (star z) := by
  apply _root_.HahnSeries.ext
  funext g
  apply QuadraticAlgebra.ext <;> simp

@[simp] theorem hahnToComplexify_conjugation (z : (Complexify R)⟦Γ⟧) :
    hahnToComplexify (conjugation z) = star (hahnToComplexify z) := by
  apply QuadraticAlgebra.ext <;> ext g <;> simp

/-- Embedded base-coefficient Hahn series are fixed by conjugation. -/
@[simp] theorem conjugation_embedRealSeries (z : R⟦Γ⟧) :
    conjugation (embedRealSeries z) = embedRealSeries z := by
  apply _root_.HahnSeries.ext
  funext g
  apply QuadraticAlgebra.ext <;> simp

/-- Conjugation preserves exactly the exponents with nonzero coefficients. -/
@[simp] theorem support_conjugation (z : (Complexify R)⟦Γ⟧) :
    (conjugation z).support = z.support := by
  ext g
  simp only [mem_support, coeff_conjugation, ne_eq, star_eq_zero]

/-- In the increasing-exponent Hahn convention, conjugation preserves the
least exponent, including the value `⊤` for the zero series. -/
@[simp] theorem orderTop_conjugation (z : (Complexify R)⟦Γ⟧) :
    (conjugation z).orderTop = z.orderTop := by
  by_cases hz : z = 0
  · simp [hz]
  have hcoeff : z.coeff z.order ≠ 0 := coeff_order_eq_zero.not.mpr hz
  have horder : (conjugation z).orderTop = (z.order : WithTop Γ) := by
    apply orderTop_eq_of_le
    · simpa only [mem_support, coeff_conjugation, ne_eq, star_eq_zero] using hcoeff
    · intro g hg
      rw [support_conjugation] at hg
      exact order_le_of_coeff_ne_zero hg
  exact horder.trans (order_eq_orderTop_of_ne_zero hz)

end Ring

section FixedSubring

variable [Field R] [CharZero R]

/-- Characteristic zero excludes nonzero imaginary coefficients fixed by
negation; this is the coefficient-level fixed-subring assertion of
`polynomial:prop:workspace`. -/
theorem conjugation_eq_self_iff_im_eq_zero (z : (Complexify R)⟦Γ⟧) :
    conjugation z = z ↔ ∀ g, (z.coeff g).im = 0 := by
  constructor
  · intro h g
    have him := congrArg (fun w : (Complexify R)⟦Γ⟧ => (w.coeff g).im) h
    simpa only [coeff_conjugation, Complexify.conj_im, CharZero.neg_eq_self_iff] using him
  · intro h
    apply _root_.HahnSeries.ext
    funext g
    apply QuadraticAlgebra.ext <;> simp [h g]

/-- The fixed series are exactly the embedded base-coefficient Hahn series.
This proves the generic algebraic part of the fixed-field clause in
`polynomial:prop:workspace`; it does not assert that either ring is a field. -/
theorem conjugation_eq_self_iff_mem_range (z : (Complexify R)⟦Γ⟧) :
    conjugation z = z ↔ z ∈ Set.range
      (embedRealSeries : R⟦Γ⟧ →+* (Complexify R)⟦Γ⟧) := by
  constructor
  · intro h
    refine ⟨(hahnToComplexify z).re, ?_⟩
    have him := (conjugation_eq_self_iff_im_eq_zero z).mp h
    apply _root_.HahnSeries.ext
    funext g
    apply QuadraticAlgebra.ext <;> simp [him g]
  · rintro ⟨w, rfl⟩
    exact conjugation_embedRealSeries w

end FixedSubring

end
end Surreal.HahnSeries
