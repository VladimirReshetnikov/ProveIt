import Surreal.Algebra.Complexify
import Mathlib.RingTheory.HahnSeries.Multiplication

/-!
# Complexification commutes with Hahn series

This is the coefficientwise algebraic bridge `K_Γ = F_Γ[i]` used in
`polynomial:prop:workspace`. A Hahn series with coefficients in `R[i]`
is equivalent as a ring to a pair of Hahn series over `R` with the correct
quadratic multiplication. The coefficient and support formulas are explicit.

Both constructions reuse Mathlib. No surreal embedding, divisibility of the
value group, algebraic closedness, or order on the coefficient ring is needed
for this finite algebraic bridge.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

variable {Γ R : Type*} [AddCommMonoid Γ] [LinearOrder Γ]
  [IsOrderedCancelAddMonoid Γ] [CommRing R]

/-- Embed each coefficient into its quadratic extension. -/
def embedRealSeries : R⟦Γ⟧ →+* (Complexify R)⟦Γ⟧ where
  toFun x := x.map (algebraMap R (Complexify R))
  map_zero' := _root_.HahnSeries.map_zero (algebraMap R (Complexify R)).toZeroHom
  map_one' := _root_.HahnSeries.map_one (algebraMap R (Complexify R)).toMonoidWithZeroHom
  map_add' _ _ := _root_.HahnSeries.map_add (algebraMap R (Complexify R)).toAddMonoidHom
  map_mul' _ _ := _root_.HahnSeries.map_mul (algebraMap R (Complexify R)).toNonUnitalRingHom

@[simp] theorem coeff_embedRealSeries (x : R⟦Γ⟧) (g : Γ) :
    (embedRealSeries x).coeff g = algebraMap R (Complexify R) (x.coeff g) := rfl

local instance complexifyHahnAlgebra : Algebra R⟦Γ⟧ (Complexify R)⟦Γ⟧ :=
  embedRealSeries.toAlgebra

/-- Apply the quadratic-algebra universal property to the constant imaginary unit. -/
def complexifyToHahn : Complexify (R⟦Γ⟧) →+* (Complexify R)⟦Γ⟧ :=
  (QuadraticAlgebra.lift ⟨C Complexify.I, by
    rw [← map_mul, ← pow_two, Complexify.I_sq, map_neg, map_one]
    simp [Algebra.smul_def]⟩).toRingHom

/-- The bridge preserves the real and imaginary coefficient at every exponent. -/
@[simp] theorem coeff_complexifyToHahn (z : Complexify (R⟦Γ⟧)) (g : Γ) :
    (complexifyToHahn z).coeff g = ⟨z.re.coeff g, z.im.coeff g⟩ := by
  change (embedRealSeries z.re * 1 + embedRealSeries z.im * C Complexify.I).coeff g = _
  rw [mul_one, coeff_add, C_apply, coeff_mul_single_zero]
  ext <;> simp [Complexify.I]

/-- Split each quadratic coefficient into two Hahn series. Mapping a
zero-preserving function only shrinks the support. -/
def hahnToComplexify (z : (Complexify R)⟦Γ⟧) : Complexify (R⟦Γ⟧) :=
  ⟨z.map (QuadraticAlgebra.reₗ (-1) 0), z.map (QuadraticAlgebra.imₗ (-1) 0)⟩

@[simp] theorem coeff_hahnToComplexify_re (z : (Complexify R)⟦Γ⟧) (g : Γ) :
    (hahnToComplexify z).re.coeff g = (z.coeff g).re := rfl

@[simp] theorem coeff_hahnToComplexify_im (z : (Complexify R)⟦Γ⟧) (g : Γ) :
    (hahnToComplexify z).im.coeff g = (z.coeff g).im := rfl

theorem hahnToComplexify_re_support_subset (z : (Complexify R)⟦Γ⟧) :
    (hahnToComplexify z).re.support ⊆ z.support :=
  support_map_subset z (QuadraticAlgebra.reₗ (-1) 0).toAddMonoidHom.toZeroHom

theorem hahnToComplexify_im_support_subset (z : (Complexify R)⟦Γ⟧) :
    (hahnToComplexify z).im.support ⊆ z.support :=
  support_map_subset z (QuadraticAlgebra.imₗ (-1) 0).toAddMonoidHom.toZeroHom

@[simp] theorem hahnToComplexify_complexifyToHahn (z : Complexify (R⟦Γ⟧)) :
    hahnToComplexify (complexifyToHahn z) = z := by
  apply QuadraticAlgebra.ext <;> ext g <;> simp

@[simp] theorem complexifyToHahn_hahnToComplexify (z : (Complexify R)⟦Γ⟧) :
    complexifyToHahn (hahnToComplexify z) = z := by
  apply _root_.HahnSeries.ext
  funext g
  rw [coeff_complexifyToHahn]
  rfl

/-- The ring-level identification in `polynomial:prop:workspace`, before
any surreal or algebraic-closure interpretation. -/
def complexifyHahnEquiv : Complexify (R⟦Γ⟧) ≃+* (Complexify R)⟦Γ⟧ :=
  { complexifyToHahn with
    invFun := hahnToComplexify
    left_inv := hahnToComplexify_complexifyToHahn
    right_inv := complexifyToHahn_hahnToComplexify }

/-- The support of the combined series is exactly the union of the two
component supports; in particular this construction preserves small supports. -/
theorem support_complexifyToHahn (z : Complexify (R⟦Γ⟧)) :
    (complexifyToHahn z).support = z.re.support ∪ z.im.support := by
  ext g
  simp only [mem_support, coeff_complexifyToHahn, ne_eq, QuadraticAlgebra.ext_iff,
    QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, Set.mem_union]
  simp only [not_and_or]

end
end Surreal.HahnSeries
