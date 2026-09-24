import Mathlib.Data.Rat.Sqrt
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Tactic

/-!
# The intersective polynomial and its ordinary root obstruction

The polynomial in `odg:def:eq:Lambda` and the ordinary root-exclusion part
of `odg:def:prop:intersective`. The three radicands are positive rational
nonsquares, so no complex number with rational real and imaginary parts
can be a root.
-/

namespace Surreal.IntersectivePolynomial

open Polynomial

noncomputable section

/-- The manuscript's fixed integer polynomial. -/
def polynomial : ℤ[X] := (X ^ 2 - C 13) * (X ^ 2 - C 17) * (X ^ 2 - C 221)

/-- Its factored value over any commutative ring. -/
def value {R : Type*} [CommRing R] (x : R) : R :=
  (x ^ 2 - 13) * (x ^ 2 - 17) * (x ^ 2 - 221)

theorem polynomial_expanded :
    polynomial = X ^ 6 - C 251 * X ^ 4 + C 6851 * X ^ 2 - C 48841 := by
  simp only [polynomial, map_ofNat]
  ring

theorem eval₂_polynomial {R : Type*} [CommRing R] (x : R) :
    polynomial.eval₂ (Int.castRingHom R) x = value x := by
  simp [polynomial, value]

theorem map_value {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (x : R) :
    φ (value x) = value (φ x) := by
  simp only [value, map_mul, map_sub, map_pow, map_ofNat]

/-- All three radicands are positive and fail the decidable rational square test. -/
theorem radicands_positive_nonsquare (d : ℚ) (hd : d = 13 ∨ d = 17 ∨ d = 221) :
    0 < d ∧ ¬IsSquare d := by
  constructor
  · rcases hd with rfl | rfl | rfl <;> norm_num
  · rintro ⟨q, hq⟩
    have he := (Rat.exists_mul_self d).mp ⟨q, hq.symm⟩
    rcases hd with rfl | rfl | rfl <;> norm_num at he

/-- A positive rational nonsquare cannot be a square of a rational complex number. -/
theorem rational_complex_square_ne (d : ℚ) (hd : 0 < d) (hs : ¬IsSquare d) (a b : ℚ) :
    ((a : ℂ) + (b : ℂ) * Complex.I) ^ 2 ≠ (d : ℂ) := by
  intro h
  have hre : a ^ 2 - b ^ 2 = d := by
    have he := congrArg Complex.re h
    simp [pow_two, Complex.mul_re, Complex.mul_im] at he
    simpa only [pow_two] using (show a * a - b * b = d by exact_mod_cast he)
  have him : 2 * a * b = 0 := by
    have he := congrArg Complex.im h
    simp [pow_two, Complex.mul_re, Complex.mul_im] at he
    have he' : a * b + b * a = 0 := by exact_mod_cast he
    nlinarith [he']
  rcases mul_eq_zero.mp him with hab | hb
  · have ha : a = 0 := (mul_eq_zero.mp hab).resolve_left (by norm_num)
    rw [ha] at hre
    nlinarith [sq_nonneg b]
  · rw [hb, zero_pow (by decide), sub_zero] at hre
    exact hs ⟨a, by nlinarith [hre]⟩

/-- The polynomial has no root with rational real and imaginary coordinates. -/
theorem rational_complex_value_ne_zero (a b : ℚ) :
    value ((a : ℂ) + (b : ℂ) * Complex.I) ≠ 0 := by
  intro h
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact rational_complex_square_ne 13 (by norm_num) (radicands_positive_nonsquare _ (by tauto)).2 a b
        (by simpa using sub_eq_zero.mp h)
    · exact rational_complex_square_ne 17 (by norm_num) (radicands_positive_nonsquare _ (by tauto)).2 a b
        (by simpa using sub_eq_zero.mp h)
  · exact rational_complex_square_ne 221 (by norm_num) (radicands_positive_nonsquare _ (by tauto)).2 a b
      (by simpa using sub_eq_zero.mp h)

/-- Rational real and imaginary coordinates form the ordinary Gaussian rational field. -/
def rationalComplexField : IntermediateField ℚ ℂ where
  carrier := {z | ∃ a b : ℚ, z = (a : ℂ) + (b : ℂ) * Complex.I}
  zero_mem' := ⟨0, 0, by simp⟩
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro z w ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    exact ⟨a + c, b + d, by push_cast; ring⟩
  mul_mem' := by
    rintro z w ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    refine ⟨a * c - b * d, a * d + b * c, ?_⟩
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  inv_mem' := by
    rintro z ⟨a, b, rfl⟩
    refine ⟨a / (a ^ 2 + b ^ 2), -b / (a ^ 2 + b ^ 2), ?_⟩
    apply Complex.ext <;>
      simp only [Complex.inv_re, Complex.inv_im, Complex.normSq_apply,
        Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
        mul_zero, mul_one, add_zero, zero_add, sub_zero] <;>
      push_cast <;> ring
  algebraMap_mem' q := ⟨q, 0, by simp⟩

/-- The rational-coordinate field is precisely Mathlib's field obtained by adjoining i to Q. -/
theorem rationalComplexField_eq_adjoin :
    rationalComplexField = IntermediateField.adjoin ℚ {Complex.I} := by
  apply le_antisymm
  · rintro z ⟨a, b, rfl⟩
    exact add_mem ((IntermediateField.adjoin ℚ {Complex.I}).algebraMap_mem a)
      (mul_mem ((IntermediateField.adjoin ℚ {Complex.I}).algebraMap_mem b)
        (IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton Complex.I)))
  · apply IntermediateField.adjoin_le_iff.mpr
    intro z hz
    have hz : z = Complex.I := Set.mem_singleton_iff.mp hz
    exact ⟨0, 1, by simp [hz]⟩

/-- The root exclusion on the native Q(i) intermediate field. -/
theorem gaussian_rational_value_ne_zero (z : IntermediateField.adjoin ℚ {Complex.I}) :
    value z ≠ 0 := by
  intro h
  have hz : z.val ∈ rationalComplexField := by
    rw [rationalComplexField_eq_adjoin]
    exact z.property
  obtain ⟨a, b, hab⟩ := hz
  apply rational_complex_value_ne_zero a b
  have he := congrArg (IntermediateField.adjoin ℚ {Complex.I}).val.toRingHom h
  rw [map_value, map_zero] at he
  change value z.val = 0 at he
  rwa [hab] at he

/-- In particular the polynomial has no Gaussian integer root. -/
theorem gaussian_value_ne_zero (a : GaussianInt) : value a ≠ 0 := by
  intro h
  have he := congrArg GaussianInt.toComplex h
  rw [map_value, map_zero] at he
  apply rational_complex_value_ne_zero (a.re : ℚ) (a.im : ℚ)
  have hr : GaussianInt.toComplex a =
      ((a.re : ℚ) : ℂ) + ((a.im : ℚ) : ℂ) * Complex.I := by
    simp only [Rat.cast_intCast]
    apply Complex.ext <;>
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im,
        ← GaussianInt.intCast_re, ← GaussianInt.intCast_im] <;> ring
  rw [← hr]
  exact he

/-- In particular the polynomial has no ordinary integer root. -/
theorem integer_value_ne_zero (a : ℤ) : value a ≠ 0 := by
  intro h
  apply gaussian_value_ne_zero (a : GaussianInt)
  have he := congrArg (Int.castRingHom GaussianInt) h
  rw [map_value, map_zero] at he
  exact he

end
end Surreal.IntersectivePolynomial
