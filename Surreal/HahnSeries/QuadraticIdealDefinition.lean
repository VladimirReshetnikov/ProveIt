import Surreal.HahnSeries.NonpositiveSupportUnits
import Surreal.Algebra.QuadraticIdealDefinition
import Surreal.Algebra.QuadraticConstantObstruction

/-!
# Quadratic definitions of purely infinite ideals in arbitrary Hahn workspaces

The general assertion of `odg:def:thm:ideal`, its other-radicand variant
`odg:def:rem:delta`, and `odg:def:cor:idealhom`. The full coefficient
pullback is used, so all zero-constant series and their coefficient-field
scalar multiples are present. No exponent-group divisibility is assumed.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

variable {Γ K O : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field K] [CommRing O]

attribute [local instance] nonpositiveSupportAlgebra

/-- The full ring of nonpositive-support series with constant coefficient in the embedded ring. -/
abbrev coefficientRestrictedSubring (i : O →+* K) : Subring (nonpositiveSupportSubring Γ K) :=
  CoefficientPullback.subring nonpositiveConstantCoeff i

/-- Constants of the restricted coefficient ring embed in the full pullback. -/
def coefficientRestrictedConstants (i : O →+* K) : O →+* coefficientRestrictedSubring (Γ := Γ) i :=
  CoefficientPullback.sectionMap (nonpositiveConstantCoeff (Γ := Γ) (R := K)) i
    (nonpositiveConstants (Γ := Γ)) (nonpositiveConstantCoeff_constants (Γ := Γ))

/-- Any radicand nonsquare in the fraction field, but with a root in the coefficient field,
defines the purely infinite ideal by a single quadratic equation. -/
theorem coefficientRestricted_quadratic_iff [IsDomain O] (i : O →+* K)
    (hi : Function.Injective i) (δ : O)
    (hn : ¬ IsSquare (algebraMap O (FractionRing O) δ)) (r : K) (hr : r ^ 2 = i δ)
    (x : coefficientRestrictedSubring (Γ := Γ) i) :
    x.val ∈ purelyInfiniteIdeal ↔ ∃ y : coefficientRestrictedSubring (Γ := Γ) i,
      x ^ 2 = coefficientRestrictedConstants i δ * y ^ 2 := by
  have hd : δ ≠ 0 := by
    intro h
    apply hn
    rw [h, map_zero]
    exact ⟨0, by simp⟩
  have hr0 : r ≠ 0 := by
    intro h
    have he : i δ = 0 := by simpa [h] using hr.symm
    exact hd (hi (he.trans i.map_zero.symm))
  exact QuadraticIdeal.kernel_iff_quadratic (nonpositiveConstantCoeffAlgHom (Γ := Γ) (K := K)) i hi δ r hr hr0
    (QuadraticIdeal.zero_of_nonsquare_fraction (Q := FractionRing O) δ hn)
    (coefficientRestrictedConstants i δ) rfl x

/-- The numeral-two formula in every integer-constant Hahn ring containing a square root of two. -/
theorem integerRestricted_purelyInfinite_iff_quadratic [CharZero K]
    (r : K) (hr : r ^ 2 = 2)
    (x : coefficientRestrictedSubring (Γ := Γ) (Int.castRingHom K)) :
    x.val ∈ purelyInfiniteIdeal ↔
      ∃ y : coefficientRestrictedSubring (Γ := Γ) (Int.castRingHom K), x ^ 2 = 2 * y ^ 2 := by
  have hr0 : r ≠ 0 := by intro h; norm_num [h] at hr
  exact QuadraticIdeal.kernel_iff_quadratic (nonpositiveConstantCoeffAlgHom (Γ := Γ) (K := K))
    (Int.castRingHom K) Int.cast_injective 2 r (by simpa only [map_ofNat] using hr) hr0
    QuadraticIdeal.integer_square_eq_two_zero 2 (by
      change (2 : nonpositiveSupportSubring Γ K) = algebraMap K _ ((Int.castRingHom K) 2)
      simp only [map_ofNat]) x

/-- The numeral-two formula also works for any embedded Gaussian coefficient ring. -/
theorem gaussianRestricted_purelyInfinite_iff_quadratic [CharZero K]
    (i : GaussianInt →+* K) (hi : Function.Injective i) (r : K) (hr : r ^ 2 = 2)
    (x : coefficientRestrictedSubring (Γ := Γ) i) :
    x.val ∈ purelyInfiniteIdeal ↔
      ∃ y : coefficientRestrictedSubring (Γ := Γ) i, x ^ 2 = 2 * y ^ 2 := by
  have hr0 : r ≠ 0 := by intro h; norm_num [h] at hr
  exact QuadraticIdeal.kernel_iff_quadratic (nonpositiveConstantCoeffAlgHom (Γ := Γ) (K := K)) i hi 2 r
    (by simpa only [map_ofNat] using hr) hr0 QuadraticIdeal.gaussian_square_eq_two_zero
    2 (by
      change (2 : nonpositiveSupportSubring Γ K) = algebraMap K _ (i 2)
      simp only [map_ofNat]) x

/-- Arbitrary unital homomorphisms between integer-constant Hahn rings preserve their
purely infinite ideals, independently of both exponent groups and coefficient fields. -/
theorem integerRestricted_hom_preserves_purelyInfinite
    {Δ E : Type*} [AddCommGroup Δ] [LinearOrder Δ] [IsOrderedAddMonoid Δ]
    [Field E] [CharZero K] [CharZero E] (r : K) (hr : r ^ 2 = 2) (s : E) (hs : s ^ 2 = 2)
    (φ : coefficientRestrictedSubring (Γ := Γ) (Int.castRingHom K) →+*
      coefficientRestrictedSubring (Γ := Δ) (Int.castRingHom E))
    (x : coefficientRestrictedSubring (Γ := Γ) (Int.castRingHom K))
    (hx : x.val ∈ purelyInfiniteIdeal) : (φ x).val ∈ purelyInfiniteIdeal :=
  (integerRestricted_purelyInfinite_iff_quadratic s hs _).mpr
    (QuadraticIdeal.map_quadratic_witness φ x
      ((integerRestricted_purelyInfinite_iff_quadratic r hr x).mp hx))

/-- The same homomorphism invariance holds for Gaussian coefficient rings; the map need
not fix a chosen imaginary unit, a square root of two, or any monomial. -/
theorem gaussianRestricted_hom_preserves_purelyInfinite
    {Δ E : Type*} [AddCommGroup Δ] [LinearOrder Δ] [IsOrderedAddMonoid Δ]
    [Field E] [CharZero K] [CharZero E]
    (i : GaussianInt →+* K) (hi : Function.Injective i)
    (j : GaussianInt →+* E) (hj : Function.Injective j)
    (r : K) (hr : r ^ 2 = 2) (s : E) (hs : s ^ 2 = 2)
    (φ : coefficientRestrictedSubring (Γ := Γ) i →+* coefficientRestrictedSubring (Γ := Δ) j)
    (x : coefficientRestrictedSubring (Γ := Γ) i) (hx : x.val ∈ purelyInfiniteIdeal) :
    (φ x).val ∈ purelyInfiniteIdeal :=
  (gaussianRestricted_purelyInfinite_iff_quadratic j hj s hs _).mpr
    (QuadraticIdeal.map_quadratic_witness φ x
      ((gaussianRestricted_purelyInfinite_iff_quadratic i hi r hr x).mp hx))

end
end Surreal.HahnSeries
