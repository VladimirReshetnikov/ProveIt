import Surreal.Algebra.IntersectivePolynomial
import Surreal.HahnSeries.NonpositivePolynomialDegree

/-!
# The intersective polynomial has no intermediate Hahn-ring roots

The intermediate-ring clause of `odg:def:prop:intersective` (ii). Ordinary
root exclusion descends through the exact intersection with constants;
the intermediate ring need not be closed under constant extraction.
-/

namespace Surreal.HahnSeries

open IntersectivePolynomial

noncomputable section

variable {Γ K R : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field K] [CommRing R]

/-- Any embedded constant ring without roots of Lambda gives root exclusion in every
intermediate Hahn ring having precisely that constant intersection. -/
theorem intermediate_intersectivePolynomial_ne_zero
    (φ : R →+* K) (hφ : Function.Injective φ) (hroot : ∀ a : R, value a ≠ 0)
    (A : Subring (nonpositiveSupportSubring Γ K))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ φ.range) (x : A) : value x ≠ 0 := by
  have hp (c : φ.range) :
      (polynomial.map (Int.castRingHom K)).eval (c : K) ≠ 0 := by
    obtain ⟨a, ha⟩ := c.property
    have he : (polynomial.map (Int.castRingHom K)).eval (c : K) = value (c : K) := by
      simp [polynomial, value]
    rw [he, ← ha, ← map_value φ]
    exact (map_ne_zero_iff φ hφ).mpr (hroot a)
  have hn := intermediate_polynomial_no_root A φ.range hA
    (polynomial.map (Int.castRingHom K)) hp x
  have he : (polynomial.map (Int.castRingHom K)).eval₂ nonpositiveConstants x.val =
      value x.val := by simp [polynomial, value]
  rw [he] at hn
  intro hx
  apply hn
  have hv := congrArg A.subtype hx
  rw [map_value, map_zero] at hv
  exact hv

/-- Integer-constant intermediate rings have no roots of the fixed polynomial. -/
theorem integer_intermediate_intersectivePolynomial_ne_zero [CharZero K]
    (A : Subring (nonpositiveSupportSubring Γ K))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ (Int.castRingHom K).range)
    (x : A) : value x ≠ 0 :=
  intermediate_intersectivePolynomial_ne_zero (Int.castRingHom K) Int.cast_injective
    integer_value_ne_zero A hA x

/-- Gaussian-constant intermediate rings have no roots, in any field admitting the embedding. -/
theorem gaussian_intermediate_intersectivePolynomial_ne_zero
    (φ : GaussianInt →+* K) (hφ : Function.Injective φ)
    (A : Subring (nonpositiveSupportSubring Γ K))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ φ.range) (x : A) : value x ≠ 0 :=
  intermediate_intersectivePolynomial_ne_zero φ hφ gaussian_value_ne_zero A hA x

end
end Surreal.HahnSeries
