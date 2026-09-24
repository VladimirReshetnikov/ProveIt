import Surreal.Algebra.QuadraticEmbeddedObstruction
import Surreal.HahnSeries.IntersectiveIdealTest
import Surreal.HahnSeries.ConstantTermGraph

/-!
# Failure of the quadratic ideal test when the radicand becomes a square

The fraction-field obstruction at the start of `odg:def:rem:numberfieldideal`.
A nonzero ordinary solution is a false positive, even when the square root
belongs only to the fraction field of the coefficient ring. The concrete
Z[sqrt(2)] example is already proved in `QuadraticIdealBoundary`.
-/

namespace Surreal.HahnSeries
noncomputable section

variable {Γ L O : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Field L] [CommRing O]

/-- Any nonzero ordinary quadratic solution gives a non-purely-infinite element passing the test. -/
theorem coefficientRestricted_quadratic_false_positive (i : O →+* L) (hi : Function.Injective i)
    (δ : ℕ) (a b : O) (ha : a ≠ 0) (hab : a ^ 2 = (δ : O) * b ^ 2) :
    ∃ x : coefficientRestrictedSubring (Γ := Γ) i,
      x ∉ coefficientRestrictedPurelyInfiniteIdeal i ∧
        ∃ y : coefficientRestrictedSubring (Γ := Γ) i, x ^ 2 = (δ : _) * y ^ 2 := by
  refine ⟨coefficientRestrictedConstants i a, ?_, coefficientRestrictedConstants i b, ?_⟩
  · change nonpositiveConstantCoeff (nonpositiveConstants (i a)) ≠ 0
    rw [nonpositiveConstantCoeff_constants]
    exact (map_ne_zero_iff i hi).mpr ha
  · have he := congrArg (coefficientRestrictedConstants (Γ := Γ) i) hab
    simp only [map_pow, map_mul, map_natCast] at he
    exact he

/-- A square in the fraction field is enough; the square root need not belong to the coefficient ring. -/
theorem coefficientRestricted_quadratic_false_positive_of_fraction_square [IsDomain O]
    (i : O →+* L) (hi : Function.Injective i) (δ : ℕ) (hd : (δ : O) ≠ 0)
    (hs : IsSquare (algebraMap O (FractionRing O) (δ : O))) :
    ∃ x : coefficientRestrictedSubring (Γ := Γ) i,
      x ∉ coefficientRestrictedPurelyInfiniteIdeal i ∧
        ∃ y : coefficientRestrictedSubring (Γ := Γ) i, x ^ 2 = (δ : _) * y ^ 2 := by
  obtain ⟨a, b, ha, hab⟩ := QuadraticIdeal.exists_nonzero_quadratic_of_fraction_square (δ : O) hd hs
  exact coefficientRestricted_quadratic_false_positive i hi δ a b ha hab

end
end Surreal.HahnSeries
