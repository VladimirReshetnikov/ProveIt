import Surreal.Algebra.ConstantTermHomomorphisms
import Surreal.HahnSeries.ConstantTermGraph

/-!
# Constant terms under all homomorphisms of coefficient-restricted Hahn rings

The full scope of `odg:def:thm:homct`: the two exponent groups and fields
may differ, and both fields need only characteristic zero and a square
root of two. The maps are arbitrary unital ring homomorphisms.
-/

namespace Surreal.HahnSeries

noncomputable section

variable {Γ Δ K E O : Type*}
  [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [AddCommGroup Δ] [LinearOrder Δ] [IsOrderedAddMonoid Δ]
  [Field K] [Field E] [CommRing O]

/-- The ordinary-constant inclusion into a full Hahn pullback is injective. -/
theorem coefficientRestrictedConstants_injective (i : O →+* K) (hi : Function.Injective i) :
    Function.Injective (coefficientRestrictedConstants (Γ := Γ) i) := by
  have h : Function.LeftInverse (coefficientRestrictedRetraction (Γ := Γ) i hi)
      (coefficientRestrictedConstants (Γ := Γ) i) :=
    CoefficientPullback.retraction_sectionMap (nonpositiveConstantCoeff (Γ := Γ) (R := K))
      i hi nonpositiveConstants nonpositiveConstantCoeff_constants
  exact h.injective

/-- All integer-coefficient Hahn homomorphisms preserve the ordinary integer constant term. -/
theorem integerRestricted_hom_constant [CharZero K] [CharZero E]
    (r : K) (hr : r ^ 2 = 2) (s : E) (hs : s ^ 2 = 2)
    (φ : coefficientRestrictedSubring (Γ := Γ) (Int.castRingHom K) →+*
      coefficientRestrictedSubring (Γ := Δ) (Int.castRingHom E))
    (x : coefficientRestrictedSubring (Γ := Γ) (Int.castRingHom K)) :
    coefficientRestrictedRetraction (Int.castRingHom E) Int.cast_injective (φ x) =
      coefficientRestrictedRetraction (Int.castRingHom K) Int.cast_injective x :=
  ConstantTermGraph.integer_hom_constant
    (coefficientRestrictedRetraction (Γ := Γ) (Int.castRingHom K) Int.cast_injective)
    (coefficientRestrictedConstants (Γ := Γ) (Int.castRingHom K))
    (coefficientRestrictedRetraction (Γ := Δ) (Int.castRingHom E) Int.cast_injective)
    (coefficientRestrictedConstants (Γ := Δ) (Int.castRingHom E))
    (coefficientRestrictedConstants_injective _ Int.cast_injective)
    (integerRestricted_constantTermGraph_iff r hr)
    (integerRestricted_constantTermGraph_iff s hs) φ x

/-- In the Gaussian case the sign of the image of i fixes a single action on all constant terms. -/
theorem gaussianRestricted_hom_constant [CharZero K] [CharZero E]
    (i : GaussianInt →+* K) (hi : Function.Injective i)
    (j : GaussianInt →+* E) (hj : Function.Injective j)
    (r : K) (hr : r ^ 2 = 2) (s : E) (hs : s ^ 2 = 2)
    (φ : coefficientRestrictedSubring (Γ := Γ) i →+* coefficientRestrictedSubring (Γ := Δ) j) :
    (φ (coefficientRestrictedConstants (Γ := Γ) i Zsqrtd.sqrtd) =
      coefficientRestrictedConstants (Γ := Δ) j Zsqrtd.sqrtd ∧
        ∀ x, coefficientRestrictedRetraction j hj (φ x) = coefficientRestrictedRetraction i hi x) ∨
    (φ (coefficientRestrictedConstants (Γ := Γ) i Zsqrtd.sqrtd) =
      -coefficientRestrictedConstants (Γ := Δ) j Zsqrtd.sqrtd ∧
        ∀ x, coefficientRestrictedRetraction j hj (φ x) = star (coefficientRestrictedRetraction i hi x)) :=
  ConstantTermGraph.gaussian_hom_constant
    (coefficientRestrictedRetraction (Γ := Γ) i hi) (coefficientRestrictedConstants (Γ := Γ) i)
    (coefficientRestrictedRetraction (Γ := Δ) j hj) (coefficientRestrictedConstants (Γ := Δ) j)
    (coefficientRestrictedConstants_injective j hj)
    (gaussianRestricted_constantTermGraph_iff i hi r hr)
    (gaussianRestricted_constantTermGraph_iff j hj s hs) φ

end
end Surreal.HahnSeries
