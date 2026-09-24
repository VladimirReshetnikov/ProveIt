import Surreal.Algebra.QuadraticEmbeddedObstruction
import Surreal.Algebra.NumberFieldQuadraticRadicand
import Surreal.HahnSeries.NumberFieldDetector

/-!
# One-witness quadratic definitions for number-field coefficient ideals

The ideal clause of `odg:def:rem:numberfieldideal`. Any natural radicand
nonsquare in the number field, but with a root in the larger coefficient
field, gives the definition. No root of the tailored sextic is required.
-/

namespace Surreal.HahnSeries
noncomputable section

variable {Γ K L : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Field K] [Field L]
variable (o : Subring K) (j : K →+* L)

attribute [local instance] nonpositiveSupportAlgebra
local notation "A" => coefficientRestrictedSubring (Γ := Γ) (j.comp o.subtype)
local notation "I" => coefficientRestrictedPurelyInfiniteIdeal (Γ := Γ) (j.comp o.subtype)

/-- A natural nonsquare in the containing field yields the exact one-witness ideal definition. -/
theorem numberFieldRestricted_purelyInfinite_iff_quadratic
    (δ : ℕ) (hn : ¬IsSquare (δ : K)) (r : L) (hr : r ^ 2 = (δ : L)) (x : A) :
    x ∈ I ↔ ∃ y : A, x ^ 2 = (δ : A) * y ^ 2 := by
  have hdK : (δ : K) ≠ 0 := by
    intro hz
    exact hn ⟨0, by simp [hz]⟩
  have hdL : (δ : L) ≠ 0 := by
    rw [← map_natCast j δ]
    exact (map_ne_zero_iff j j.injective).mpr hdK
  have hr0 : r ≠ 0 := by
    intro hz
    exact hdL (by simpa [hz] using hr.symm)
  exact QuadraticIdeal.kernel_iff_quadratic
    (nonpositiveConstantCoeffAlgHom (Γ := Γ) (K := L)) (j.comp o.subtype)
    (j.injective.comp Subtype.val_injective) (δ : o) r (by simpa using hr) hr0
    (QuadraticIdeal.zero_of_nonsquare_embedding o.subtype Subtype.val_injective (δ : o)
      (by simpa using hn))
    (δ : A) (by
      change (δ : nonpositiveSupportSubring Γ L) =
        algebraMap L _ ((j.comp o.subtype) (δ : o))
      simp only [map_natCast]) x

/-- The detector root hypothesis itself supplies one of the required radicands. -/
theorem numberFieldRestricted_exists_quadratic_ideal [NumberField K]
    (r : L) (hr : TailoredIntersectivePolynomial.value
      (NumberFieldTailoredGuard.pair K).p (NumberFieldTailoredGuard.pair K).q r = 0) :
    ∃ δ : ℕ, ¬IsSquare (δ : K) ∧
      ∀ x : A, x ∈ I ↔ ∃ y : A, x ^ 2 = (δ : A) * y ^ 2 := by
  obtain ⟨δ, _, hn, hd⟩ := NumberFieldTailoredGuard.exists_nonsquare_radicand_of_root K r hr
  exact ⟨δ, hn, numberFieldRestricted_purelyInfinite_iff_quadratic o j δ hn r hd⟩

end
end Surreal.HahnSeries
