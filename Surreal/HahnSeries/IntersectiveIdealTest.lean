import Surreal.Algebra.IntersectiveIdealTest
import Surreal.HahnSeries.IntersectiveDetector

/-!
# Lambda tests all ideals in the full Hahn coefficient pullbacks

The full Hahn-ring scope of `odg:def:thm:idealtest`,
`odg:def:eq:idealtest`, and `odg:def:cor:universal`, for arbitrary
ordered abelian exponent groups and both ordinary coefficient rings.
-/

namespace Surreal.HahnSeries

open IntersectivePolynomial

noncomputable section

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- The purely infinite ideal restricted to the full coefficient pullback. -/
def coefficientRestrictedPurelyInfiniteIdeal {K O : Type*} [Field K] [CommRing O]
    (i : O →+* K) : Ideal (coefficientRestrictedSubring (Γ := Γ) i) :=
  purelyInfiniteIdeal.comap (coefficientRestrictedSubring (Γ := Γ) i).subtype

section Real

local notation "A" => coefficientRestrictedSubring (Γ := Γ) (Int.castRingHom ℝ)
local notation "I" => coefficientRestrictedPurelyInfiniteIdeal (Γ := Γ) (Int.castRingHom ℝ)

/-- A real Hahn pullback ideal contains a Lambda value exactly when it escapes the kernel. -/
theorem realRestricted_ideal_contains_value_iff (J : Ideal A) :
    (∃ t : A, value t ∈ J) ↔ ¬J ≤ I :=
  exists_value_mem_iff I realRestricted_detector_iff J

/-- Root-free real Hahn quotients are exactly the ideals below the purely infinite ideal. -/
theorem realRestricted_quotient_no_root_iff (J : Ideal A) :
    (∀ t : A ⧸ J, value t ≠ 0) ↔ J ≤ I :=
  quotient_no_root_iff I realRestricted_detector_iff J

/-- The purely infinite ideal is greatest among ideals with a root-free real Hahn quotient. -/
theorem realRestricted_greatest_root_free_ideal :
    IsGreatest {J : Ideal A | ∀ t : A ⧸ J, value t ≠ 0} I :=
  greatest_root_free_ideal I realRestricted_detector_iff

/-- The universal formula defines purely infinite real Hahn elements. -/
theorem realRestricted_purelyInfinite_iff_universal (a : A) :
    a ∈ I ↔ ∀ s t : A, a * s ≠ value t :=
  mem_iff_universal I realRestricted_detector_iff a

/-- The formula on a difference detects equality of the real constant coefficients. -/
theorem realRestricted_constant_eq_iff_universal (a b : A) :
    nonpositiveConstantCoeff a.val = nonpositiveConstantCoeff b.val ↔
      ∀ s t : A, (a - b) * s ≠ value t :=
  constant_eq_iff_universal (nonpositiveConstantCoeff.comp (A).subtype)
    realRestricted_detector_iff a b

end Real
section Complex

local notation "A" => coefficientRestrictedSubring (Γ := Γ) GaussianInt.toComplex
local notation "I" => coefficientRestrictedPurelyInfiniteIdeal (Γ := Γ) GaussianInt.toComplex

/-- The same ideal test holds in the full Gaussian coefficient Hahn pullback. -/
theorem complexRestricted_ideal_contains_value_iff (J : Ideal A) :
    (∃ t : A, value t ∈ J) ↔ ¬J ≤ I :=
  exists_value_mem_iff I complexRestricted_detector_iff J

/-- The Gaussian root-free quotients are exactly those below the purely infinite ideal. -/
theorem complexRestricted_quotient_no_root_iff (J : Ideal A) :
    (∀ t : A ⧸ J, value t ≠ 0) ↔ J ≤ I :=
  quotient_no_root_iff I complexRestricted_detector_iff J

/-- The Gaussian purely infinite ideal is greatest among ideals with a root-free quotient. -/
theorem complexRestricted_greatest_root_free_ideal :
    IsGreatest {J : Ideal A | ∀ t : A ⧸ J, value t ≠ 0} I :=
  greatest_root_free_ideal I complexRestricted_detector_iff

/-- The universal formula defines purely infinite Gaussian Hahn elements. -/
theorem complexRestricted_purelyInfinite_iff_universal (a : A) :
    a ∈ I ↔ ∀ s t : A, a * s ≠ value t :=
  mem_iff_universal I complexRestricted_detector_iff a

/-- The same formula detects equality of complex constant coefficients in the Gaussian pullback. -/
theorem complexRestricted_constant_eq_iff_universal (a b : A) :
    nonpositiveConstantCoeff a.val = nonpositiveConstantCoeff b.val ↔
      ∀ s t : A, (a - b) * s ≠ value t :=
  constant_eq_iff_universal (nonpositiveConstantCoeff.comp (A).subtype)
    complexRestricted_detector_iff a b

end Complex
end
end Surreal.HahnSeries
