import Surreal.Algebra.DiophantineConstants
import Surreal.HahnSeries.PellRigidity
import Surreal.HahnSeries.IntersectivePolynomial

/-!
# The three-equation definition in intermediate Hahn rings

The general Hahn-ring assertion of `odg:def:thm:constants`. Only the exact
intersection with the coefficient field is assumed; there need not be a
constant-term retraction onto the prescribed ordinary constant ring.
-/

namespace Surreal.HahnSeries

open DiophantineConstants

noncomputable section

variable {Γ K O : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field K] [CharZero K] [CommRing O]

/-- The ordinary constant embedding into an intermediate support ring. -/
def intermediateConstants (φ : O →+* K) (A : Subring (nonpositiveSupportSubring Γ K))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ φ.range) : O →+* A :=
  (nonpositiveConstants.comp φ).codRestrict A (fun a => (hA (φ a)).mpr ⟨a, rfl⟩)

omit [CharZero K] in
/-- A divisor of a nonzero ordinary constant in an intermediate ring is itself ordinary. -/
theorem intermediate_divisor_mem_constants (φ : O →+* K)
    (A : Subring (nonpositiveSupportSubring Γ K))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ φ.range)
    (x w : A) (a : O) (ha : intermediateConstants φ A hA a ≠ 0)
    (he : x * w = intermediateConstants φ A hA a) :
    x ∈ (intermediateConstants φ A hA).range := by
  have ha0 : φ a ≠ 0 := by
    intro hz
    apply ha
    apply Subtype.ext
    change nonpositiveConstants (φ a) = 0
    rw [hz, map_zero]
  have hp : x.val * w.val = nonpositiveConstants (φ a) := congrArg Subtype.val he
  have hu : IsUnit (x.val * w.val) := hp ▸ (isUnit_iff_ne_zero.mpr ha0).map nonpositiveConstants
  have hx := nonpositiveSupport_unit_eq_constant x.val (isUnit_of_mul_isUnit_left hu)
  have hm : nonpositiveConstantCoeff x.val ∈ φ.range := (hA _).mp (hx ▸ x.property)
  obtain ⟨b, hb⟩ := hm
  refine ⟨b, Subtype.ext ?_⟩
  change nonpositiveConstants (φ b) = x.val
  rw [hb]
  exact hx.symm

/-- The abstract ordinary ring needs no more than root exclusion and ordinary witnesses;
all ambient Pell and divisor rigidity is supplied by the proved Hahn theorems. -/
theorem intermediate_xi_iff (φ : O →+* K) (hφ : Function.Injective φ)
    (hroot : ∀ a : O, IntersectivePolynomial.value a ≠ 0) (hordinary : ∀ a : O, Xi a)
    (A : Subring (nonpositiveSupportSubring Γ K))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ φ.range) (x : A) :
    Xi x ↔ ∃ a : O, x.val = nonpositiveConstants (φ a) := by
  have hiff := xi_iff_mem_range (intermediateConstants φ A hA) (fun u v hp => ?_)
    (intermediate_intersectivePolynomial_ne_zero φ hφ hroot A hA)
    (intermediate_divisor_mem_constants φ A hA) hordinary x
  · rw [hiff]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, (congrArg Subtype.val ha).symm⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, Subtype.ext ha.symm⟩
  · obtain ⟨_, b, _, _, hb⟩ := intermediate_pell_two_rigidity A φ.range hA u v hp
    obtain ⟨a, ha⟩ := b.property
    refine ⟨a, Subtype.ext ?_⟩
    change nonpositiveConstants (φ a) = v.val
    rw [ha]
    exact hb.symm

/-- The same parameter-free system defines Z in every integer-constant intermediate Hahn ring. -/
theorem integer_intermediate_xi_iff (A : Subring (nonpositiveSupportSubring Γ K))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ (Int.castRingHom K).range) (x : A) :
    Xi x ↔ ∃ a : ℤ, x.val = nonpositiveConstants (a : K) :=
  intermediate_xi_iff (Int.castRingHom K) Int.cast_injective
    IntersectivePolynomial.integer_value_ne_zero integer_xi A hA x

/-- The identical system defines Gaussian constants over every field containing Z[i]. -/
theorem gaussian_intermediate_xi_iff (φ : GaussianInt →+* K) (hφ : Function.Injective φ)
    (A : Subring (nonpositiveSupportSubring Γ K))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ φ.range) (x : A) :
    Xi x ↔ ∃ a : GaussianInt, x.val = nonpositiveConstants (φ a) :=
  intermediate_xi_iff φ hφ IntersectivePolynomial.gaussian_value_ne_zero gaussian_xi A hA x

end
end Surreal.HahnSeries
