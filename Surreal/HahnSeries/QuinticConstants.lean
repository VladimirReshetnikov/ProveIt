import Surreal.Algebra.QuinticConstants
import Surreal.HahnSeries.DiophantineConstants
import Mathlib.RingTheory.HahnSeries.Lex

/-!
# The quintic definition in ordered-coefficient Hahn rings

The general ordered-field assertion of `odg:def:eq:quintic`. In fact the
formula works in every integer-constant intermediate ring, and no square
root in the coefficient field is necessary. Its order argument uses
Mathlib's lexicographic Hahn order.
-/

namespace Surreal.HahnSeries

open QuinticConstants _root_.HahnSeries

noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The ordinary ring inclusion into the ordered lexicographic Hahn ring. -/
def intermediateLexInclusion (A : Subring (nonpositiveSupportSubring Γ K)) :
    A →+* Lex (K⟦Γ⟧) where
  toFun x := toLex x.val.val
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem intermediateLexInclusion_injective (A : Subring (nonpositiveSupportSubring Γ K)) :
    Function.Injective (intermediateLexInclusion A) := by
  intro x y h
  exact Subtype.ext (Subtype.ext (toLex.injective h))

/-- The seven-witness quintic defines precisely the integer constants in every intermediate ring. -/
theorem integer_intermediate_quintic_iff (A : Subring (nonpositiveSupportSubring Γ K))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ (Int.castRingHom K).range) (x : A) :
    Defines x ↔ ∃ a : ℤ, x.val = nonpositiveConstants (a : K) := by
  have hiff := defines_iff_mem_range (intermediateLexInclusion A)
    (intermediateLexInclusion_injective A) (intermediateConstants (Int.castRingHom K) A hA)
    (fun u v hp => ?_) (intermediate_divisor_mem_constants (Int.castRingHom K) A hA)
    integer_defines x
  · rw [hiff]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, (congrArg Subtype.val ha).symm⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, Subtype.ext ha.symm⟩
  · obtain ⟨_, b, _, _, hb⟩ :=
      intermediate_pell_two_rigidity A (Int.castRingHom K).range hA u v hp
    obtain ⟨a, ha⟩ := b.property
    refine ⟨a, Subtype.ext ?_⟩
    change nonpositiveConstants (a : K) = v.val
    change (a : K) = (b : K) at ha
    rw [ha]
    exact hb.symm

end
end Surreal.HahnSeries
