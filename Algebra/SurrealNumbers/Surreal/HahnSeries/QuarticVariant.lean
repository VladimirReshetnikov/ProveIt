import Surreal.Algebra.QuarticVariant
import Surreal.HahnSeries.QuinticConstants
import Surreal.HahnSeries.NonpositiveSupportBounds

/-!
# The squared-bound quartic in intermediate Hahn rings

The full intermediate-ring assertion in `odg:def:rem:quarticvariant`.
Only the intersection with the coefficient field is prescribed. Neither
constant-term closure nor a nontrivial exponent group is required.
-/

namespace Surreal.HahnSeries

noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem integer_range_iff (A : Subring (nonpositiveSupportSubring Γ K))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ (Int.castRingHom K).range) (x : A) :
    x ∈ (intermediateConstants (Int.castRingHom K) A hA).range ↔
      ∃ a : ℤ, x.val = nonpositiveConstants (a : K) := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, (congrArg Subtype.val ha).symm⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha.symm⟩

/-- The square-bound criterion descends to integer constants in an intermediate ring. -/
theorem integer_intermediate_square_bound (A : Subring (nonpositiveSupportSubring Γ K))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ (Int.castRingHom K).range)
    (x : A) (b : ℤ)
    (h : intermediateLexInclusion A x ^ 2 ≤
      intermediateLexInclusion A (intermediateConstants (Int.castRingHom K) A hA b) ^ 2) :
    x ∈ (intermediateConstants (Int.castRingHom K) A hA).range := by
  have hx := nonpositiveSupport_eq_constant_of_sq_le x.val (b : K) h
  have hm := (hA _).mp (hx ▸ x.property)
  obtain ⟨a, ha⟩ := hm
  apply (integer_range_iff A hA x).mpr
  exact ⟨a, by rw [show (a : K) = nonpositiveConstantCoeff x.val from ha]; exact hx⟩

private theorem pell_mem_range (A : Subring (nonpositiveSupportSubring Γ K))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ (Int.castRingHom K).range)
    (u v : A) (hp : u ^ 2 - 2 * v ^ 2 = 1) :
    u ∈ (intermediateConstants (Int.castRingHom K) A hA).range ∧
      v ∈ (intermediateConstants (Int.castRingHom K) A hA).range := by
  obtain ⟨a, b, _, hu, hv⟩ :=
    intermediate_pell_two_rigidity A (Int.castRingHom K).range hA u v hp
  obtain ⟨a', ha⟩ := a.property
  obtain ⟨b', hb⟩ := b.property
  constructor
  · apply (integer_range_iff A hA u).mpr
    exact ⟨a', by rw [show (a' : K) = a.val from ha]; exact hu⟩
  · apply (integer_range_iff A hA v).mpr
    exact ⟨b', by rw [show (b' : K) = b.val from hb]; exact hv⟩

/-- Every one of the seven coordinates of a quartic zero is an integer constant. -/
theorem integer_intermediate_quarticVariant_witnesses
    (A : Subring (nonpositiveSupportSubring Γ K))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ (Int.castRingHom K).range)
    (x u v : A) (a : Fin 4 → A) (h : QuarticVariant.value x u v a = 0) :
    (∃ b : ℤ, x.val = nonpositiveConstants (b : K)) ∧
      (∃ b : ℤ, u.val = nonpositiveConstants (b : K)) ∧
      (∃ b : ℤ, v.val = nonpositiveConstants (b : K)) ∧
      (∀ j, ∃ b : ℤ, (a j).val = nonpositiveConstants (b : K)) := by
  have hw := QuarticVariant.witnesses_mem_range (intermediateLexInclusion A)
    (intermediateLexInclusion_injective A) (intermediateConstants (Int.castRingHom K) A hA)
    (pell_mem_range A hA) (integer_intermediate_square_bound A hA) x u v a h
  exact ⟨(integer_range_iff A hA x).mp hw.1, (integer_range_iff A hA u).mp hw.2.1,
    (integer_range_iff A hA v).mp hw.2.2.1, fun j =>
      (integer_range_iff A hA (a j)).mp (hw.2.2.2 j)⟩

/-- The alternative quartic defines Z in every integer-constant intermediate ordered Hahn ring. -/
theorem integer_intermediate_quarticVariant_iff
    (A : Subring (nonpositiveSupportSubring Γ K))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ (Int.castRingHom K).range) (x : A) :
    QuarticVariant.Defines x ↔ ∃ b : ℤ, x.val = nonpositiveConstants (b : K) := by
  rw [QuarticVariant.defines_iff_mem_range (intermediateLexInclusion A)
    (intermediateLexInclusion_injective A) (intermediateConstants (Int.castRingHom K) A hA)
    (pell_mem_range A hA) (integer_intermediate_square_bound A hA)]
  exact integer_range_iff A hA x

end
end Surreal.HahnSeries
