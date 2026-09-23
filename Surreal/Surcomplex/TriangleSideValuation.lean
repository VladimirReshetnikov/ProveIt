import Surreal.Surcomplex.TriangleLaws

/-!
# The least side valuation is attained twice

The ultrametric law for actual surcomplex displacements prevents a
triangle from having just one dominant side scale. This proves the
closing side-valuation assertion of `trigonometry:thm:trianglelaws` and
the minimum-attainment clause of `trigonometry:thm:valuationtriangle`.
The latter theorem's angle-defect and radius identities are separate.
-/

universe u

namespace Surreal.Surcomplex.Triangle

open Foundations

/-- The valuation of the third side is bounded below by the smaller of the first two valuations. -/
theorem min_side_valuation_le (T : Triangle.{u}) :
    min (SignSequence.valuation T.sideA) (SignSequence.valuation T.sideB) ≤
      SignSequence.valuation T.sideC := by
  have he : (T.B - T.C) + (T.C - T.A) = T.B - T.A := by abel
  simpa only [valuation_eq_modulus, he, modulus_sub_comm T.B T.A, sideA, sideB, sideC] using
    min_valuation_le_add (T.B - T.C) (T.C - T.A)

/-- Unequal side valuations force the third side to share the smaller valuation. -/
theorem side_valuation_eq_min_of_ne (T : Triangle.{u})
    (h : SignSequence.valuation T.sideA ≠ SignSequence.valuation T.sideB) :
    SignSequence.valuation T.sideC =
      min (SignSequence.valuation T.sideA) (SignSequence.valuation T.sideB) := by
  have he : (T.B - T.C) + (T.C - T.A) = T.B - T.A := by abel
  change valuation (T.B - T.C) ≠ valuation (T.C - T.A) at h
  simpa only [valuation_eq_modulus, he, modulus_sub_comm T.B T.A, sideA, sideB, sideC] using
    valuation_add_of_ne h

/-- At least two of the three actual side lengths attain the least side valuation. -/
theorem side_valuation_minimum (T : Triangle.{u}) :
    (SignSequence.valuation T.sideA = SignSequence.valuation T.sideB ∧
      SignSequence.valuation T.sideA ≤ SignSequence.valuation T.sideC) ∨
    (SignSequence.valuation T.sideB = SignSequence.valuation T.sideC ∧
      SignSequence.valuation T.sideB ≤ SignSequence.valuation T.sideA) ∨
    (SignSequence.valuation T.sideC = SignSequence.valuation T.sideA ∧
      SignSequence.valuation T.sideC ≤ SignSequence.valuation T.sideB) := by
  by_cases hab : SignSequence.valuation T.sideA = SignSequence.valuation T.sideB
  · exact Or.inl ⟨hab, by simpa only [← hab, min_self] using T.min_side_valuation_le⟩
  · have he := T.side_valuation_eq_min_of_ne hab
    rcases le_total (SignSequence.valuation T.sideA) (SignSequence.valuation T.sideB) with h | h
    · rw [min_eq_left h] at he
      exact Or.inr (Or.inr ⟨he, he.le.trans h⟩)
    · rw [min_eq_right h] at he
      exact Or.inr (Or.inl ⟨he.symm, h⟩)

end Surreal.Surcomplex.Triangle
