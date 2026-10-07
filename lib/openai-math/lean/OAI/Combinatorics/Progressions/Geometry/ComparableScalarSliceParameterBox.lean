import OAI.Combinatorics.Progressions.Lattices.DenseResidueScalarRectangleGeometry

namespace OAI

section

namespace Erdos3.ResidueBoxSlice

variable {J : Type*} {P : J → ℕ} {q : ℕ}

theorem comparableScalarSliceParameterBox_bounds (S : ResidueBoxSlice P q) (hq : 0 < q)
    {L density ratio : ℝ} (hL : 1 ≤ L) (hdensity : 0 < density)
    (hratio : 1 ≤ ratio) (hlong : 4 ≤ density * L)
    (hP : ∀ j, (P j : ℝ) ≤ ratio * L)
    (hlen : ∀ j, density * L / 2 ≤ (S.length j : ℝ)) :
    (∀ j, (0 : ℤ) < (S.length j : ℤ)) ∧
    0 < density * L / 2 ∧
    (∀ j, density * L / 2 ≤ (((S.length j : ℤ) - 0 : ℤ) : ℝ)) ∧
    (∀ j, (S.length j : ℤ) - 0 ≤ (⌈ratio * L⌉₊ : ℤ)) ∧
    (⌈ratio * L⌉₊ : ℝ) ≤ (4 * ratio / density) * (density * L / 2) ∧
    (density / 2) * L ≤ density * L / 2 ∧
    (∀ j, |(((S.start j : ℤ) + (q : ℤ) * 0 : ℤ) : ℝ) / L| ≤ 2 * ratio) ∧
    (∀ j, |(((S.start j : ℤ) + (q : ℤ) * (S.length j : ℤ) : ℤ) : ℝ) / L| ≤
      2 * ratio) := by
  obtain ⟨hlen2, hwidth, hwidthRatio, hleft, hright⟩ :=
    S.scalarRectangle_geometry hq hL hdensity hratio hlong hP hlen
  refine ⟨?_, by positivity, ?_, ?_, hwidthRatio, ?_, ?_, ?_⟩
  · intro j
    exact_mod_cast (show 0 < S.length j by have := hlen2 j; omega)
  · intro j
    simpa only [sub_zero, Int.cast_natCast] using hlen j
  · intro j
    simpa only [sub_zero] using (show (S.length j : ℤ) ≤ (⌈ratio * L⌉₊ : ℤ) by
      exact_mod_cast hwidth j)
  · apply le_of_eq
    ring
  · intro j
    simpa only [mul_zero, add_zero, Int.cast_natCast] using hleft j
  · intro j
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using hright j

end Erdos3.ResidueBoxSlice

end

end OAI
