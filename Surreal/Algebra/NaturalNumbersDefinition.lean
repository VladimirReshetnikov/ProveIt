import Surreal.Algebra.QuinticConstants

/-!
# Four squares select the natural numbers among integer constants

The generic ordered-ring argument of `odg:def:cor:naturals`. Any predicate
defining the ordinary integers gives a definition of the ordinary natural
numbers by adjoining four-square witnesses, including the value zero.
-/

namespace Surreal.NaturalNumbersDefinition

noncomputable section

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- No extra standardness predicates on the four witnesses are needed. -/
theorem natural_iff_standard_four_squares (Std : R → Prop)
    (hStd : ∀ x, Std x ↔ ∃ a : ℤ, x = (a : R)) (x : R) :
    (∃ n : ℕ, x = (n : R)) ↔ Std x ∧ ∃ s : Fin 4 → R, x = ∑ j, s j ^ 2 := by
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨(hStd _).mpr ⟨n, by simp⟩, ?_⟩
    obtain ⟨s, hs⟩ := QuinticConstants.integer_four_squares (n : ℤ) (Int.natCast_nonneg _)
    refine ⟨fun j => (s j : R), ?_⟩
    have h := congrArg (Int.castRingHom R) hs
    simp only [map_sum, map_pow] at h
    change (∑ j, (s j : R) ^ 2) = ((n : ℤ) : R) at h
    simpa only [Int.cast_natCast] using h.symm
  · rintro ⟨hx, s, hs⟩
    obtain ⟨a, rfl⟩ := (hStd x).mp hx
    have ha : 0 ≤ a := by
      have hp : (0 : R) ≤ (a : R) := hs ▸ Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      exact_mod_cast hp
    exact ⟨a.toNat, by rw [← Int.cast_natCast, Int.toNat_of_nonneg ha]⟩

end
end Surreal.NaturalNumbersDefinition
