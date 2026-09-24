import Surreal.Algebra.PositiveExistentialDefinability
import Mathlib.Algebra.CharZero.Infinite

/-!
# A split retraction with nonzero kernel has infinite and coinfinite distinguished sets

The set-theoretic prerequisite of `odg:def:prop:notqf`. Positive natural
multiples of one nonzero kernel element suffice; no choice of an infinite
family of exponents is necessary.
-/

namespace Surreal.RetractionInfiniteSets

variable {R O : Type*} [CommRing R] [IsDomain R] [CharZero R] [CommRing O] [CharZero O]

/-- Distinct positive natural multiples of a nonzero element remain distinct in a domain. -/
theorem positive_multiples_injective {w : R} (hw : w ≠ 0) :
    Function.Injective (fun n : ℕ => ((n + 1 : ℕ) : R) * w) := by
  intro m n h
  have he : ((m + 1 : ℕ) : R) = ((n + 1 : ℕ) : R) := mul_right_cancel₀ hw h
  exact Nat.add_right_cancel (Nat.cast_injective he)

omit [CharZero O] in
/-- The kernel of a ring homomorphism containing one nonzero point is infinite. -/
theorem kernel_infinite (ct : R →+* O) {w : R} (hw : w ≠ 0) (hct : ct w = 0) :
    Set.Infinite {x : R | ct x = 0} := by
  apply Set.Infinite.mono (s := Set.range (fun n : ℕ => ((n + 1 : ℕ) : R) * w))
  · rintro x ⟨n, rfl⟩
    simp [hct]
  · exact Set.infinite_range_of_injective (positive_multiples_injective hw)

omit [IsDomain R] in
/-- Nonzero ordinary natural coefficients give infinitely many points outside the kernel. -/
theorem kernel_complement_infinite (ct : R →+* O) :
    Set.Infinite {x : R | ct x ≠ 0} := by
  apply Set.Infinite.mono (s := Set.range (fun n : ℕ => ((n + 1 : ℕ) : R)))
  · rintro x ⟨n, rfl⟩
    simp only [Set.mem_setOf_eq, map_natCast]
    exact_mod_cast Nat.succ_ne_zero n
  · apply Set.infinite_range_of_injective
    intro m n h
    exact Nat.add_right_cancel (Nat.cast_injective h)

omit [IsDomain R] [CharZero R] in
/-- A section contains infinitely many ordinary coefficients. -/
theorem constants_infinite (ct : R →+* O) (i : O →+* R) (hi : ∀ a, ct (i a) = a) :
    (Set.range i).Infinite :=
  Set.infinite_range_of_injective (show Function.LeftInverse ct i from hi).injective

omit [CharZero O] in
/-- Positive multiples of a nonzero kernel point all lie outside the coefficient section. -/
theorem constants_complement_infinite (ct : R →+* O) (i : O →+* R)
    (hi : ∀ a, ct (i a) = a) {w : R} (hw : w ≠ 0) (hct : ct w = 0) :
    (Set.range i)ᶜ.Infinite := by
  apply Set.Infinite.mono (s := Set.range (fun n : ℕ => ((n + 1 : ℕ) : R) * w))
  · rintro x ⟨n, rfl⟩
    apply retraction_kernel_not_mem_range ct i hi
    · exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)) hw
    · simp [hct]
  · exact Set.infinite_range_of_injective (positive_multiples_injective hw)

end Surreal.RetractionInfiniteSets
