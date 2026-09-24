import Surreal.Algebra.PellTwoGrowth
import Surreal.Algebra.QuinticConstants

/-!
# The six-witness quartic definition of ordinary integers

The algebraic part of `odg:thm:standarddef`, `odg:eq:standardsystem`, and
`odg:eq:standardquartic`. Pell growth and Mathlib's four-square theorem
construct ordinary witnesses, also for vectors of arbitrary finite length.
-/

namespace Surreal.QuarticConstants

noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The literal scalar quartic with a Pell pair and four square witnesses. -/
def value (t x y : R) (z : Fin 4 → R) : R :=
  (x ^ 2 - 2 * y ^ 2 - 1) ^ 2 + (x - t ^ 2 - ∑ j, z j ^ 2) ^ 2

/-- The six-variable existential formula defining ordinary integers. -/
def Defines (t : R) : Prop := ∃ x y : R, ∃ z : Fin 4 → R, value t x y z = 0

/-- The same six witnesses suffice for a vector of any finite length. -/
def vectorValue {n : ℕ} (t : Fin n → R) (x y : R) (z : Fin 4 → R) : R :=
  (x ^ 2 - 2 * y ^ 2 - 1) ^ 2 + (x - ∑ i, t i ^ 2 - ∑ j, z j ^ 2) ^ 2

theorem map_value (φ : R →+* S) (t x y : R) (z : Fin 4 → R) :
    φ (value t x y z) = value (φ t) (φ x) (φ y) (φ ∘ z) := by
  simp [value, map_sum, map_ofNat]

theorem map_vectorValue (φ : R →+* S) {n : ℕ} (t : Fin n → R)
    (x y : R) (z : Fin 4 → R) :
    φ (vectorValue t x y z) = vectorValue (φ ∘ t) (φ x) (φ y) (φ ∘ z) := by
  simp [vectorValue, map_sum, map_ofNat]

theorem Defines.map (φ : R →+* S) {t : R} (h : Defines t) : Defines (φ t) := by
  obtain ⟨x, y, z, he⟩ := h
  refine ⟨φ x, φ y, φ ∘ z, ?_⟩
  rw [← map_value, he, map_zero]

/-- Ordinary witnesses for the two-equation vector system. -/
theorem integer_vector_system {n : ℕ} (t : Fin n → ℤ) :
    ∃ x y : ℤ, ∃ z : Fin 4 → ℤ,
      x ^ 2 - 2 * y ^ 2 = 1 ∧ x - ∑ i, t i ^ 2 = ∑ j, z j ^ 2 := by
  obtain ⟨k, hk⟩ := PellTwo.exists_X_gt (∑ i, t i ^ 2)
  obtain ⟨z, hz⟩ := QuinticConstants.integer_four_squares
    (PellTwo.X k - ∑ i, t i ^ 2) (by omega)
  exact ⟨PellTwo.X k, PellTwo.Y k, z, PellTwo.equation k, hz.symm⟩

/-- Every ordinary vector has six ordinary witnesses to the quartic. -/
theorem integer_vector_defines {n : ℕ} (t : Fin n → ℤ) :
    ∃ x y : ℤ, ∃ z : Fin 4 → ℤ, vectorValue t x y z = 0 := by
  obtain ⟨x, y, z, hp, hs⟩ := integer_vector_system t
  exact ⟨x, y, z, by simp [vectorValue, hp, hs]⟩

/-- Every ordinary integer satisfies the literal scalar quartic. -/
theorem integer_defines (t : ℤ) : Defines t := by
  obtain ⟨x, y, z, he⟩ := integer_vector_defines (fun _ : Fin 1 => t)
  exact ⟨x, y, z, by simpa [vectorValue, value] using he⟩

section Ordered

variable [LinearOrder S] [IsStrictOrderedRing S]

/-- A faithful ordered-ring inclusion separates the two squared equations. -/
theorem value_eq_zero_iff (φ : R →+* S) (hφ : Function.Injective φ)
    (t x y : R) (z : Fin 4 → R) :
    value t x y z = 0 ↔ x ^ 2 - 2 * y ^ 2 = 1 ∧ x - t ^ 2 = ∑ j, z j ^ 2 := by
  constructor
  · intro he
    have h := QuinticConstants.three_squares_zero φ hφ
      (x ^ 2 - 2 * y ^ 2 - 1) (x - t ^ 2 - ∑ j, z j ^ 2) 0 (by
        simpa only [value, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] using he)
    exact ⟨sub_eq_zero.mp h.1, sub_eq_zero.mp h.2.1⟩
  · rintro ⟨hp, hs⟩
    simp [value, hp, hs]

/-- The same separation for the vector formula. -/
theorem vectorValue_eq_zero_iff (φ : R →+* S) (hφ : Function.Injective φ)
    {n : ℕ} (t : Fin n → R) (x y : R) (z : Fin 4 → R) :
    vectorValue t x y z = 0 ↔
      x ^ 2 - 2 * y ^ 2 = 1 ∧ x - ∑ i, t i ^ 2 = ∑ j, z j ^ 2 := by
  constructor
  · intro he
    have h := QuinticConstants.three_squares_zero φ hφ
      (x ^ 2 - 2 * y ^ 2 - 1) (x - ∑ i, t i ^ 2 - ∑ j, z j ^ 2) 0 (by
        simpa only [vectorValue, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] using he)
    exact ⟨sub_eq_zero.mp h.1, sub_eq_zero.mp h.2.1⟩
  · rintro ⟨hp, hs⟩
    simp [vectorValue, hp, hs]

end Ordered
end
end Surreal.QuarticConstants
