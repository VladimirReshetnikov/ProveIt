import Surreal.Algebra.QuarticConstants

/-!
# The quartic with a squared Pell-coordinate bound

The algebraic formula `odg:def:eq:F4` in `odg:def:rem:quarticvariant`.
The ordinary witnesses use Pell growth and Lagrange's four-square theorem.
Pell rigidity and constant square bounds suffice to identify every zero.
-/

namespace Surreal.QuarticVariant

noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Source 07's literal six-witness quartic. -/
def value (x u v : R) (a : Fin 4 → R) : R :=
  (u ^ 2 - 2 * v ^ 2 - 1) ^ 2 + (u ^ 2 - x ^ 2 - ∑ j, a j ^ 2) ^ 2

/-- The corresponding existential ring predicate. -/
def Defines (x : R) : Prop := ∃ u v : R, ∃ a : Fin 4 → R, value x u v a = 0

theorem map_value (φ : R →+* S) (x u v : R) (a : Fin 4 → R) :
    φ (value x u v a) = value (φ x) (φ u) (φ v) (φ ∘ a) := by
  simp [value, map_sum, map_ofNat]

theorem Defines.map (φ : R →+* S) {x : R} (h : Defines x) : Defines (φ x) := by
  obtain ⟨u, v, a, he⟩ := h
  refine ⟨φ u, φ v, φ ∘ a, ?_⟩
  rw [← map_value, he, map_zero]

/-- Every ordinary integer has six ordinary witnesses. -/
theorem integer_defines (x : ℤ) : Defines x := by
  obtain ⟨k, hk⟩ := PellTwo.exists_X_gt |x|
  have hgap : 0 ≤ PellTwo.X k ^ 2 - x ^ 2 := by
    nlinarith [sq_abs x, abs_nonneg x]
  obtain ⟨a, ha⟩ := QuinticConstants.integer_four_squares _ hgap
  exact ⟨PellTwo.X k, PellTwo.Y k, a, by simp [value, PellTwo.equation, ha]⟩

/-- In any ring containing a square root of minus one, the formula accepts every element. -/
theorem complex_collapse (x i : R) (hi : i ^ 2 = -1) :
    value x 1 0 ![i * x, 1, 0, 0] = 0 := by
  simp only [value, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one, Finset.univ_eq_empty, Finset.sum_empty,
    zero_pow (by decide : (2 : ℕ) ≠ 0), one_pow, mul_zero, sub_zero,
    sub_self, zero_add, add_zero, mul_pow, hi]
  ring

section Ordered

variable [LinearOrder S] [IsStrictOrderedRing S]

/-- A faithful ordered inclusion recovers the Pell equation and the square bound. -/
theorem value_eq_zero_iff (φ : R →+* S) (hφ : Function.Injective φ)
    (x u v : R) (a : Fin 4 → R) :
    value x u v a = 0 ↔ u ^ 2 - 2 * v ^ 2 = 1 ∧ u ^ 2 - x ^ 2 = ∑ j, a j ^ 2 := by
  constructor
  · intro he
    have h := QuinticConstants.three_squares_zero φ hφ
      (u ^ 2 - 2 * v ^ 2 - 1) (u ^ 2 - x ^ 2 - ∑ j, a j ^ 2) 0 (by
        simpa only [value, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] using he)
    exact ⟨sub_eq_zero.mp h.1, sub_eq_zero.mp h.2.1⟩
  · rintro ⟨hp, hs⟩
    simp [value, hp, hs]

/-- Pell rigidity and constant square bounds force all seven coordinates to be integers. -/
theorem witnesses_mem_range (φ : R →+* S) (hφ : Function.Injective φ) (ι : ℤ →+* R)
    (hpell : ∀ u v : R, u ^ 2 - 2 * v ^ 2 = 1 → u ∈ ι.range ∧ v ∈ ι.range)
    (hbound : ∀ z : R, ∀ b : ℤ, φ z ^ 2 ≤ φ (ι b) ^ 2 → z ∈ ι.range)
    (x u v : R) (a : Fin 4 → R) (he : value x u v a = 0) :
    x ∈ ι.range ∧ u ∈ ι.range ∧ v ∈ ι.range ∧ ∀ j, a j ∈ ι.range := by
  obtain ⟨hp, hs⟩ := (value_eq_zero_iff φ hφ x u v a).mp he
  obtain ⟨hu, hv⟩ := hpell u v hp
  obtain ⟨b, hb⟩ := hu
  have hs' := congrArg φ hs
  simp only [map_sub, map_pow, map_sum] at hs'
  have hn : 0 ≤ ∑ j, φ (a j) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  refine ⟨hbound x b ?_, ⟨b, hb⟩, hv, fun j => hbound (a j) b ?_⟩
  · rw [hb]
    linarith
  · rw [hb]
    have hj : φ (a j) ^ 2 ≤ ∑ j, φ (a j) ^ 2 :=
      Finset.single_le_sum (fun i _ => sq_nonneg (φ (a i))) (Finset.mem_univ j)
    nlinarith [sq_nonneg (φ x)]

/-- The two rigidity properties suffice for the full definition equivalence. -/
theorem defines_iff_mem_range (φ : R →+* S) (hφ : Function.Injective φ) (ι : ℤ →+* R)
    (hpell : ∀ u v : R, u ^ 2 - 2 * v ^ 2 = 1 → u ∈ ι.range ∧ v ∈ ι.range)
    (hbound : ∀ z : R, ∀ b : ℤ, φ z ^ 2 ≤ φ (ι b) ^ 2 → z ∈ ι.range)
    (x : R) : Defines x ↔ x ∈ ι.range := by
  constructor
  · rintro ⟨u, v, a, he⟩
    exact (witnesses_mem_range φ hφ ι hpell hbound x u v a he).1
  · rintro ⟨b, rfl⟩
    exact (integer_defines b).map ι

end Ordered
end
end Surreal.QuarticVariant
