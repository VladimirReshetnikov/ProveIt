import Surreal.Algebra.DiophantineConstants
import Mathlib.NumberTheory.SumFourSquares

/-!
# The real quintic definition of ordinary constants

The algebraic core of `odg:def:eq:quintic` and `odg:def:rem:quintic`.
Seven witnesses consist of a Pell pair, its divisibility quotient, and
four squares for the first Pell coordinate minus two.
-/

namespace Surreal.QuinticConstants

noncomputable section

variable {R S O : Type*} [CommRing R] [CommRing S] [CommRing O]

/-- The literal quintic polynomial evaluated at its eight arguments. -/
def value (x u v w : R) (s : Fin 4 → R) : R :=
  x * ((u ^ 2 - 2 * v ^ 2 - 1) ^ 2 + (v - x * w) ^ 2 +
    (u - 2 - ∑ j, s j ^ 2) ^ 2)

/-- The seven-witness existential predicate. -/
def Defines (x : R) : Prop := ∃ u v w : R, ∃ s : Fin 4 → R, value x u v w s = 0

theorem map_value (φ : R →+* S) (x u v w : R) (s : Fin 4 → R) :
    φ (value x u v w s) = value (φ x) (φ u) (φ v) (φ w) (φ ∘ s) := by
  simp [value, map_sum, map_ofNat]

theorem Defines.map (φ : R →+* S) {x : R} (h : Defines x) : Defines (φ x) := by
  obtain ⟨u, v, w, s, he⟩ := h
  refine ⟨φ u, φ v, φ w, φ ∘ s, ?_⟩
  rw [← map_value, he, map_zero]

theorem defines_zero : Defines (0 : R) := ⟨0, 0, 0, fun _ => 0, by simp [value]⟩

/-- Every positive-index first Pell coordinate is at least three. -/
theorem pell_X_ge_three {k : ℕ} (hk : 0 < k) : 3 ≤ PellTwo.X k := by
  have hx : 0 < PellTwo.X k :=
    Pell.Solution₁.x_pow_pos (by norm_num [PellTwo.fundamental]) k
  have hy := PellTwo.Y_pos hk
  have hp := PellTwo.equation k
  have hx1 : 1 < PellTwo.X k := by nlinarith
  exact PellTwo.fundamental_isFundamental.2.2 hx1

/-- A nonnegative integer has a four-square representation over the ordinary integers. -/
theorem integer_four_squares (n : ℤ) (hn : 0 ≤ n) :
    ∃ s : Fin 4 → ℤ, ∑ j, s j ^ 2 = n := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares n.toNat
  refine ⟨![a, b, c, d], ?_⟩
  simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  have he : (a : ℤ) ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n := by
    have he := congrArg (fun q : ℕ => (q : ℤ)) h
    simpa only [Nat.cast_add, Nat.cast_pow, Int.toNat_of_nonneg hn] using he
  linear_combination he

/-- Every ordinary integer satisfies the quintic, with all witnesses ordinary. -/
theorem integer_defines (x : ℤ) : Defines x := by
  by_cases hx : x = 0
  · subst x
    exact defines_zero
  obtain ⟨k, hk, _, hd, _⟩ :=
    PellTwo.exists_bounded_divisible_coordinate x.natAbs (Int.natAbs_pos.mpr hx)
  have hxd : x ∣ PellTwo.Y k := (Int.natAbs_dvd).mp hd
  obtain ⟨w, hw⟩ := hxd
  obtain ⟨s, hs⟩ := integer_four_squares (PellTwo.X k - 2) (by have := pell_X_ge_three hk; omega)
  refine ⟨PellTwo.X k, PellTwo.Y k, w, s, ?_⟩
  simp only [value, PellTwo.equation, hs, ← hw, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0),
    zero_add, mul_zero]

section Ordered

variable [LinearOrder S] [IsStrictOrderedRing S]

/-- An injective map into an ordered ring reflects the vanishing of each of three squares. -/
theorem three_squares_zero (φ : R →+* S) (hφ : Function.Injective φ)
    (a b c : R) (h : a ^ 2 + b ^ 2 + c ^ 2 = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have he : φ a ^ 2 + φ b ^ 2 + φ c ^ 2 = 0 := by
    rw [← map_pow, ← map_pow, ← map_pow, ← map_add, ← map_add, h, map_zero]
  have ha : φ a = 0 := by nlinarith [sq_nonneg (φ b), sq_nonneg (φ c)]
  have hb : φ b = 0 := by nlinarith [sq_nonneg (φ a), sq_nonneg (φ c)]
  have hc : φ c = 0 := by nlinarith [sq_nonneg (φ a), sq_nonneg (φ b)]
  exact ⟨(map_eq_zero_iff φ hφ).mp ha, (map_eq_zero_iff φ hφ).mp hb,
    (map_eq_zero_iff φ hφ).mp hc⟩

/-- Pell and divisor rigidity suffice for the real quintic definition. -/
theorem defines_iff_mem_range [IsDomain R] (φ : R →+* S) (hφ : Function.Injective φ)
    (ι : O →+* R)
    (hpell : ∀ u v : R, u ^ 2 - 2 * v ^ 2 = 1 → v ∈ ι.range)
    (hdivisor : ∀ x w : R, ∀ a : O, ι a ≠ 0 → x * w = ι a → x ∈ ι.range)
    (hordinary : ∀ a : O, Defines a) (x : R) : Defines x ↔ x ∈ ι.range := by
  constructor
  · rintro ⟨u, v, w, s, he⟩
    by_cases hx : x = 0
    · rw [hx]
      exact ι.range.zero_mem
    obtain ⟨hp, hw, hs⟩ := three_squares_zero φ hφ _ _ _ ((mul_eq_zero.mp he).resolve_left hx)
    have hp := sub_eq_zero.mp hp
    have hw := sub_eq_zero.mp hw
    have hu : 2 ≤ φ u := by
      have h := congrArg φ hs
      simp only [map_sub, map_ofNat, map_sum, map_pow, map_zero] at h
      have hn : 0 ≤ ∑ j, φ (s j) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      linarith
    have hv : v ≠ 0 := by
      intro hz
      have h := congrArg φ hp
      simp only [hz, map_pow, map_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, sub_zero] at h
      nlinarith
    obtain ⟨a, ha⟩ := hpell u v hp
    exact hdivisor x w a (ha ▸ hv) (hw.symm.trans ha.symm)
  · rintro ⟨a, rfl⟩
    exact (hordinary a).map ι

end Ordered
end
end Surreal.QuinticConstants
