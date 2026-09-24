import Diophantine.Common.RefinedRelationCombiningArithmetic

/-!
# The arithmetic factor in the relation-combining theorem

After the radical sum is known to be an integer, its positive offset `T`
reduces the vanishing-factor equation to divisibility and positivity. This
module specializes the unsquared arithmetic factor to `B²` and `C²`. A
nonzero signed divisor has positive square, and the dividend's square is
nonnegative, so the unsquared lemmas apply without sign restrictions on
`B` or `C`. Divisibility of their squares is equivalent to `B ∣ C`.
-/

namespace Diophantine.RelationCombiningArithmetic

/-- A vanishing factor makes the weighted radical sum rational, by applying
the unsquared factor lemma to `B²` and `C²`. The odd integer `2D-1` remains
nonzero without any positivity assumption on `D`. -/
theorem sum_rational_of_factor {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
    {B C D T n : ℤ} {s : K} (hB : B ≠ 0)
    (h : (B : K) ^ 2 * n + (C : K) ^ 2 -
      (B : K) ^ 2 * (2 * D - 1) * ((C : K) ^ 2 + T + s) = 0) :
    ∃ q : ℚ, s = algebraMap ℚ K q := by
  apply RefinedRelationCombiningArithmetic.sum_rational_of_factor
    (B := B ^ 2) (C := C ^ 2) (D := D) (T := T) (n := n) (pow_ne_zero 2 hB)
  simpa only [Int.cast_pow] using h

/-- The unsquared necessity lemma yields divisibility of the squares;
integer power cancellation recovers divisibility of the original parameters. -/
theorem conditions_of_factor {B C D T : ℤ} {n : ℕ}
    (hB : B ≠ 0) (hT : 1 ≤ T)
    (h : B ^ 2 * n + C ^ 2 = B ^ 2 * (2 * D - 1) * (C ^ 2 + T)) :
    B ∣ C ∧ 0 < D := by
  obtain ⟨hdiv, hD⟩ := RefinedRelationCombiningArithmetic.conditions_of_factor
    (sq_pos_of_ne_zero hB) (sq_nonneg C) hT h
  exact ⟨(Int.pow_dvd_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp hdiv, hD⟩

/-- Divisibility passes to squares, so the unsquared sufficiency lemma
supplies the natural witness for the signed-integer parameters. -/
theorem exists_factor_of_conditions {B C D T : ℤ}
    (hB : B ≠ 0) (hT : 1 ≤ T) (hdiv : B ∣ C) (hD : 0 < D) :
    ∃ n : ℕ, B ^ 2 * n + C ^ 2 = B ^ 2 * (2 * D - 1) * (C ^ 2 + T) := by
  exact RefinedRelationCombiningArithmetic.exists_factor_of_conditions
    (sq_pos_of_ne_zero hB) (sq_nonneg C) hT (pow_dvd_pow_of_dvd hdiv 2) hD

/-- The positive radical offset does not alter the encoded divisibility
and positivity conditions. -/
theorem factor_iff {B C D T : ℤ} (hB : B ≠ 0) (hT : 1 ≤ T) :
    (∃ n : ℕ, B ^ 2 * n + C ^ 2 = B ^ 2 * (2 * D - 1) * (C ^ 2 + T)) ↔
      B ∣ C ∧ 0 < D := by
  constructor
  · rintro ⟨n, hn⟩
    exact conditions_of_factor hB hT hn
  · rintro ⟨hdiv, hD⟩
    exact exists_factor_of_conditions hB hT hdiv hD

end Diophantine.RelationCombiningArithmetic
