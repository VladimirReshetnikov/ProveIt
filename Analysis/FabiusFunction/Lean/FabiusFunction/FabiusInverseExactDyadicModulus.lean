import FabiusFunction.FabiusInverseLogarithmicModulus

/-!
# Exact dyadic reciprocal moduli for the inverse Fabius function

The exact rational value `fabiusAtInverseTwoPow r` is the sharp input radius
for the inverse-output target `2⁻ʳ`.  Taking the natural ceiling of its
reciprocal therefore gives the least positive integer denominator whose
reciprocal is at most that radius.

This module proves both sides of the resulting sharp statement.  The ceiling
denominator supplies the strict inverse modulus, while the endpoint pair
`0, F(2⁻ʳ)` defeats every smaller positive denominator.  Composing with the
least logarithmic dyadic order gives a smaller witness for output tolerance
`1 / n` at positive `n`, with the harmless convention `d(0) = 1`.

The minimality theorem is deliberately restricted to the fixed dyadic target
`2⁻ʳ`.  The logarithmic corollary only gives the weaker target `1 / n` and
does not claim that its denominator is least for that weaker target.
-/

set_option autoImplicit false

open Set

namespace Fabius

private theorem fabiusAtInverseTwoPow_pos_exact (r : ℕ) :
    0 < fabiusAtInverseTwoPow r := by
  rw [fabiusAtInverseTwoPow_eq_recurrenceSequence]
  exact mul_pos (inv_pos.mpr (by positivity))
    (fabiusRecurrenceSequence_pos r)

private theorem inverseTwoPow_mem_Icc_exact (r : ℕ) :
    ((2 : ℝ) ^ r)⁻¹ ∈ Icc (0 : ℝ) 1 := by
  refine ⟨by positivity, ?_⟩
  exact (inv_le_one₀ (by positivity)).2 (one_le_pow₀ (by norm_num))

/-! ## The least denominator at a fixed dyadic target -/

/-- The least positive natural denominator whose reciprocal is at most the
exact endpoint mass `F(2⁻ʳ)`.

The definition uses the exact rational evaluator, so no ceiling of an
approximated real number is involved. -/
def inverseFabiusExactDyadicDenominator (r : ℕ) : ℕ :=
  ⌈(fabiusAtInverseTwoPow r)⁻¹⌉₊

/-- The exact dyadic denominator is strictly positive at every order,
including order zero. -/
theorem inverseFabiusExactDyadicDenominator_pos (r : ℕ) :
    0 < inverseFabiusExactDyadicDenominator r := by
  rw [inverseFabiusExactDyadicDenominator, Nat.ceil_pos]
  exact inv_pos.mpr (fabiusAtInverseTwoPow_pos_exact r)

/-- The reciprocal of the exact dyadic denominator lies below the exact
rational endpoint mass. -/
theorem inv_inverseFabiusExactDyadicDenominator_le_fabiusAtInverseTwoPow
    (r : ℕ) :
    ((inverseFabiusExactDyadicDenominator r : ℚ))⁻¹ ≤
      fabiusAtInverseTwoPow r := by
  have hmass : 0 < fabiusAtInverseTwoPow r :=
    fabiusAtInverseTwoPow_pos_exact r
  have hden : (0 : ℚ) < inverseFabiusExactDyadicDenominator r := by
    exact_mod_cast inverseFabiusExactDyadicDenominator_pos r
  apply (inv_le_comm₀ hmass hden).1
  exact Nat.le_ceil _

/-- The ceiling denominator is the least positive natural denominator whose
reciprocal is bounded by the exact rational endpoint mass. -/
theorem inverseFabiusExactDyadicDenominator_isLeast (r : ℕ) :
    IsLeast
      {d : ℕ | 0 < d ∧ ((d : ℚ))⁻¹ ≤ fabiusAtInverseTwoPow r}
      (inverseFabiusExactDyadicDenominator r) := by
  constructor
  · exact ⟨inverseFabiusExactDyadicDenominator_pos r,
      inv_inverseFabiusExactDyadicDenominator_le_fabiusAtInverseTwoPow r⟩
  · intro d hd
    rw [inverseFabiusExactDyadicDenominator, Nat.ceil_le]
    have hdq : (0 : ℚ) < d := by exact_mod_cast hd.1
    exact (inv_le_comm₀ hdq (fabiusAtInverseTwoPow_pos_exact r)).1 hd.2

/-! ## Sharp strict inverse moduli -/

/-- The exact ceiling denominator gives the strict inverse modulus for the
fixed dyadic output target `2⁻ʳ`. -/
theorem abs_fabiusInv_sub_lt_inverse_two_pow_of_lt_exactDyadicDenominator
    (F : BoundedFabius) (hF : IsFabius F) (r : ℕ) {u v : ℝ}
    (huv : |u - v| <
      ((inverseFabiusExactDyadicDenominator r : ℝ))⁻¹) :
    |fabiusInv F hF u - fabiusInv F hF v| < ((2 : ℝ) ^ r)⁻¹ := by
  have hthresholdQ :=
    inv_inverseFabiusExactDyadicDenominator_le_fabiusAtInverseTwoPow r
  have hthresholdR := Rat.cast_mono (K := ℝ) hthresholdQ
  push_cast at hthresholdR
  rw [fabiusAtInverseTwoPow_cast F hF r] at hthresholdR
  exact abs_fabiusInv_sub_lt_of_abs_sub_lt_fabiusReal F hF
    (inverseTwoPow_mem_Icc_exact r) (huv.trans_le hthresholdR)

/-- Every smaller positive denominator fails at the endpoint pair
`0, F(2⁻ʳ)`: its input gap is below the proposed reciprocal radius, while its
inverse-output gap is exactly `2⁻ʳ`. -/
theorem exists_fabiusInv_gap_of_lt_exactDyadicDenominator
    (F : BoundedFabius) (hF : IsFabius F) (r d : ℕ)
    (hdpos : 0 < d) (hd : d < inverseFabiusExactDyadicDenominator r) :
    ∃ u v : ℝ,
      |u - v| < ((d : ℝ))⁻¹ ∧
      |fabiusInv F hF u - fabiusInv F hF v| = ((2 : ℝ) ^ r)⁻¹ := by
  have hmass : 0 < fabiusAtInverseTwoPow r :=
    fabiusAtInverseTwoPow_pos_exact r
  have hdq : (0 : ℚ) < d := by exact_mod_cast hdpos
  have hdlt : (d : ℚ) < (fabiusAtInverseTwoPow r)⁻¹ := by
    exact (Nat.lt_ceil.mp (by
      simpa only [inverseFabiusExactDyadicDenominator] using hd))
  have hmassltQ : fabiusAtInverseTwoPow r < ((d : ℚ))⁻¹ :=
    (lt_inv_comm₀ hmass hdq).2 hdlt
  have hmassltR := (Rat.cast_lt (K := ℝ)).2 hmassltQ
  push_cast at hmassltR
  rw [fabiusAtInverseTwoPow_cast F hF r] at hmassltR
  refine ⟨0, fabiusReal F (((2 : ℝ) ^ r)⁻¹), ?_, ?_⟩
  · simpa [abs_of_nonneg (fabiusReal_nonneg F (((2 : ℝ) ^ r)⁻¹))] using
      hmassltR
  · rw [fabiusInv_zero F hF,
      fabiusInv_fabiusReal F hF (inverseTwoPow_mem_Icc_exact r),
      zero_sub, abs_neg, abs_of_nonneg (inverseTwoPow_mem_Icc_exact r).1]

/-- The exact ceiling denominator is the least positive integer strict
modulus for the fixed dyadic output target.  This is a target-specific
optimality statement, not optimality for a larger output tolerance. -/
theorem inverseFabiusExactDyadicDenominator_isLeast_strictModulus
    (F : BoundedFabius) (hF : IsFabius F) (r : ℕ) :
    IsLeast
      {d : ℕ | 0 < d ∧
        ∀ u v : ℝ, |u - v| < ((d : ℝ))⁻¹ →
          |fabiusInv F hF u - fabiusInv F hF v| < ((2 : ℝ) ^ r)⁻¹}
      (inverseFabiusExactDyadicDenominator r) := by
  constructor
  · exact ⟨inverseFabiusExactDyadicDenominator_pos r,
      fun _u _v huv =>
        abs_fabiusInv_sub_lt_inverse_two_pow_of_lt_exactDyadicDenominator
          F hF r huv⟩
  · intro d hd
    by_contra hnot
    have hlt : d < inverseFabiusExactDyadicDenominator r :=
      Nat.lt_of_not_ge hnot
    rcases exists_fabiusInv_gap_of_lt_exactDyadicDenominator
      F hF r d hd.1 hlt with ⟨u, v, huv, hgap⟩
    have hstrict := hd.2 u v huv
    rw [hgap] at hstrict
    exact (lt_irrefl _) hstrict

/-! ## A logarithmic witness for reciprocal output tolerances -/

/-- The exact dyadic denominator evaluated at the least order whose dyadic
scale is strictly below `1 / n`.  Its value at zero is defined to be `1`;
no modulus conclusion is asserted at that convention-only input. -/
def inverseFabiusExactLogarithmicDenominator : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      inverseFabiusExactDyadicDenominator
        (inverseFabiusLogarithmicOrder (n + 1))

/-- At positive inputs the logarithmic denominator is exactly the fixed-target
ceiling denominator at the least logarithmic dyadic order. -/
theorem inverseFabiusExactLogarithmicDenominator_of_pos
    (n : ℕ) (hn : 0 < n) :
    inverseFabiusExactLogarithmicDenominator n =
      inverseFabiusExactDyadicDenominator
        (inverseFabiusLogarithmicOrder n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rfl

/-- At every positive `n`, the exact logarithmic denominator gives output
error below `1 / n`.  Its leastness is only for the stronger fixed dyadic
target `2⁻ʳ⁽ⁿ⁾`; no least-denominator claim is made here for `1 / n`. -/
theorem abs_fabiusInv_sub_lt_inv_nat_of_lt_exactLogarithmicDenominator
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (hn : 0 < n)
    {u v : ℝ}
    (huv : |u - v| <
      ((inverseFabiusExactLogarithmicDenominator n : ℝ))⁻¹) :
    |fabiusInv F hF u - fabiusInv F hF v| < (n : ℝ)⁻¹ := by
  have huv' : |u - v| <
      ((inverseFabiusExactDyadicDenominator
        (inverseFabiusLogarithmicOrder n) : ℝ))⁻¹ := by
    rw [← inverseFabiusExactLogarithmicDenominator_of_pos n hn]
    exact huv
  have hdyadic :=
    abs_fabiusInv_sub_lt_inverse_two_pow_of_lt_exactDyadicDenominator
      F hF (inverseFabiusLogarithmicOrder n) huv'
  have hpowNat := (inverseFabiusLogarithmicOrder_isLeast n hn).1
  have hpowReal : (n : ℝ) <
      (2 : ℝ) ^ inverseFabiusLogarithmicOrder n := by
    exact_mod_cast hpowNat
  have hinv :
      ((2 : ℝ) ^ inverseFabiusLogarithmicOrder n)⁻¹ < (n : ℝ)⁻¹ :=
    (inv_lt_inv₀ (by positivity) (by exact_mod_cast hn)).2 hpowReal
  exact hdyadic.trans hinv

end Fabius
