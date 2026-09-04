import FabiusFunction.StirlingSecondReverseColumn
import FabiusFunction.BellComposition
import FabiusFunction.ExponentialRiordan

/-!
# The reverse row recurrence of the second kind

`StirlingSecondReverseColumn` proves one of the two reverse recurrences the source states for
the second-kind numbers; this module proves the other,

`(n - k) S(n,k) = ∑_{j=2}^{n-k+1} (j-2)! C(-k, j) S(n, k+j-1)`   (`second_reverse_row`),

which moves along a row rather than down a column.

The univariate proof of `eq:second-reverse-row` in the canonical
`Combinatorial_Coefficient_Calculus` monograph replaces the original bivariate argument:
with `k` fixed and the sum taken over `n` alone, every term is a *column*
generating function `u^m/m!` in the single variable `x`, where `u = e^x - 1`.  Both sides then
carry the common factor `u^{k-1}/(k-1)!`, because

`(j-2)! C(-k,j) / (k+j-1)! = (-1)^j / (j(j-1)(k-1)!)`,

and what is left is the single series identity `∑_{j≥2} (-1)^j t^j/(j(j-1)) = (1+t)log(1+t) - t`
(`coeff_logTail`, one coefficient computation) evaluated at `t = u`, where `1 + u = e^x` and
`log(1+u) = x` (`log_subst_exp_sub_one` of `BellComposition`).

## Main results

* `coeff_logTail`, the coefficients of `(1+X)log(1+X) - X`.
* `subst_logTail`, its value at `u = e^x - 1`, namely `x·e^x - u`.
* `second_reverse_row_succ`, the division-free recurrence over any ring,
  with the positive column written as `k + 1`.
* `second_reverse_row_ring`, the same recurrence for any positive column and every row.
* `second_reverse_row_ring_Icc`, the exact finite range `2 ≤ j ≤ n-k+1` over any ring.
* `second_reverse_row`, the manuscript's rational identity with that exact finite range.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

section SecondRow

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The quadratic tail of the logarithm, `(1+X)·log(1+X) - X`.  Its coefficients are
`(-1)^j/(j(j-1))`, which is the weight the reverse row recurrence carries. -/
noncomputable def logTail : A⟦X⟧ := (1 + X) * log A - X

/-- The coefficients of `logTail`: `(-1)^j/(j(j-1))` from `j = 2` on, and `0` below.  This is
the one series identity the row recurrence needs, and it is a coefficient computation rather
than the double differentiation the source performs. -/
theorem coeff_logTail (j : ℕ) :
    coeff j (logTail A) =
      if 2 ≤ j then algebraMap ℚ A ((-1 : ℚ) ^ j / (j * (j - 1))) else 0 := by
  rcases j with _ | _ | m
  · simp [logTail]
  · rw [if_neg (by omega), logTail, map_sub, add_mul, one_mul, map_add, coeff_succ_X_mul,
      coeff_log, coeff_log, PowerSeries.coeff_X]
    norm_num
  · rw [logTail, map_sub, add_mul, one_mul, map_add, coeff_log, if_neg (by omega),
      coeff_succ_X_mul, coeff_log, if_neg (by omega), PowerSeries.coeff_X, if_neg (by omega),
      sub_zero, if_pos (by omega), ← map_add]
    congr 1
    have hpow : (-1 : ℚ) ^ (m + 1 + 1 + 1) = -((-1 : ℚ) ^ (m + 1 + 1)) := by
      rw [pow_succ]; ring
    rw [hpow]
    set c : ℚ := (-1 : ℚ) ^ (m + 1 + 1)
    have h1 : ((m : ℚ) + 1) ≠ 0 := by positivity
    have h2 : ((m : ℚ) + 1 + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-- **The tail at `u = e^x - 1` is `x·e^x - u`.**  This is the whole content of the row
recurrence: the two sides of the identity differ by exactly this substitution, and the step
that makes it work is `log(e^x) = x`. -/
theorem subst_logTail :
    (logTail A).subst (exp A - 1) = X * exp A - (exp A - 1) := by
  have hu : HasSubst (exp A - 1) := HasSubst.exp_sub_one
  rw [logTail, ← coe_substAlgHom hu, map_sub, map_mul, map_add, map_one, coe_substAlgHom hu,
    subst_X hu, log_subst_exp_sub_one]
  ring

end SecondRow

section ReverseRow

private theorem succ_mul_inv_factorial (k : ℕ) :
    ((k + 1 : ℕ) : ℚ) * (1 / (k + 1).factorial) = 1 / k.factorial := by
  rw [Nat.factorial_succ, Nat.cast_mul, ← mul_div_assoc]
  exact mul_div_mul_left 1 (k.factorial : ℚ) (by positivity)

private theorem reverse_row_series (k : ℕ) :
    X * d⁄dX ℚ (egfA ℚ fun n => (Nat.stirlingSecond n (k + 1) : ℚ)) -
        ((k + 1 : ℕ) : ℚ⟦X⟧) * egfA ℚ (fun n => (Nat.stirlingSecond n (k + 1) : ℚ)) =
      PowerSeries.C (1 / (k.factorial : ℚ)) * (exp ℚ - 1) ^ k *
        (logTail ℚ).subst (exp ℚ - 1) := by
  rw [subst_logTail]
  simp only [egfA_stirlingSecond, Algebra.algebraMap_self, RingHom.id_apply]
  rw [Derivation.leibniz, derivative_C, smul_zero, add_zero,
    Derivation.leibniz_pow, Nat.add_sub_cancel, map_sub,
    Derivation.map_one_eq_zero, sub_zero, PowerSeries.derivative_exp]
  simp only [smul_eq_mul, nsmul_eq_mul, pow_succ]
  have hc : ((k + 1 : ℕ) : ℚ⟦X⟧) * PowerSeries.C (1 / ((k + 1).factorial : ℚ)) =
      PowerSeries.C (1 / (k.factorial : ℚ)) := by
    rw [← map_natCast (PowerSeries.C : ℚ →+* ℚ⟦X⟧) (k + 1),
      ← map_mul, succ_mul_inv_factorial]
  linear_combination
    (X * (exp ℚ - 1) ^ k * exp ℚ - (exp ℚ - 1) ^ k * (exp ℚ - 1)) * hc

private theorem reverse_row_coefficient_term (n k j : ℕ) :
    (n.factorial : ℚ) * (coeff j (logTail ℚ) *
        coeff n ((PowerSeries.C (1 / (k.factorial : ℚ)) * (exp ℚ - 1) ^ k) *
          (exp ℚ - 1) ^ j)) =
      if 2 ≤ j then
        (-1 : ℚ) ^ j * (j - 2).factorial * (k + j).choose j *
          Nat.stirlingSecond n (k + j)
      else 0 := by
  rw [mul_assoc (PowerSeries.C (1 / (k.factorial : ℚ))), ← pow_add,
    coeff_C_mul, exp_sub_one_pow, coeff_egf, coeff_logTail]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  by_cases hj : 2 ≤ j
  · simp only [if_pos hj]
    obtain ⟨r, rfl⟩ : ∃ r, j = r + 2 := ⟨j - 2, by omega⟩
    have hfac : ((k + (r + 2)).choose (r + 2) : ℚ) * (k.factorial : ℚ) *
        ((r + 2).factorial : ℚ) = ((k + (r + 2)).factorial : ℚ) := by
      exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial k (r + 2)
    rw [← hfac, Nat.factorial_succ (r + 1), Nat.factorial_succ r,
      Nat.add_sub_cancel]
    have hn : (n.factorial : ℚ) ≠ 0 := by positivity
    have hk : (k.factorial : ℚ) ≠ 0 := by positivity
    have hr1 : (r : ℚ) + 1 ≠ 0 := by positivity
    have hr2 : (r : ℚ) + 2 ≠ 0 := by positivity
    push_cast
    simp only [show (r : ℚ) + 2 - 1 = (r : ℚ) + 1 by ring]
    field_simp [hn, hk, hr1, hr2] <;> ring
  · simp [hj]

private theorem second_reverse_row_rat (n k : ℕ) :
    ((n : ℚ) - ((k + 1 : ℕ) : ℚ)) * Nat.stirlingSecond n (k + 1) =
      ∑ j ∈ range (n + 1),
        if 2 ≤ j then
          (-1 : ℚ) ^ j * (j - 2).factorial * (k + j).choose j *
            Nat.stirlingSecond n (k + j)
        else 0 := by
  have h := congrArg (fun f : ℚ⟦X⟧ => (n.factorial : ℚ) * coeff n f)
    (reverse_row_series k)
  rw [X_mul_derivative_egfA, natCast_mul_egfA, egfA_sub, coeff_egfA,
    coeff_mul_subst_eq ℚ (by simp [constantCoeff_exp]), Finset.mul_sum] at h
  simp only [Algebra.algebraMap_self, RingHom.id_apply, Pi.sub_apply] at h
  have hn : (n.factorial : ℚ) ≠ 0 := by positivity
  calc
    ((n : ℚ) - ((k + 1 : ℕ) : ℚ)) * Nat.stirlingSecond n (k + 1) =
        (n.factorial : ℚ) * (1 / (n.factorial : ℚ) *
          ((n : ℚ) * Nat.stirlingSecond n (k + 1) -
            ((k + 1 : ℕ) : ℚ) * Nat.stirlingSecond n (k + 1))) := by
      rw [← mul_assoc, mul_one_div_cancel hn, one_mul, sub_mul]
    _ = _ := h
    _ = _ := Finset.sum_congr rfl fun j _ => reverse_row_coefficient_term n k j

/-- **Reverse row recurrence of the second kind, over any ring.**

This is `eq:second-reverse-row` of `thm:second-reverse-recurrences` in
`Combinatorial_Coefficient_Calculus`, with its positive column written as `k + 1`.
The generalized binomial coefficient is expanded as
`C(-(k+1),j) = (-1)^j C(k+j,j)`, so the identity contains no division.
It holds for every `n`, including `n ≤ k + 1`; out-of-range Stirling numbers
vanish. The proof first extracts rational coefficients, then transports the
resulting integer identity to an arbitrary ring. -/
theorem second_reverse_row_succ (R : Type*) [Ring R] (n k : ℕ) :
    ((n : R) - ((k + 1 : ℕ) : R)) * (Nat.stirlingSecond n (k + 1) : R) =
      ∑ j ∈ range (n + 1),
        if 2 ≤ j then
          (-1 : R) ^ j * ((j - 2).factorial : R) * ((k + j).choose j : R) *
            (Nat.stirlingSecond n (k + j) : R)
        else 0 := by
  have hz : ((n : ℤ) - ((k + 1 : ℕ) : ℤ)) * (Nat.stirlingSecond n (k + 1) : ℤ) =
      ∑ j ∈ range (n + 1),
        if 2 ≤ j then
          (-1 : ℤ) ^ j * ((j - 2).factorial : ℤ) * ((k + j).choose j : ℤ) *
            (Nat.stirlingSecond n (k + j) : ℤ)
        else 0 := by
    exact_mod_cast second_reverse_row_rat n k
  simpa only [map_sub, map_mul, map_sum, map_pow, map_neg, map_one,
    map_natCast, map_zero, apply_ite] using congrArg (Int.castRingHom R) hz

/-- **Reverse row recurrence for every positive column.**

The sum uses a uniform range `j ≤ n`; its `j < 2` terms and all terms beyond
the manuscript's endpoint vanish. No ordering hypothesis between `n` and `k`
is needed, and the coefficient ring may have positive characteristic. -/
theorem second_reverse_row_ring (R : Type*) [Ring R] (n k : ℕ) (hk : 1 ≤ k) :
    ((n : R) - (k : R)) * (Nat.stirlingSecond n k : R) =
      ∑ j ∈ range (n + 1),
        if 2 ≤ j then
          (-1 : R) ^ j * ((j - 2).factorial : R) * ((k + j - 1).choose j : R) *
            (Nat.stirlingSecond n (k + j - 1) : R)
        else 0 := by
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := ⟨k - 1, by omega⟩
  have hindex (j : ℕ) : l + 1 + j - 1 = l + j := by omega
  simpa only [hindex] using second_reverse_row_succ R n l

/-- **The exact finite-range reverse row formula of the manuscript.**

For `k ≥ 1`, only `2 ≤ j ≤ n-k+1` contributes. Here `(-1)^j C(k+j-1,j)`
is the generalized binomial coefficient `C(-k,j)`. Thus this is precisely
`eq:second-reverse-row`, with the stronger boundary range of every `n ≥ 0`
and coefficients in any ring. -/
theorem second_reverse_row_ring_Icc (R : Type*) [Ring R] (n k : ℕ) (hk : 1 ≤ k) :
    ((n : R) - (k : R)) * (Nat.stirlingSecond n k : R) =
      ∑ j ∈ Icc 2 (n - k + 1),
        (-1 : R) ^ j * ((j - 2).factorial : R) * ((k + j - 1).choose j : R) *
          (Nat.stirlingSecond n (k + j - 1) : R) := by
  rw [second_reverse_row_ring R n k hk]
  let T : ℕ → R := fun j =>
    (-1 : R) ^ j * ((j - 2).factorial : R) * ((k + j - 1).choose j : R) *
      (Nat.stirlingSecond n (k + j - 1) : R)
  change (∑ j ∈ range (n + 1), if 2 ≤ j then T j else 0) =
    ∑ j ∈ Icc 2 (n - k + 1), T j
  calc
    (∑ j ∈ range (n + 1), if 2 ≤ j then T j else 0) =
        ∑ j ∈ Icc 2 (n - k + 1), if 2 ≤ j then T j else 0 := by
      symm
      apply Finset.sum_subset
      · intro j hj
        simp only [mem_Icc, mem_range] at hj ⊢
        omega
      · intro j _ hj
        by_cases hj2 : 2 ≤ j
        · rw [if_pos hj2]
          have hupper : n - k + 1 < j := by
            simp only [mem_Icc, hj2, true_and, not_le] at hj
            exact hj
          have hzero : n < k + j - 1 := by omega
          simp [T, Nat.stirlingSecond_eq_zero_of_lt hzero]
        · rw [if_neg hj2]
    _ = _ := Finset.sum_congr rfl fun j hj => if_pos (mem_Icc.mp hj).1

/-- **The rational reverse row recurrence, with the manuscript's exact summation range.**

This is `eq:second-reverse-row` of `thm:second-reverse-recurrences` in
`Combinatorial_Coefficient_Calculus`, where the generalized binomial coefficient
`C(-k,j)` is written as `(-1)^j C(k+j-1,j)`. The manuscript assumes `1 ≤ k < n`;
only `1 ≤ k` is needed. -/
theorem second_reverse_row (n k : ℕ) (hk : 1 ≤ k) :
    ((n : ℚ) - (k : ℚ)) * (Nat.stirlingSecond n k : ℚ) =
      ∑ j ∈ Icc 2 (n - k + 1),
        (-1 : ℚ) ^ j * ((j - 2).factorial : ℚ) * ((k + j - 1).choose j : ℚ) *
          (Nat.stirlingSecond n (k + j - 1) : ℚ) :=
  second_reverse_row_ring_Icc ℚ n k hk

end ReverseRow

end Fabius
