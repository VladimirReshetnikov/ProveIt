import FabiusFunction.StirlingSecondReverseColumn
import FabiusFunction.ExpAddLog
import FabiusFunction.SmoothingOperatorExponential

/-!
# The reverse row recurrence of the second kind

`StirlingSecondReverseColumn` proves one of the two reverse recurrences the source states for
the second-kind numbers; this module proves the other,

`(n - k) S(n,k) = ∑_{j=2}^{n-k+1} (j-2)! C(-k, j) S(n, k+j-1)`   (`second_reverse_row`),

which moves along a row rather than down a column.

The source proves it with a bivariate generating function `F(x,y) = exp(y(e^x - 1))`,
differentiating `j` times in `y`.  That is not necessary, and this module follows the shorter
route instead: with `k` fixed and the sum taken over `n` alone, every term is a *column*
generating function `u^m/m!` in the single variable `x`, where `u = e^x - 1`.  Both sides then
carry the common factor `u^{k-1}/(k-1)!`, because

`(j-2)! C(-k,j) / (k+j-1)! = (-1)^j / (j(j-1)(k-1)!)`,

and what is left is the single series identity `∑_{j≥2} (-1)^j t^j/(j(j-1)) = (1+t)log(1+t) - t`
(`coeff_logTail`, one coefficient computation) evaluated at `t = u`, where `1 + u = e^x` and
`log(1+u) = x` (`log_subst_exp_sub_one` of `BellComposition`).

## Main results

* `coeff_logTail`, the coefficients of `(1+X)log(1+X) - X`.
* `subst_logTail`, its value at `u = e^x - 1`, namely `x·e^x - u`.
* `second_reverse_row`, the division-free integral reverse row recurrence.
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

section Recurrence

/-! The outer series below packages the shifted row weights.  Its coefficient
at `m + j` is

`(-1)^j (j-2)! choose(m+j,j) / (m+j)!`

for `j ≥ 2`; factorial denormalization therefore gives exactly the integer
coefficient in the reverse recurrence. -/

private noncomputable def secondReverseRowOuter (m : ℕ) : ℚ⟦X⟧ :=
  PowerSeries.C (1 / (m.factorial : ℚ)) * (X ^ m * logTail ℚ)

private noncomputable def secondReverseRowWeight (m r : ℕ) : ℚ :=
  (r.factorial : ℚ) * coeff r (secondReverseRowOuter m)

private theorem egfA_secondReverseRowWeight (m : ℕ) :
    egfA ℚ (secondReverseRowWeight m) = secondReverseRowOuter m := by
  ext r
  rw [coeff_egfA]
  simp only [secondReverseRowWeight]
  have hr : (r.factorial : ℚ) ≠ 0 := by positivity
  change (1 / (r.factorial : ℚ)) *
      ((r.factorial : ℚ) * coeff r (secondReverseRowOuter m)) = _
  field_simp

private theorem secondReverseRowWeight_eq_zero_of_lt (m r : ℕ) (hr : r < m + 2) :
    secondReverseRowWeight m r = 0 := by
  rw [secondReverseRowWeight, secondReverseRowOuter, coeff_C_mul,
    coeff_X_pow_mul']
  by_cases hmr : m ≤ r
  · rw [if_pos hmr, coeff_logTail, if_neg (by omega), mul_zero, mul_zero]
  · rw [if_neg hmr, mul_zero, mul_zero]

private theorem secondReverseRowWeight_add_two (m i : ℕ) :
    secondReverseRowWeight m (m + 2 + i) =
      (-1 : ℚ) ^ (i + 2) * (i.factorial : ℚ) *
        ((m + 2 + i).choose (i + 2) : ℚ) := by
  rw [secondReverseRowWeight, secondReverseRowOuter, coeff_C_mul,
    coeff_X_pow_mul', if_pos (by omega), coeff_logTail, if_pos (by omega)]
  simp only [show m + 2 + i - m = i + 2 by omega]
  have hchoose :
      (((m + 2 + i).choose (i + 2) : ℚ) * ((i + 2).factorial : ℚ) *
          (m.factorial : ℚ)) = ((m + 2 + i).factorial : ℚ) := by
    have hnat := Nat.choose_mul_factorial_mul_factorial
      (show i + 2 ≤ m + 2 + i by omega)
    rw [show m + 2 + i - (i + 2) = m by omega] at hnat
    exact_mod_cast hnat
  have hfactorial :
      ((i + 2).factorial : ℚ) = (i + 2 : ℚ) * (i + 1 : ℚ) * i.factorial := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  rw [hfactorial] at hchoose
  push_cast
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  rw [show (i : ℚ) + 2 - 1 = (i : ℚ) + 1 by ring]
  rw [← hchoose]
  have hi1 : (i : ℚ) + 1 ≠ 0 := by positivity
  field_simp [hi1]

private theorem secondReverseRowOuter_subst (m : ℕ) :
    (secondReverseRowOuter m).subst (exp ℚ - 1) =
      PowerSeries.C (1 / (m.factorial : ℚ)) * (exp ℚ - 1) ^ m *
        (X * exp ℚ - (exp ℚ - 1)) := by
  have hu : HasSubst (exp ℚ - 1) := HasSubst.exp_sub_one
  rw [secondReverseRowOuter, subst_mul hu, subst_mul hu, PowerSeries.subst_C,
    subst_pow hu, subst_X hu, subst_logTail]
  simp only [PowerSeries.C_apply, mul_assoc]

private theorem egfA_secondReverseRow_lhs (m : ℕ) :
    egfA ℚ (fun n => ((n : ℚ) - (m + 1 : ℚ)) * Nat.stirlingSecond n (m + 1)) =
      PowerSeries.C (1 / (m.factorial : ℚ)) * (exp ℚ - 1) ^ m *
        (X * exp ℚ - (exp ℚ - 1)) := by
  calc
    egfA ℚ (fun n => ((n : ℚ) - (m + 1 : ℚ)) * Nat.stirlingSecond n (m + 1)) =
        X * d⁄dX ℚ (egfA ℚ fun n => (Nat.stirlingSecond n (m + 1) : ℚ)) -
          ((m + 1 : ℕ) : ℚ⟦X⟧) *
            egfA ℚ (fun n => (Nat.stirlingSecond n (m + 1) : ℚ)) := by
      rw [X_mul_derivative_egfA, natCast_mul_egfA, egfA_sub]
      congr 1
      funext n
      rw [Pi.sub_apply]
      push_cast
      ring
    _ = PowerSeries.C (1 / (m.factorial : ℚ)) * (exp ℚ - 1) ^ m *
          (X * exp ℚ - (exp ℚ - 1)) := by
      rw [egfA_stirlingSecond, Derivation.leibniz, derivative_C, smul_zero, add_zero,
        Derivation.leibniz_pow, Nat.add_sub_cancel, map_sub, Derivation.map_one_eq_zero,
        sub_zero, PowerSeries.derivative_exp, pow_succ]
      simp only [smul_eq_mul, nsmul_eq_mul]
      have hscalar :
          ((m + 1 : ℕ) : ℚ⟦X⟧) *
              PowerSeries.C (1 / ((m + 1).factorial : ℚ)) =
            PowerSeries.C (1 / (m.factorial : ℚ)) := by
        rw [← map_natCast (PowerSeries.C : ℚ →+* ℚ⟦X⟧), ← map_mul]
        congr 1
        rw [Nat.factorial_succ]
        push_cast
        field_simp
      simp only [Algebra.algebraMap_self, RingHom.id_apply]
      rw [← hscalar]
      ring

private theorem egfA_second_reverse_row (m : ℕ) :
    egfA ℚ (fun n => ((n : ℚ) - (m + 1 : ℚ)) * Nat.stirlingSecond n (m + 1)) =
      egfA ℚ fun n => ∑ r ∈ range (n + 1),
        secondReverseRowWeight m r * Nat.stirlingSecond n r := by
  have hcomp := egfA_subst_bellWeightSeries ℚ (secondReverseRowWeight m)
    (fun _ => (1 : ℚ))
  rw [egfA_secondReverseRowWeight, bellWeightSeries_one,
    secondReverseRowOuter_subst] at hcomp
  simp only [partialBell_one_cast] at hcomp
  exact (egfA_secondReverseRow_lhs m).trans hcomp

/-- **Reverse row recurrence of the second kind**, in a division-free
integral form.  The manuscript's generalized binomial coefficient is written
as `choose(k+i+1,i+2)` using
`binom(-k,i+2) = (-1)^(i+2) choose(k+i+1,i+2)`.  Unlike the divided
form, this cleared identity also holds when `n ≤ k`, since both sides vanish. -/
theorem second_reverse_row (n k : ℕ) (hk : 1 ≤ k) :
    ((n - k : ℕ) : ℤ) * (Nat.stirlingSecond n k : ℤ) =
      ∑ i ∈ range (n - k),
        (-1 : ℤ) ^ (i + 2) * (i.factorial : ℤ) *
          ((k + i + 1).choose (i + 2) : ℤ) *
            (Nat.stirlingSecond n (k + i + 1) : ℤ) := by
  by_cases hkn : k < n
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hmn : m + 1 < n := by omega
    have hseq := congrFun (seq_eq_of_egfA_eq ℚ (egfA_second_reverse_row m)) n
    have hzero :
        ∑ r ∈ range (m + 2),
          secondReverseRowWeight m r * (Nat.stirlingSecond n r : ℚ) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      rw [secondReverseRowWeight_eq_zero_of_lt m r (Finset.mem_range.mp hr), zero_mul]
    rw [← Nat.Ico_zero_eq_range,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le (m + 2))
        (show m + 2 ≤ n + 1 by omega),
      Nat.Ico_zero_eq_range, hzero, zero_add] at hseq
    have htail :
        (∑ r ∈ Ico (m + 2) (n + 1),
            secondReverseRowWeight m r * (Nat.stirlingSecond n r : ℚ)) =
          ∑ i ∈ range (n - (m + 1)),
            (-1 : ℚ) ^ (i + 2) * (i.factorial : ℚ) *
              ((m + 1 + i + 1).choose (i + 2) : ℚ) *
                (Nat.stirlingSecond n (m + 1 + i + 1) : ℚ) := by
      rw [Finset.sum_Ico_eq_sum_range,
        show n + 1 - (m + 2) = n - (m + 1) by omega]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [secondReverseRowWeight_add_two]
      rw [show m + 2 + i = m + 1 + i + 1 by omega]
    rw [htail] at hseq
    have hq :
        ((n - (m + 1) : ℕ) : ℚ) * (Nat.stirlingSecond n (m + 1) : ℚ) =
          ∑ i ∈ range (n - (m + 1)),
            (-1 : ℚ) ^ (i + 2) * (i.factorial : ℚ) *
              ((m + 1 + i + 1).choose (i + 2) : ℚ) *
                (Nat.stirlingSecond n (m + 1 + i + 1) : ℚ) := by
      rw [Nat.cast_sub hmn.le]
      simpa only [Nat.cast_add, Nat.cast_one] using hseq
    exact_mod_cast hq
  · simp [Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hkn)]

end Recurrence

end Fabius
