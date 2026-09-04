import FabiusFunction.StirlingSecondReverseRow
import FabiusFunction.StirlingTransformEGF

/-!
# The finite reverse-row identity for second-kind Stirling numbers

The series identity in `StirlingSecondReverseRow` becomes an actual finite
recurrence here. With `u = exp X - 1`, the shared series is

`u^k / k! * logTail(u) = X * F_(k+1)' - (k+1) * F_(k+1)`.

The Stirling transform reads its coefficients without a bivariate generating
function. A single factorial identity identifies the resulting kernel with
the negative-binomial weights in the source, giving the unrestricted rational
kernel sum `second_reverse_row_sum`. The triangular commutative-ring form is a
short corollary of the stronger all-boundary theorem in
`StirlingSecondReverseRow`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

noncomputable section

private def reverseRowKernel (k m : ℕ) : ℚ :=
  if k + 2 ≤ m then
    (-1 : ℚ) ^ (m - k) * (m - k - 2).factorial * m.choose k
  else 0

private theorem reverseRowKernel_factorial (k j : ℕ) :
    (1 / ((k + j + 2).factorial : ℚ)) *
        ((-1 : ℚ) ^ (j + 2) * j.factorial * (k + j + 2).choose k) =
      (1 / (k.factorial : ℚ)) *
        ((-1 : ℚ) ^ (j + 2) / ((j + 2 : ℕ) * (j + 1 : ℕ))) := by
  have hc : ((k + j + 2).choose k : ℚ) * k.factorial * (j + 2).factorial =
      (k + j + 2).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial
      (show k ≤ k + j + 2 by omega)
    rw [show k + j + 2 - k = j + 2 by omega] at h
    exact_mod_cast h
  rw [Nat.factorial_succ, Nat.factorial_succ] at hc
  push_cast at hc ⊢
  have hk : (k.factorial : ℚ) ≠ 0 := by positivity
  have hn : ((k + j + 2).factorial : ℚ) ≠ 0 := by positivity
  have hj1 : (j : ℚ) + 1 ≠ 0 := by positivity
  have hj2 : (j : ℚ) + 2 ≠ 0 := by positivity
  field_simp [hk, hn, hj1, hj2]
  linear_combination hc

private theorem egfA_reverseRowKernel (k : ℕ) :
    egfA ℚ (reverseRowKernel k) =
      C (1 / (k.factorial : ℚ)) * (X ^ k * logTail ℚ) := by
  ext m
  rw [coeff_egfA, coeff_C_mul, coeff_X_pow_mul']
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  by_cases hm : k + 2 ≤ m
  · obtain ⟨j, rfl⟩ : ∃ j, m = k + j + 2 := ⟨m - k - 2, by omega⟩
    rw [reverseRowKernel, if_pos (by omega), if_pos (by omega),
      show k + j + 2 - k = j + 2 by omega, Nat.add_sub_cancel,
      coeff_logTail, if_pos (by omega)]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    have h := reverseRowKernel_factorial k j
    push_cast at h ⊢
    rw [show (j : ℚ) + 2 - 1 = (j : ℚ) + 1 by ring]
    exact h
  · rw [reverseRowKernel, if_neg hm, mul_zero]
    by_cases hkm : k ≤ m
    · rw [if_pos hkm, coeff_logTail, if_neg (by omega), mul_zero]
    · rw [if_neg hkm, mul_zero]

private theorem factorial_succ_reciprocal (k : ℕ) :
    ((k + 1 : ℕ) : ℚ⟦X⟧) * C (1 / ((k + 1).factorial : ℚ)) =
      C (1 / (k.factorial : ℚ)) := by
  rw [← map_natCast (C : ℚ →+* ℚ⟦X⟧) (k + 1), ← map_mul]
  congr 1
  rw [Nat.factorial_succ, Nat.cast_mul]
  have hk : (k.factorial : ℚ) ≠ 0 := by positivity
  have hk1 : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  field_simp [hk, hk1]

private theorem reverseRow_series (k : ℕ) :
    (egfA ℚ (reverseRowKernel k)).subst (exp ℚ - 1) =
      egfA ℚ (fun n =>
        ((n : ℚ) - ((k + 1 : ℕ) : ℚ)) * Nat.stirlingSecond n (k + 1)) := by
  have hu : HasSubst (exp ℚ - 1) := HasSubst.exp_sub_one
  have hder : d⁄dX ℚ (egfA ℚ (fun n => (Nat.stirlingSecond n (k + 1) : ℚ))) =
      C (1 / (k.factorial : ℚ)) * (exp ℚ - 1) ^ k * exp ℚ := by
    rw [egfA_stirlingSecond, Derivation.leibniz, derivative_C,
      smul_zero, add_zero, derivative_pow, Nat.add_sub_cancel, map_sub,
      Derivation.map_one_eq_zero, sub_zero, PowerSeries.derivative_exp]
    simp only [Algebra.algebraMap_self, RingHom.id_apply, smul_eq_mul]
    calc
      _ = (((k + 1 : ℕ) : ℚ⟦X⟧) * C (1 / ((k + 1).factorial : ℚ))) *
          (exp ℚ - 1) ^ k * exp ℚ := by ring
      _ = _ := by rw [factorial_succ_reciprocal]
  have hmul : ((k + 1 : ℕ) : ℚ⟦X⟧) *
      egfA ℚ (fun n => (Nat.stirlingSecond n (k + 1) : ℚ)) =
      C (1 / (k.factorial : ℚ)) * (exp ℚ - 1) ^ (k + 1) := by
    rw [egfA_stirlingSecond]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    rw [← mul_assoc, factorial_succ_reciprocal]
  have hleft : egfA ℚ (fun n =>
        ((n : ℚ) - ((k + 1 : ℕ) : ℚ)) * Nat.stirlingSecond n (k + 1)) =
      X * d⁄dX ℚ (egfA ℚ (fun n => (Nat.stirlingSecond n (k + 1) : ℚ))) -
        ((k + 1 : ℕ) : ℚ⟦X⟧) *
          egfA ℚ (fun n => (Nat.stirlingSecond n (k + 1) : ℚ)) := by
    rw [X_mul_derivative_egfA, natCast_mul_egfA, egfA_sub]
    congr 1
    funext n
    simp only [Pi.sub_apply]
    ring
  rw [egfA_reverseRowKernel, subst_mul hu, subst_C, subst_mul hu,
    subst_pow hu, subst_X hu, subst_logTail, hleft, hder, hmul, pow_succ]
  simp only [PowerSeries.C_apply]
  ring

/-- The reverse-row recurrence as a finite Stirling transform. It is valid
for every `n` and `k`, including rows above the chosen column: subtraction on
the left takes place in `ℚ`, and the right kernel vanishes below `k + 2`. -/
theorem second_reverse_row_sum (n k : ℕ) :
    ((n : ℚ) - ((k + 1 : ℕ) : ℚ)) * Nat.stirlingSecond n (k + 1) =
      ∑ m ∈ range (n + 1), (Nat.stirlingSecond n m : ℚ) *
        (if k + 2 ≤ m then
          (-1 : ℚ) ^ (m - k) * (m - k - 2).factorial * m.choose k
        else 0) := by
  have h := reverseRow_series k
  rw [egfA_subst_exp_sub_one] at h
  exact (congrFun (seq_eq_of_egfA_eq ℚ h) n).symm

/-- Triangular-domain compatibility form of `second_reverse_row_commRing`.
The additional hypothesis records the source's natural range but is not
needed by the stronger all-boundary theorem. -/
theorem second_reverse_row_commRing_of_le {R : Type*} [CommRing R]
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    ((n : R) - k) * Nat.stirlingSecond n k =
      ∑ i ∈ range (n - k),
        (-1 : R) ^ (i + 2) * i.factorial * (k + i + 1).choose (i + 2) *
          Nat.stirlingSecond n (k + i + 1) := by
  have _ := hkn
  exact second_reverse_row_commRing n k hk

end

end Fabius
