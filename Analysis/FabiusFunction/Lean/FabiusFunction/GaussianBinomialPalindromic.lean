import FabiusFunction.GaussianBinomialAtOne
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Eval.Coeff

/-!
# Degree and palindromicity of the Gaussian coefficient

The universal Gaussian coefficient `[n,k]_X ∈ R[X]` (`0 ≤ k ≤ n`) has degree
`k(n-k)`, constant term `1`, leading coefficient `1`, and a **palindromic**
coefficient sequence: reflecting it in degree `k(n-k)` returns it.  The
palindromicity is proved by induction from the two `q`-Pascal recurrences:
reflecting `[n,k+1]_X + X^{n-k}[n,k]_X` in degree `(k+1)(n-k)` gives
`X^{k+1}[n,k+1]_X + [n,k]_X`, which is the other recurrence.
For a strict interior column `0 < k < n`, the coefficient of `X` is one.

The immediate consequence for the inversion distribution with generating
function `[n,k]_q` is that its mean is `k(n-k)/2`, in the division-free form

`2 · ([n,k]_X)'(1) = k(n-k) · \binom nk`.

## Main declarations

* `gaussianBinomial_natDegree_le`, `gaussianBinomial_natDegree`,
  `gaussianBinomial_monic`.
* `reflect_gaussianBinomial`: `reflect (k(n-k)) [n,k]_X = [n,k]_X`.
* `coeff_gaussianBinomial_reflect`: `c_j = c_{k(n-k)-j}`.
* `coeff_gaussianBinomial_zero`, `coeff_gaussianBinomial_top`.
* `coeff_gaussianBinomial_one_of_pos_of_lt` and
  `coeff_gaussianBinomial_one`: the strict-interior and total linear
  coefficient formulas.
* `two_mul_derivative_gaussianBinomial_eval_one`: the mean.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Polynomial

variable {R : Type*} [CommSemiring R]

/-- Reflecting in a larger degree multiplies by a power of `X`. -/
theorem reflect_add_of_natDegree_le (f : R[X]) {M m : ℕ} (hf : f.natDegree ≤ M) :
    reflect (M + m) f = reflect M f * X ^ m := by
  conv_lhs => rw [← mul_one f]
  rw [reflect_mul f 1 hf (natDegree_one.le.trans (Nat.zero_le m)), ← C_1, reflect_C, C_1, one_mul]

/-- Reflecting the constant polynomial one in degree `N` produces `X ^ N`. -/
theorem reflect_one' (N : ℕ) : reflect N (1 : R[X]) = X ^ N := by
  rw [← C_1, reflect_C, C_1, one_mul]

/-- `[n,k]_X` has degree at most `k(n-k)`. -/
theorem gaussianBinomial_natDegree_le (n k : ℕ) :
    (gaussianBinomial (X : R[X]) n k).natDegree ≤ k * (n - k) := by
  induction n generalizing k with
  | zero => cases k <;> simp
  | succ n ih =>
      cases k with
      | zero => simp
      | succ k =>
          rw [gaussianBinomial_succ_succ]
          refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
          · exact (ih (k + 1)).trans (Nat.mul_le_mul_left _ (by omega))
          · refine natDegree_mul_le.trans ((add_le_add (natDegree_X_pow_le _) (ih k)).trans ?_)
            rw [show n + 1 - (k + 1) = n - k by omega]
            exact le_of_eq (by ring)

/-- `[n,k]_0 = 1` for `k ≤ n`. -/
theorem gaussianBinomial_zero_left {n k : ℕ} (hk : k ≤ n) : gaussianBinomial (0 : R) n k = 1 := by
  induction n generalizing k with
  | zero =>
      obtain rfl : k = 0 := Nat.le_zero.mp hk
      simp
  | succ n ih =>
      cases k with
      | zero => simp
      | succ k =>
          rw [gaussianBinomial_succ_succ]
          rcases Nat.lt_or_ge k n with h | h
          · rw [ih (by omega), zero_pow (by omega), zero_mul, add_zero]
          · have hkn : k = n := by omega
            rw [hkn, gaussianBinomial_eq_zero_of_lt _ (Nat.lt_succ_self n), Nat.sub_self, pow_zero,
              one_mul, ih le_rfl, zero_add]

/-- The diagonal Gaussian coefficient is one. -/
theorem gaussianBinomial_diag' (q : R) (n : ℕ) : gaussianBinomial q n n = 1 := by
  rw [← gaussianBinomial_symm q le_rfl, Nat.sub_self, gaussianBinomial_zero_right]

/-- **Palindromicity**: `reflect (k(n-k)) [n,k]_X = [n,k]_X` for `k ≤ n`. -/
theorem reflect_gaussianBinomial {n k : ℕ} (hk : k ≤ n) :
    reflect (k * (n - k)) (gaussianBinomial (X : R[X]) n k) = gaussianBinomial (X : R[X]) n k := by
  induction n generalizing k with
  | zero =>
      obtain rfl : k = 0 := Nat.le_zero.mp hk
      simp
  | succ n ih =>
      cases k with
      | zero => simp
      | succ k =>
          conv_lhs => rw [gaussianBinomial_succ_succ, reflect_add]
          rcases Nat.lt_or_ge k n with hkn | hkn
          · have hD1 : (k + 1) * (n + 1 - (k + 1)) = (k + 1) * (n - (k + 1)) + (k + 1) := by
              rw [show n + 1 - (k + 1) = n - (k + 1) + 1 by omega, mul_add, mul_one]
            have hD2 : (k + 1) * (n + 1 - (k + 1)) = (n - k) + k * (n - k) := by
              rw [show n + 1 - (k + 1) = n - k by omega]
              ring
            have hA : reflect ((k + 1) * (n + 1 - (k + 1))) (gaussianBinomial (X : R[X]) n (k + 1)) =
                gaussianBinomial (X : R[X]) n (k + 1) * X ^ (k + 1) := by
              rw [hD1, reflect_add_of_natDegree_le _ (gaussianBinomial_natDegree_le n (k + 1)),
                ih (by omega)]
            have hB : reflect ((k + 1) * (n + 1 - (k + 1)))
                (X ^ (n - k) * gaussianBinomial (X : R[X]) n k) = gaussianBinomial (X : R[X]) n k := by
              rw [hD2, reflect_mul _ _ (natDegree_X_pow_le _) (gaussianBinomial_natDegree_le n k),
                reflect_monomial, revAt_le le_rfl, Nat.sub_self, pow_zero, one_mul, ih (by omega)]
            rw [hA, hB, gaussianBinomial_succ_succ_alt, mul_comm]
          · obtain rfl : k = n := by omega
            simp [gaussianBinomial_eq_zero_of_lt]

/-- **Coefficient reversal**: `c_j = c_{k(n-k)-j}` for `j ≤ k(n-k)`. -/
theorem coeff_gaussianBinomial_reflect {n k : ℕ} (hk : k ≤ n) {j : ℕ} (hj : j ≤ k * (n - k)) :
    (gaussianBinomial (X : R[X]) n k).coeff j =
      (gaussianBinomial (X : R[X]) n k).coeff (k * (n - k) - j) := by
  conv_lhs => rw [← reflect_gaussianBinomial hk]
  rw [coeff_reflect, revAt_le hj]

/-- The constant term of `[n,k]_X` is `1`. -/
theorem coeff_gaussianBinomial_zero {n k : ℕ} (hk : k ≤ n) :
    (gaussianBinomial (X : R[X]) n k).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero]
  have h := map_gaussianBinomial (evalRingHom (0 : R)) (X : R[X]) n k
  rw [coe_evalRingHom, eval_X] at h
  rw [h, gaussianBinomial_zero_left hk]

/-- In every strict interior column `0 < k < n`, the coefficient of `X` in
the Gaussian polynomial `[n,k]_X` is one. -/
theorem coeff_gaussianBinomial_one_of_pos_of_lt
    {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    (gaussianBinomial (X : R[X]) n k).coeff 1 = 1 := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
      cases k with
      | zero => omega
      | succ k =>
          rw [gaussianBinomial_succ_succ_alt, coeff_add]
          by_cases hk0 : k = 0
          · subst k
            simp [coeff_gaussianBinomial_zero (R := R) (by omega : 1 ≤ n), coeff_one]
          · rw [coeff_X_pow_mul', if_neg (by omega : ¬ k + 1 ≤ 1),
              ih (by omega) (by omega), zero_add]

/-- **Complete linear-coefficient classification.**  The coefficient of `X`
in `[n,k]_X` is one exactly in the strict interior `0 < k < n`; it is zero
on the lower edge, on the diagonal, and above the diagonal. -/
theorem coeff_gaussianBinomial_one (n k : ℕ) :
    (gaussianBinomial (X : R[X]) n k).coeff 1 =
      if 0 < k ∧ k < n then 1 else 0 := by
  by_cases h : 0 < k ∧ k < n
  · rw [if_pos h, coeff_gaussianBinomial_one_of_pos_of_lt h.1 h.2]
  · rw [if_neg h]
    by_cases hk0 : k = 0
    · subst k
      simp [coeff_one]
    · have hnk : n ≤ k := by
        by_contra hnk
        exact h ⟨Nat.pos_of_ne_zero hk0, Nat.lt_of_not_ge hnk⟩
      rcases eq_or_lt_of_le hnk with hdiag | habove
      · subst k
        simp [coeff_one]
      · rw [gaussianBinomial_eq_zero_of_lt (X : R[X]) habove]
        simp

/-- The coefficient of `X^{k(n-k)}` in `[n,k]_X` is `1`. -/
theorem coeff_gaussianBinomial_top {n k : ℕ} (hk : k ≤ n) :
    (gaussianBinomial (X : R[X]) n k).coeff (k * (n - k)) = 1 := by
  have h := coeff_gaussianBinomial_reflect (R := R) hk (Nat.zero_le (k * (n - k)))
  rw [Nat.sub_zero, coeff_gaussianBinomial_zero hk] at h
  exact h.symm

/-- **The degree** of `[n,k]_X` is exactly `k(n-k)`. -/
theorem gaussianBinomial_natDegree [Nontrivial R] {n k : ℕ} (hk : k ≤ n) :
    (gaussianBinomial (X : R[X]) n k).natDegree = k * (n - k) :=
  natDegree_eq_of_le_of_coeff_ne_zero (gaussianBinomial_natDegree_le n k)
    (by rw [coeff_gaussianBinomial_top hk]; exact one_ne_zero)

/-- `[n,k]_X` is monic. -/
theorem gaussianBinomial_monic [Nontrivial R] {n k : ℕ} (hk : k ≤ n) :
    (gaussianBinomial (X : R[X]) n k).Monic := by
  rw [Monic, leadingCoeff, gaussianBinomial_natDegree hk, coeff_gaussianBinomial_top hk]

/-- **The mean of the inversion distribution**, division-free:
`2 · ([n,k]_X)'(1) = k(n-k) · \binom nk`. -/
theorem two_mul_derivative_gaussianBinomial_eval_one {n k : ℕ} (hk : k ≤ n) :
    2 * (derivative (gaussianBinomial (X : R[X]) n k)).eval 1 =
      ((k * (n - k) : ℕ) : R) * (n.choose k : R) := by
  have hdeg : (gaussianBinomial (X : R[X]) n k).natDegree < k * (n - k) + 1 :=
    Nat.lt_succ_of_le (gaussianBinomial_natDegree_le n k)
  have hsum : (derivative (gaussianBinomial (X : R[X]) n k)).eval 1 =
      ∑ j ∈ Finset.range (k * (n - k) + 1),
        (j : R) * (gaussianBinomial (X : R[X]) n k).coeff j := by
    rw [derivative_eval, sum_over_range' _ (fun j => by simp) (k * (n - k) + 1) hdeg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [one_pow, mul_one, mul_comm]
  have hsym : ∑ j ∈ Finset.range (k * (n - k) + 1),
        (j : R) * (gaussianBinomial (X : R[X]) n k).coeff j =
      ∑ j ∈ Finset.range (k * (n - k) + 1),
        ((k * (n - k) - j : ℕ) : R) * (gaussianBinomial (X : R[X]) n k).coeff j := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < k * (n - k) + 1 := Finset.mem_range.mp hj
    rw [coeff_gaussianBinomial_reflect hk (by omega : k * (n - k) + 1 - 1 - j ≤ k * (n - k)),
      show k * (n - k) + 1 - 1 - j = k * (n - k) - j by omega,
      show k * (n - k) - (k * (n - k) - j) = j by omega]
  have heval : (gaussianBinomial (X : R[X]) n k).eval 1 = (n.choose k : R) := by
    have h := map_gaussianBinomial (evalRingHom (1 : R)) (X : R[X]) n k
    rw [coe_evalRingHom, eval_X] at h
    rw [h, gaussianBinomial_one_eq_natCast_choose]
  have hsumP : (gaussianBinomial (X : R[X]) n k).eval 1 =
      ∑ j ∈ Finset.range (k * (n - k) + 1), (gaussianBinomial (X : R[X]) n k).coeff j := by
    rw [eval_eq_sum_range' hdeg]
    simp
  calc 2 * (derivative (gaussianBinomial (X : R[X]) n k)).eval 1
      = (derivative (gaussianBinomial (X : R[X]) n k)).eval 1 +
          (derivative (gaussianBinomial (X : R[X]) n k)).eval 1 := two_mul _
    _ = ∑ j ∈ Finset.range (k * (n - k) + 1),
          ((j : R) + ((k * (n - k) - j : ℕ) : R)) * (gaussianBinomial (X : R[X]) n k).coeff j := by
        rw [hsum]
        nth_rewrite 2 [hsym]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ j ∈ Finset.range (k * (n - k) + 1),
          ((k * (n - k) : ℕ) : R) * (gaussianBinomial (X : R[X]) n k).coeff j := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj' : j ≤ k * (n - k) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        rw [← Nat.cast_add, Nat.add_sub_of_le hj']
    _ = ((k * (n - k) : ℕ) : R) * (n.choose k : R) := by
        rw [← Finset.mul_sum, ← hsumP, heval]

end Fabius
