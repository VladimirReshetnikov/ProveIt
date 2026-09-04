import FabiusFunction.LambertPolynomialStirling
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Nat.Choose.Cast

/-!
# Coefficients of the Lambert coefficient polynomials

The transseries volume's `plt:cor:lambert-coefficients`, items (i), (ii),
(iii), (v) and (vii), read off the Stirling-number formula of
`LambertPolynomialStirling` together with the values Mathlib carries for
the unsigned first-kind numbers: `c(n,1) = (n-1)!`, `c(n,n) = 1`,
`c(n,n-1) = C(n,2)`.  Items (iv) and (vi), the coefficients of `u^{n-1}`
and `u^{n-2}`, need `c(n,2) = (n-1)!·H_{n-1}` and the `H^{(2)}` identity
(`plt:lem:om-stirling-values`), which are not in Mathlib; they are being
formalized in the coefficient-calculus lane and will be cited from there.

* `stirlingFirst_pos` — `c(n,k) > 0` for `1 ≤ k ≤ n`, by induction on
  Mathlib's recurrence; the one combinatorial input.
* `coeff_lambertPoly_eq_unsigned` — **the unsigned form**
  (`plt:eq:lambert-stirling`): `[u^m] Pₙ = (-1)^{n-m} c(n, n+1-m)/m!`.
* `neg_one_pow_mul_coeff_lambertPoly_pos`, `coeff_lambertPoly_ne_zero` —
  **(ii)**: all `n` coefficients are nonzero and strictly alternate.
* `natDegree_lambertPoly`, `X_dvd_lambertPoly`, with
  `coeff_lambertPoly_of_lt` and `coeff_lambertPoly_succ_self` — **(i)**.
* `coeff_lambertPoly_self` — **(iii)**: `[uⁿ] Pₙ = 1/n`.
* `coeff_lambertPoly_one` — **(v)**: `[u] Pₙ = (-1)^{n-1}`.
* `coeff_lambertPoly_two` — **(vii)**: `[u²] Pₙ = (-1)ⁿ n(n-1)/4`.
-/

set_option autoImplicit false

open Polynomial Finset

namespace Fabius

/-- Unsigned Stirling numbers of the first kind are positive on `1 ≤ k ≤ n`:
there is at least one permutation of `n` letters with `k` cycles. -/
theorem stirlingFirst_pos : ∀ n k : ℕ, 1 ≤ k → k ≤ n → 0 < Nat.stirlingFirst n k
  | 0, _, hk, hkn => by omega
  | n + 1, k, hk, hkn => by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · rw [Nat.stirlingFirst_one_right]
        exact Nat.factorial_pos n
      · rw [Nat.stirlingFirst_succ_succ]
        have := stirlingFirst_pos n j hj (by omega)
        omega

/-- Above `u^{n+1}` every coefficient of `Pₙ` vanishes. -/
theorem coeff_lambertPoly_of_lt (n m : ℕ) (hm : n + 1 < m) :
    (lambertPoly n).coeff m = 0 := by
  rw [lambertPoly, lambertFallingOp_eq_derivEval, derivEval_descPochhammer_apply,
    coeff_C_mul, finsetSum_coeff]
  simp only [iterate_derivative_X_pow_eq_smul, coeff_smul, coeff_X_pow, smul_eq_mul]
  rw [sum_eq_zero, mul_zero]
  intro k hk
  rw [mem_range] at hk
  rw [if_neg (by omega), mul_zero, mul_zero]

/-- The coefficient of `u^{n+1}` vanishes for `n ≥ 1`: the operator has `n`
factors and the first one already lowers the degree. -/
theorem coeff_lambertPoly_succ_self (n : ℕ) (hn : 1 ≤ n) :
    (lambertPoly n).coeff (n + 1) = 0 := by
  rw [coeff_lambertPoly n (n + 1) le_rfl, Nat.sub_self]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [signedStirlingFirst_succ_zero]
  simp

/-- **The unsigned form** (`plt:eq:lambert-stirling`): for `1 ≤ m ≤ n`,
`[u^m] Pₙ = (-1)^{n-m} · c(n, n+1-m) / m!`. -/
theorem coeff_lambertPoly_eq_unsigned (n m : ℕ) (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    (lambertPoly n).coeff m =
      (-1) ^ (n - m) * (Nat.stirlingFirst n (n + 1 - m) : ℚ) / (m.factorial : ℚ) := by
  rw [coeff_lambertPoly n m (by omega), signedStirlingFirst]
  push_cast
  have hpow : ((-1 : ℚ)) ^ (n + 1) * (-1) ^ (n - (n + 1 - m)) = (-1) ^ (n - m) := by
    rw [← pow_add, show n + 1 + (n - (n + 1 - m)) = (n - m) + 2 * m by omega, pow_add,
      pow_mul]
    simp
  rw [← hpow]
  ring

/-- **Nonvanishing and alternation** (`plt:cor:lambert-coefficients` (ii)):
`(-1)^{n-m} · [u^m] Pₙ > 0` for `1 ≤ m ≤ n`. -/
theorem neg_one_pow_mul_coeff_lambertPoly_pos (n m : ℕ) (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    0 < (-1) ^ (n - m) * (lambertPoly n).coeff m := by
  rw [coeff_lambertPoly_eq_unsigned n m hm1 hmn]
  have hpos : (0 : ℚ) < Nat.stirlingFirst n (n + 1 - m) := by
    exact_mod_cast stirlingFirst_pos n (n + 1 - m) (by omega) (by omega)
  have h2 : ((-1 : ℚ)) ^ (n - m) * (-1) ^ (n - m) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have hfac : (0 : ℚ) < m.factorial := by exact_mod_cast m.factorial_pos
  calc (-1 : ℚ) ^ (n - m) *
        ((-1) ^ (n - m) * (Nat.stirlingFirst n (n + 1 - m) : ℚ) / (m.factorial : ℚ))
      = ((-1 : ℚ) ^ (n - m) * (-1) ^ (n - m)) *
          ((Nat.stirlingFirst n (n + 1 - m) : ℚ) / (m.factorial : ℚ)) := by ring
    _ = (Nat.stirlingFirst n (n + 1 - m) : ℚ) / (m.factorial : ℚ) := by rw [h2, one_mul]
    _ > 0 := div_pos hpos hfac

/-- `[u^m] Pₙ ≠ 0` for `1 ≤ m ≤ n`. -/
theorem coeff_lambertPoly_ne_zero (n m : ℕ) (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    (lambertPoly n).coeff m ≠ 0 := by
  intro h
  have := neg_one_pow_mul_coeff_lambertPoly_pos n m hm1 hmn
  rw [h, mul_zero] at this
  exact lt_irrefl _ this

/-- **Leading coefficient** (`plt:cor:lambert-coefficients` (iii)):
`[uⁿ] Pₙ = 1/n` for `n ≥ 1`. -/
theorem coeff_lambertPoly_self (n : ℕ) (hn : 1 ≤ n) :
    (lambertPoly n).coeff n = 1 / (n : ℚ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [coeff_lambertPoly_eq_unsigned (k + 1) (k + 1) (by omega) le_rfl, Nat.sub_self,
    show k + 1 + 1 - (k + 1) = 1 by omega, Nat.stirlingFirst_one_right, pow_zero, one_mul,
    Nat.factorial_succ]
  push_cast
  have : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  field_simp

/-- **Degree** (`plt:cor:lambert-coefficients` (i)): `deg Pₙ = n` for `n ≥ 1`. -/
theorem natDegree_lambertPoly (n : ℕ) (hn : 1 ≤ n) : (lambertPoly n).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rcases Nat.lt_or_ge (n + 1) m with h | h
    · exact coeff_lambertPoly_of_lt n m h
    · rw [show m = n + 1 by omega]
      exact coeff_lambertPoly_succ_self n hn
  · rw [coeff_lambertPoly_self n hn]
    have : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    exact one_div_ne_zero this

/-- `u ∣ Pₙ` (`plt:cor:lambert-coefficients` (i)). -/
theorem X_dvd_lambertPoly (n : ℕ) : (X : ℚ[X]) ∣ lambertPoly n := by
  rw [X_dvd_iff, coeff_zero_eq_eval_zero]
  exact lambertPoly_eval_zero n

/-- **Linear coefficient** (`plt:cor:lambert-coefficients` (v)):
`[u] Pₙ = (-1)^{n-1}` for `n ≥ 1`. -/
theorem coeff_lambertPoly_one (n : ℕ) (hn : 1 ≤ n) :
    (lambertPoly n).coeff 1 = (-1) ^ (n - 1) := by
  rw [coeff_lambertPoly_eq_unsigned n 1 le_rfl hn, Nat.add_sub_cancel, Nat.stirlingFirst_self,
    Nat.factorial_one]
  simp

/-- **Quadratic coefficient** (`plt:cor:lambert-coefficients` (vii)):
`[u²] Pₙ = (-1)ⁿ · n(n-1)/4` for `n ≥ 2`. -/
theorem coeff_lambertPoly_two (n : ℕ) (hn : 2 ≤ n) :
    (lambertPoly n).coeff 2 = (-1) ^ n * ((n : ℚ) * ((n : ℚ) - 1) / 4) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [coeff_lambertPoly_eq_unsigned (k + 1) 2 (by omega) hn,
    show k + 1 + 1 - 2 = k by omega, Nat.stirlingFirst_succ_self_left, Nat.cast_choose_two,
    show k + 1 - 2 = k - 1 by omega]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [show j + 1 - 1 = j by omega, pow_succ, pow_succ, Nat.factorial_two]
  push_cast
  ring

end Fabius
