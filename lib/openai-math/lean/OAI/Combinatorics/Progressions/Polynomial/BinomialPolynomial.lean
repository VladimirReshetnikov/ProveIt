import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.RingTheory.Polynomial.Pochhammer

namespace OAI

section

namespace Erdos3

open Polynomial

noncomputable def binomialPolynomial (n : ℕ) : Polynomial ℚ :=
  (n.factorial : ℚ)⁻¹ • descPochhammer ℚ n

@[simp] theorem binomialPolynomial_zero : binomialPolynomial 0 = 1 := by
  simp [binomialPolynomial]

theorem factorial_smul_binomialPolynomial (n : ℕ) :
    (n.factorial : ℚ) • binomialPolynomial n = descPochhammer ℚ n := by
  rw [binomialPolynomial, smul_smul, mul_inv_cancel₀, one_smul]
  exact_mod_cast n.factorial_ne_zero

theorem binomialPolynomial_natDegree (n : ℕ) : (binomialPolynomial n).natDegree = n := by
  rw [binomialPolynomial, natDegree_smul]
  · exact descPochhammer_natDegree ℚ n
  · exact inv_ne_zero (by exact_mod_cast n.factorial_ne_zero)

theorem binomialPolynomial_eval_nat (n a : ℕ) :
    (binomialPolynomial n).eval (a : ℚ) = (a.choose n : ℚ) := by
  rw [binomialPolynomial, smul_eq_C_mul, eval_mul, eval_C,
    Nat.cast_choose_eq_descPochhammer_div ℚ a n]
  simp only [div_eq_mul_inv, mul_comm]

theorem X_pow_eq_sum_binomialPolynomial (n : ℕ) :
    (X : Polynomial ℚ) ^ n =
      ∑ k ∈ Finset.range (n + 1), ((Nat.stirlingSecond n k * k.factorial : ℕ) : ℚ) •
        binomialPolynomial k := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hinf : Set.Infinite (Set.range (fun a : ℕ => (a : ℚ))) :=
    Set.infinite_range_of_injective Nat.cast_injective
  apply hinf.mono
  rintro _ ⟨a, rfl⟩
  change eval (a : ℚ) ((X : Polynomial ℚ) ^ n) = _
  simp only [eval_pow, eval_X, eval_finsetSum, smul_eq_C_mul, eval_mul, eval_C,
    binomialPolynomial_eval_nat, Nat.cast_mul]
  have h := congrArg (fun b : ℕ => (b : ℚ)) (Nat.pow_eq_sum_stirlingSecond_mul_descFactorial a n)
  simpa only [Nat.cast_pow, Nat.cast_sum, Nat.cast_mul,
    Nat.descFactorial_eq_factorial_mul_choose, mul_assoc] using h

end Erdos3

end

end OAI
