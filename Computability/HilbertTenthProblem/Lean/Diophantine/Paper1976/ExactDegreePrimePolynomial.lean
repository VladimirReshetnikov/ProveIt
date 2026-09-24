import Diophantine.Paper1976.RefinedPolynomialDegrees
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# A twelve-variable prime polynomial of exact degree 13697

The five-square construction supplies a combined polynomial `M` of degree
at most 6848. Here we use a padded construction: multiply `M` by
`(X 11 + 1)^(6848 - M.totalDegree)`. This factor is positive on every
natural assignment, so it preserves exactly the natural zero set.

The new combined polynomial has degree exactly 6848. Applying the usual
prime-value formula gives exact total degree 13697 and the same positive
values, namely all primes. This proves the literal existence assertion
without claiming noncancellation in the unpadded polynomial.
-/

namespace JSWW1976.ExactDegreePrimePolynomial

open MvPolynomial
open TwelveVariable (Poly)

noncomputable section

/-- The combined equation cannot be identically zero: that would make four prime. -/
theorem original_combined_ne_zero : FiveSquarePrimePolynomial.combined ≠ 0 := by
  intro hzero
  have hpos : 0 < eval (fun _ : Fin 12 => (2 : ℤ)) FiveSquarePrimePolynomial.primePolynomial := by
    simp [FiveSquarePrimePolynomial.primePolynomial, hzero]
  have hp := (FiveSquarePrimePolynomial.positive_value_prime (fun _ => 2) hpos).2
  norm_num at hp

/-- The amount of positive padding needed to reach the certified upper bound. -/
def paddingExponent : ℕ := 6848 - FiveSquarePrimePolynomial.combined.totalDegree

def padding : Poly := (X 11 + 1) ^ paddingExponent

/-- The new combined equation, with the same natural zero set. -/
def paddedCombined : Poly := padding * FiveSquarePrimePolynomial.combined

private theorem totalDegree_linear (idx : Fin 12) (a : ℤ) :
    (X idx + C a : Poly).totalDegree = 1 := by
  have hlt : (C a : Poly).totalDegree < (X idx : Poly).totalDegree := by
    rw [totalDegree_C, totalDegree_X]
    decide
  rw [totalDegree_add_eq_left_of_totalDegree_lt hlt, totalDegree_X]

private theorem padding_base_degree : (X 11 + 1 : Poly).totalDegree = 1 := by
  simpa only [map_one] using totalDegree_linear 11 1

private theorem padding_base_ne_zero : (X 11 + 1 : Poly) ≠ 0 := by
  intro h
  have hd := padding_base_degree
  rw [h, totalDegree_zero] at hd
  omega

private theorem totalDegree_pow_eq {p : Poly} (hp : p ≠ 0) (n : ℕ) :
    (p ^ n).totalDegree = n * p.totalDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, totalDegree_mul_of_isDomain (pow_ne_zero n hp) hp, ih, Nat.succ_mul]

theorem padding_ne_zero : padding ≠ 0 := pow_ne_zero paddingExponent padding_base_ne_zero

theorem totalDegree_padding : padding.totalDegree = paddingExponent := by
  rw [padding, totalDegree_pow_eq padding_base_ne_zero, padding_base_degree, mul_one]

theorem paddedCombined_ne_zero : paddedCombined ≠ 0 :=
  mul_ne_zero padding_ne_zero original_combined_ne_zero

/-- Positive padding attains the combined-equation degree exactly. -/
theorem totalDegree_paddedCombined : paddedCombined.totalDegree = 6848 := by
  rw [paddedCombined, totalDegree_mul_of_isDomain padding_ne_zero original_combined_ne_zero,
    totalDegree_padding]
  exact Nat.sub_add_cancel RefinedPolynomialDegrees.totalDegree_five_combined

/-- The padding is positive, including when its exponent is zero. -/
theorem eval_padding_pos (v : Fin 12 → ℕ) :
    0 < eval (fun a => (v a : ℤ)) padding := by
  simp only [padding, map_pow, map_add, eval_X, map_one]
  exact pow_pos (by positivity) _

theorem eval_paddedCombined_zero_iff (v : Fin 12 → ℕ) :
    eval (fun a => (v a : ℤ)) paddedCombined = 0 ↔
      eval (fun a => (v a : ℤ)) FiveSquarePrimePolynomial.combined = 0 := by
  rw [paddedCombined, map_mul]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (ne_of_gt (eval_padding_pos v))
  · intro h
    rw [h, mul_zero]

/-- The prime polynomial of exact degree 13697, using the padded combined equation. -/
def primePolynomial : Poly := (X 0 + 2) * (1 - paddedCombined ^ 2)

private theorem prime_factor_degree : (X 0 + 2 : Poly).totalDegree = 1 := by
  simpa only [map_ofNat] using totalDegree_linear 0 2

private theorem prime_factor_ne_zero : (X 0 + 2 : Poly) ≠ 0 := by
  intro h
  have hd := prime_factor_degree
  rw [h, totalDegree_zero] at hd
  omega

theorem totalDegree_padded_square : (paddedCombined ^ 2).totalDegree = 13696 := by
  rw [totalDegree_pow_eq paddedCombined_ne_zero, totalDegree_paddedCombined]

theorem totalDegree_test : (1 - paddedCombined ^ 2 : Poly).totalDegree = 13696 := by
  have hlt : (1 : Poly).totalDegree < (-(paddedCombined ^ 2) : Poly).totalDegree := by
    rw [totalDegree_one, totalDegree_neg, totalDegree_padded_square]
    decide
  rw [sub_eq_add_neg, totalDegree_add_eq_right_of_totalDegree_lt hlt,
    totalDegree_neg, totalDegree_padded_square]

private theorem test_ne_zero : (1 - paddedCombined ^ 2 : Poly) ≠ 0 := by
  intro h
  have hd := totalDegree_test
  rw [h, totalDegree_zero] at hd
  omega

/-- Exact degree, obtained without an unproved leading-coefficient calculation. -/
theorem totalDegree_primePolynomial : primePolynomial.totalDegree = 13697 := by
  rw [primePolynomial, totalDegree_mul_of_isDomain prime_factor_ne_zero test_ne_zero,
    prime_factor_degree, totalDegree_test]

theorem eval_primePolynomial (v : Fin 12 → ℤ) :
    eval v primePolynomial = (v 0 + 2) * (1 - (eval v paddedCombined) ^ 2) := by
  simp [primePolynomial]

theorem positive_value_prime (v : Fin 12 → ℕ)
    (hpos : 0 < eval (fun a => (v a : ℤ)) primePolynomial) :
    eval (fun a => (v a : ℤ)) primePolynomial = (v 0 : ℤ) + 2 ∧
      Nat.Prime (v 0 + 2) := by
  have hN : eval (fun a => (v a : ℤ)) paddedCombined = 0 :=
    Diophantine.eq_zero_of_mul_one_sub_sq_pos (a := (v 0 : ℤ) + 2)
      (b := eval (fun a => (v a : ℤ)) paddedCombined) (by positivity)
      (by simpa only [eval_primePolynomial] using hpos)
  have hM := (eval_paddedCombined_zero_iff v).mp hN
  have heval : eval (fun a => (v a : ℤ)) primePolynomial = (v 0 : ℤ) + 2 := by
    simp [eval_primePolynomial, hN]
  have hold : 0 < eval (fun a => (v a : ℤ)) FiveSquarePrimePolynomial.primePolynomial := by
    simpa [FiveSquarePrimePolynomial.eval_primePolynomial, hM] using
      (show (0 : ℤ) < (v 0 : ℤ) + 2 by positivity)
  exact ⟨heval, (FiveSquarePrimePolynomial.positive_value_prime v hold).2⟩

theorem exists_value_of_prime {P : ℕ} (hP : Nat.Prime P) :
    ∃ v : Fin 12 → ℕ, eval (fun a => (v a : ℤ)) primePolynomial = (P : ℤ) := by
  obtain ⟨v, hv⟩ := FiveSquarePrimePolynomial.exists_value_of_prime hP
  have hold : 0 < eval (fun a => (v a : ℤ)) FiveSquarePrimePolynomial.primePolynomial := by
    rw [hv]
    exact_mod_cast hP.pos
  have hM : eval (fun a => (v a : ℤ)) FiveSquarePrimePolynomial.combined = 0 :=
    Diophantine.eq_zero_of_mul_one_sub_sq_pos (a := (v 0 : ℤ) + 2)
      (b := eval (fun a => (v a : ℤ)) FiveSquarePrimePolynomial.combined) (by positivity)
      (by simpa only [FiveSquarePrimePolynomial.eval_primePolynomial] using hold)
  have hN := (eval_paddedCombined_zero_iff v).mpr hM
  refine ⟨v, ?_⟩
  rw [eval_primePolynomial, hN]
  rw [FiveSquarePrimePolynomial.eval_primePolynomial, hM] at hv
  simpa using hv

/-- Positive padding preserves precisely the original prime-value set. -/
theorem prime_iff_positive_value (P : ℕ) :
    Nat.Prime P ↔ 0 < P ∧
      ∃ v : Fin 12 → ℕ, eval (fun a => (v a : ℤ)) primePolynomial = (P : ℤ) := by
  constructor
  · intro hP
    exact ⟨hP.pos, exists_value_of_prime hP⟩
  · rintro ⟨hP, v, hv⟩
    have hpos : 0 < eval (fun a => (v a : ℤ)) primePolynomial := by
      rw [hv]
      exact_mod_cast hP
    obtain ⟨he, hp⟩ := positive_value_prime v hpos
    have heq : P = v 0 + 2 := by rw [hv] at he; exact_mod_cast he
    exact heq.symm ▸ hp

/-- A literal degree-13697 polynomial in twelve variables whose positive
natural-assignment values are exactly the primes. -/
theorem exists_exact_degree_prime_polynomial :
    ∃ f : MvPolynomial (Fin 12) ℤ, f.totalDegree = 13697 ∧ ∀ P : ℕ,
      Nat.Prime P ↔ 0 < P ∧
        ∃ v : Fin 12 → ℕ, eval (fun a => (v a : ℤ)) f = (P : ℤ) :=
  ⟨primePolynomial, totalDegree_primePolynomial, prime_iff_positive_value⟩

end

end JSWW1976.ExactDegreePrimePolynomial
