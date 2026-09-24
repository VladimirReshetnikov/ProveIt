import Diophantine.Paper1976.FiveSquarePrimePolynomial

/-!
# Theorem 3: an exact prime range using a discrete zero-test

The square of the five-square combining polynomial is nonnegative on every
natural assignment. The function `2 + k * 0 ^ M` therefore uses an ordinary
natural exponent, with Lean's convention `0 ^ 0 = 1`. A failed test gives
the prime two, and a successful test gives the prime `k + 2`.

There are twelve coordinates: one parameter and eleven natural witnesses.
The final theorem packages this as the article's assertion with `n ≤ 11`.
-/

namespace JSWW1976.PrimeZeroTest

open MvPolynomial
open TwelveVariable (Poly assignment)

noncomputable section

/-- The nonnegative integer polynomial used as the zero-test exponent. -/
def M : Poly := FiveSquarePrimePolynomial.combined ^ 2

theorem eval_M (v : Fin 12 → ℤ) :
    eval v M = (eval v FiveSquarePrimePolynomial.combined) ^ 2 := by
  simp only [M, eval_pow]

/-- Nonnegativity holds for all natural assignments, including failed tests. -/
theorem eval_M_nonneg (v : Fin 12 → ℕ) :
    0 ≤ eval (fun idx => (v idx : ℤ)) M := by
  rw [eval_M]
  exact sq_nonneg _

/-- Converting the nonnegative exponent to a natural preserves its zero set. -/
theorem exponent_eq_zero_iff (v : Fin 12 → ℕ) :
    (eval (fun idx => (v idx : ℤ)) M).toNat = 0 ↔
      eval (fun idx => (v idx : ℤ)) FiveSquarePrimePolynomial.combined = 0 := by
  constructor
  · intro hzero
    have hnonneg := eval_M_nonneg v
    have heq : eval (fun idx => (v idx : ℤ)) M = 0 := by omega
    rw [eval_M] at heq
    exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp heq
  · intro hzero
    simp only [eval_M, hzero, zero_pow (by decide : 2 ≠ 0), Int.toNat_zero]

/-- The exact prime-valued function in Theorem 3. -/
def zeroTestPrime (v : Fin 12 → ℕ) : ℕ :=
  2 + v 0 * 0 ^ (eval (fun idx => (v idx : ℤ)) M).toNat

/-- The convention `0 ^ 0 = 1` makes a successful test return `k + 2`. -/
theorem zeroTestPrime_of_zero (v : Fin 12 → ℕ)
    (hzero : eval (fun idx => (v idx : ℤ)) FiveSquarePrimePolynomial.combined = 0) :
    zeroTestPrime v = v 0 + 2 := by
  simp only [zeroTestPrime, (exponent_eq_zero_iff v).mpr hzero, pow_zero, mul_one]
  exact Nat.add_comm _ _

/-- A failed test returns the prime two. -/
theorem zeroTestPrime_of_ne_zero (v : Fin 12 → ℕ)
    (hzero : eval (fun idx => (v idx : ℤ)) FiveSquarePrimePolynomial.combined ≠ 0) :
    zeroTestPrime v = 2 := by
  have hexp : (eval (fun idx => (v idx : ℤ)) M).toNat ≠ 0 :=
    fun h => hzero ((exponent_eq_zero_iff v).mp h)
  simp only [zeroTestPrime, zero_pow hexp, mul_zero, add_zero]

/-- The parameter-zero boundary returns two independently of the witnesses. -/
theorem zeroTestPrime_of_parameter_zero (v : Fin 12 → ℕ) (hk : v 0 = 0) :
    zeroTestPrime v = 2 := by
  simp only [zeroTestPrime, hk, zero_mul, add_zero]

/-- Every value is prime; there is no positivity filter on the output. -/
theorem zeroTestPrime_prime (v : Fin 12 → ℕ) : Nat.Prime (zeroTestPrime v) := by
  by_cases hzero : eval (fun idx => (v idx : ℤ)) FiveSquarePrimePolynomial.combined = 0
  · rw [zeroTestPrime_of_zero v hzero]
    have hp := (FiveSquarePrimePolynomial.criterion_of_combined_zero v hzero).prime
      (by omega : 1 ≤ v 0 + 1)
    simpa only [Nat.add_assoc] using hp
  · rw [zeroTestPrime_of_ne_zero v hzero]
    exact Nat.prime_two

/-- Every prime admits a successful test with the prescribed prime parameter. -/
theorem exists_zero_of_prime {p : ℕ} (hp : Nat.Prime p) :
    ∃ v : Fin 12 → ℕ,
      eval (fun idx => (v idx : ℤ)) FiveSquarePrimePolynomial.combined = 0 ∧
      v 0 + 2 = p := by
  let k := p - 2
  have hk : k + 2 = p := Nat.sub_add_cancel hp.two_le
  have hprime : Nat.Prime ((k + 1) + 1) := by
    simpa only [Nat.add_assoc, hk] using hp
  obtain ⟨n, x, w, m, i, j, q, l, r, z, hcriterion⟩ :=
    (theorem_3_9_five_square (k := k + 1) (by omega)).mp hprime
  obtain ⟨t, ht⟩ := FiveSquarePrimePolynomial.exists_combined_zero_of_criterion hcriterion
  refine ⟨assignment k n x w m i j q l r z t, ht, ?_⟩
  simpa [assignment] using hk

/-- The exact range consists of all primes, including two. -/
theorem prime_iff_zeroTestPrime (p : ℕ) :
    Nat.Prime p ↔ ∃ v : Fin 12 → ℕ, zeroTestPrime v = p := by
  constructor
  · intro hp
    obtain ⟨v, hzero, hpv⟩ := exists_zero_of_prime hp
    exact ⟨v, (zeroTestPrime_of_zero v hzero).trans hpv⟩
  · rintro ⟨v, rfl⟩
    exact zeroTestPrime_prime v

/-- The same exact range, with the parameter separated from eleven witnesses. -/
theorem prime_iff_parameter_witnesses (p : ℕ) :
    Nat.Prime p ↔ ∃ k : ℕ, ∃ xs : Fin 11 → ℕ,
      2 + k * 0 ^
        (eval (fun idx => ((Fin.cons (α := fun _ => ℕ) k xs idx : ℕ) : ℤ)) M).toNat = p := by
  rw [prime_iff_zeroTestPrime, Fin.exists_fin_succ_pi]
  simp only [zeroTestPrime, Fin.cons_zero]

/-- Theorem 3, including the printed witness bound and nonnegative polynomial. -/
theorem theorem_3 :
    ∃ n : ℕ, n ≤ 11 ∧ ∃ m : MvPolynomial (Fin (n + 1)) ℤ,
      (∀ v : Fin (n + 1) → ℕ, 0 ≤ eval (fun idx => (v idx : ℤ)) m) ∧
      ∀ p : ℕ, Nat.Prime p ↔ ∃ k : ℕ, ∃ xs : Fin n → ℕ,
        2 + k * 0 ^
          (eval (fun idx => ((Fin.cons (α := fun _ => ℕ) k xs idx : ℕ) : ℤ)) m).toNat = p :=
  ⟨11, le_rfl, M, eval_M_nonneg, prime_iff_parameter_witnesses⟩

end

end JSWW1976.PrimeZeroTest
