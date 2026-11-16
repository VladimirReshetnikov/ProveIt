/-!
Host-level specification scaffold.

This file records current mathlib theorem names and additional targets.  It is
not the object-theory iPRA proof.  The declarations containing `sorry` are
explicit formalization obligations.
-/
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Cyclotomic.Basic

open Finset
open ArithmeticFunction
open scoped ArithmeticFunction

namespace VonMangoldtTotientHost

-- Existing host theorems used as specifications.
example (n : ℕ) : n.divisors.sum Nat.totient = n :=
  Nat.sum_totient n

example {m n : ℕ} (h : m.Coprime n) :
    Nat.totient (m * n) = Nat.totient m * Nat.totient n :=
  Nat.totient_mul h

example {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    Nat.totient (p ^ k) = p ^ (k - 1) * (p - 1) :=
  Nat.totient_prime_pow hp hk

example {n : ℕ} :
    (∑ d ∈ n.divisors, Λ d) = Real.log n :=
  ArithmeticFunction.vonMangoldt_sum

-- Further host targets mirroring the report.  These are intentionally open.
theorem phi_gcd_lcm (m n : ℕ) :
    Nat.totient (Nat.gcd m n) * Nat.totient (Nat.lcm m n) =
      Nat.totient m * Nat.totient n := by
  sorry

theorem phi_rad_cross (n : ℕ) :
    Nat.totient n * n.rad = n * Nat.totient n.rad := by
  sorry

theorem menon_identity (n : ℕ) (hn : 0 < n) :
    (∑ a ∈ Finset.Icc 1 n with Nat.Coprime a n, Nat.gcd (a - 1) n) =
      Nat.totient n * n.divisors.card := by
  sorry

theorem phi_plus_pow_dvd (a b n : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) (hn : 0 < n) :
    n ∣ Nat.totient (a ^ n + b ^ n) := by
  sorry

-- Polynomial form of the root-of-unity identity.
theorem cyclotomic_dvd_gcd_sum (n : ℕ) (hn : 0 < n) :
    Polynomial.cyclotomic n ℤ ∣
      (∑ k ∈ Finset.Icc 1 n,
          Polynomial.C (Nat.gcd k n : ℤ) * Polynomial.X ^ k) -
        Polynomial.C (Nat.totient n : ℤ) := by
  sorry

end VonMangoldtTotientHost
