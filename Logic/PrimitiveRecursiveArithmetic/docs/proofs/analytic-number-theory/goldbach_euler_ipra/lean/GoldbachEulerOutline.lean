/--
Goldbach--Euler theorem: executable/Mathlib formalization outline.

STATUS: outline only.  The declarations with `sorry` are proof obligations,
not completed verification.  The accompanying paper gives complete human
proofs and a dependency order intended to make each `sorry` routine.
-/

import Mathlib

open scoped BigOperators

namespace GoldbachEuler

/-- Bounded Boolean test: `n = a^e` for some `2 <= a,e <= n`. -/
def perfectPowerB (n : ℕ) : Bool :=
  (Finset.Icc 2 n).any fun a =>
    (Finset.Icc 2 n).any fun e => decide (a ^ e = n)

/-- The mathematical predicate corresponding to the executable test. -/
def IsPerfectPower (n : ℕ) : Prop := perfectPowerB n = true

/-- A base is canonical/root-free when it is at least two and is not itself
    a nontrivial perfect power. -/
def RootFree (r : ℕ) : Prop := 2 ≤ r ∧ perfectPowerB r = false

/-- `n = r^e` in canonical form. -/
def Canonical (n r e : ℕ) : Prop :=
  RootFree r ∧ 1 ≤ e ∧ r ^ e = n

/-- Target partial sum: each perfect-power value occurs once because the sum is
    indexed by the value `n`, not by a presentation `a^e`. -/
noncomputable def partial (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.Icc 2 N,
    if perfectPowerB n = true then (1 : ℚ) / ((n - 1 : ℕ) : ℚ) else 0

/-- The explicit dyadic convergence modulus proved in the paper. -/
def modulus (k : ℕ) : ℕ := 2 ^ (2 * (k + 1) ^ 2)

/-- Every integer `n >= 2` has a unique canonical root/exponent pair.

Suggested proof: factor `n`; let `e` be the gcd of its positive prime
valuations and divide every valuation by `e` to obtain `r`.
-/
theorem canonical_exists_unique {n : ℕ} (hn : 2 ≤ n) :
    ∃! z : ℕ × ℕ, Canonical n z.1 z.2 := by
  sorry

/-- Canonical pairs map injectively to powers. -/
theorem canonical_pow_injective
    {r u i j : ℕ} (hr : RootFree r) (hu : RootFree u)
    (hi : 1 ≤ i) (hj : 1 ≤ j) (h : r ^ i = u ^ j) :
    r = u ∧ i = j := by
  sorry

/-- Finite geometric identity used to expand a denominator. -/
theorem geom_denominator (r s I : ℕ)
    (hr : 2 ≤ r) (hs : 1 ≤ s) :
    (1 : ℚ) / ((r ^ s - 1 : ℕ) : ℚ)
      = (∑ i ∈ Finset.Icc 1 I, (1 : ℚ) / ((r ^ (s * i) : ℕ) : ℚ))
        + (1 : ℚ) /
          (((r ^ (s * I)) * (r ^ s - 1) : ℕ) : ℚ) := by
  sorry

/-- Finite geometric identity in the exponent variable. -/
theorem geom_exponent (m S : ℕ) (hm : 2 ≤ m) (hS : 2 ≤ S) :
    (∑ s ∈ Finset.Icc 2 S, (1 : ℚ) / ((m ^ s : ℕ) : ℚ))
      = (1 : ℚ) / ((m * (m - 1) : ℕ) : ℚ)
        - (1 : ℚ) / (((m ^ S) * (m - 1) : ℕ) : ℚ) := by
  sorry

/-- Telescoping kernel. -/
theorem telescoping (M : ℕ) (hM : 2 ≤ M) :
    (∑ m ∈ Finset.Icc 2 M, (1 : ℚ) / ((m * (m - 1) : ℕ) : ℚ))
      = 1 - (1 : ℚ) / (M : ℚ) := by
  sorry

/-- Every finite target partial sum is at most one.

The proof is the finite truncation argument from the paper: assuming a rational
positive gap above one, take enough terms from every geometric expansion to
preserve that gap, group by `m = r^i`, and dominate by a finite telescoping
sum strictly below one.
-/
theorem partial_le_one (N : ℕ) : partial N ≤ 1 := by
  sorry

/-- Quantitative lower bound at the explicit cutoff. -/
theorem one_sub_partial_modulus (k : ℕ) :
    1 - partial (modulus k) ≤ (1 : ℚ) / ((2 ^ k : ℕ) : ℚ) := by
  sorry

/-- Monotonicity of target partial sums. -/
theorem partial_mono : Monotone partial := by
  sorry

/-- Effective Goldbach--Euler theorem. -/
theorem goldbachEuler_effective (k N : ℕ) (hN : modulus k ≤ N) :
    0 ≤ 1 - partial N ∧
    1 - partial N ≤ (1 : ℚ) / ((2 ^ k : ℕ) : ℚ) := by
  constructor
  · exact sub_nonneg.mpr (partial_le_one N)
  · calc
      1 - partial N ≤ 1 - partial (modulus k) := by
        exact sub_le_sub_left (partial_mono hN) 1
      _ ≤ (1 : ℚ) / ((2 ^ k : ℕ) : ℚ) := one_sub_partial_modulus k

end GoldbachEuler
