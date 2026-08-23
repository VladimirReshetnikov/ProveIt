import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination
import Mathlib.RingTheory.Coprime.Basic

/-!
# Exponent-lattice masks: gap powers, cleared evaluations, and adjacent transport

A hypothetical two-base solution `M = 2^x`, `A = 3^x` turns every relation vector
`ν = (-p, q)` into the rational *output near-unit* `z_ν = A^q / M^p = e^{x(q log 3 - p log 2)}`.
Integer "masks" — polynomials evaluated at such near-units — are the scalar auxiliary
objects of the exponent-lattice approach.  This file formalizes its finite algebraic core.

* **One-direction gap-power theorem.**  If `P ∈ ℤ[T]` has a zero of multiplicity at least
  `r` at `T = 1`, then the cleared value `S^d P(R/S)` (for any `d ≥ deg P`) is an integer
  divisible by `(R - S)^r`.  High Prouhet/Thue–Morse contact on a single near-unit therefore
  factorizes into a power of the corresponding integer output gap, and cannot produce a
  small nonzero integer.
* **Adjacent valuation transport.**  For relation vectors `(p, q)`, `(p', q')` with
  determinant `ε = p' q - p q'` and any valuation pair `(m, n)`, the output valuations
  `u = q n - p m`, `u' = q' n - p' m` satisfy the exact identities
  `q' u - q u' = ε m` and `p' u - p u' = ε n`; multiplicatively,
  `z^{q'} / z'^{q} = M^{ε}` and `z^{p'} / z'^{p} = A^{ε}`.  For adjacent convergents
  `ε = ±1`, so the two shared pole depths are coupled by a determinant-one defect.
* **Structural primes are not shared by independent reduced gaps.**  A prime dividing a
  reduced gap `R_ν - S_ν` has valuation zero on `z_ν`; two linearly independent relation
  vectors cannot both be orthogonal to the same nonzero valuation vector.

Everything here is exact integer algebra.
-/

namespace LeanProofs.TwoBaseIntegerExponent.ExponentLatticeMask

open Polynomial Finset

/-- The cleared (homogenized) evaluation `∑_{i ≤ d} P_i R^i S^{d-i}` of an integer polynomial at
the fraction `R / S`. -/
def clearedEval (P : ℤ[X]) (d : ℕ) (R S : ℤ) : ℤ :=
  ∑ i ∈ range (d + 1), P.coeff i * R ^ i * S ^ (d - i)

/-- Over `ℚ`, the cleared evaluation is `S^d · P(R/S)` whenever `d ≥ deg P`. -/
theorem clearedEval_cast (P : ℤ[X]) {d : ℕ} (hd : P.natDegree ≤ d) {R S : ℤ} (hS : S ≠ 0) :
    (clearedEval P d R S : ℚ) = (S : ℚ) ^ d * (P.map (Int.castRingHom ℚ)).eval ((R : ℚ) / S) := by
  rw [eval_eq_sum_range' (n := d + 1) (by
    calc (P.map (Int.castRingHom ℚ)).natDegree ≤ P.natDegree := natDegree_map_le
      _ < d + 1 := by omega)]
  unfold clearedEval
  push_cast
  rw [mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have hi' := mem_range.mp hi
  rw [coeff_map, eq_intCast]
  have hSq : (S : ℚ) ≠ 0 := by exact_mod_cast hS
  rw [div_pow]
  have : (S : ℚ) ^ d = (S : ℚ) ^ (d - i) * (S : ℚ) ^ i := by
    rw [← pow_add]; congr 1; omega
  rw [this]
  field_simp

/-- **One-direction gap-power theorem.**  If `(X - 1)^r ∣ P` in `ℤ[X]` and `d ≥ deg P`, then
`(R - S)^r ∣ S^d P(R/S)` for every integer pair `R, S` with `S ≠ 0`.  Explicitly, writing
`P = (X - 1)^r Q`, the cleared value is `(R - S)^r · clearedEval Q (d - r) R S`. -/
theorem clearedEval_eq_of_dvd (Q : ℤ[X]) (r : ℕ) {d : ℕ} (hd : ((X - 1) ^ r * Q).natDegree ≤ d)
    (hr : r ≤ d) {R S : ℤ} (hS : S ≠ 0) :
    clearedEval ((X - 1) ^ r * Q) d R S = (R - S) ^ r * clearedEval Q (d - r) R S := by
  have hQd : Q.natDegree ≤ d - r := by
    by_cases hQ : Q = 0
    · subst hQ; simp
    · have hX1 : (X - 1 : ℤ[X]) = X - C 1 := by rw [map_one]
      have h1 : ((X - 1) ^ r * Q).natDegree = r + Q.natDegree := by
        rw [hX1, natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero 1)) hQ, natDegree_pow,
          natDegree_X_sub_C]
        ring
      omega
  have hSq : (S : ℚ) ≠ 0 := by exact_mod_cast hS
  apply Int.cast_injective (α := ℚ)
  rw [clearedEval_cast _ hd hS]
  push_cast
  rw [clearedEval_cast _ hQd hS, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_one, eval_mul, eval_pow, eval_sub, eval_X, eval_one]
  have : ((R : ℚ) / S - 1) = (R - S) / S := by field_simp
  rw [this, div_pow]
  have hSd : (S : ℚ) ^ d = (S : ℚ) ^ r * (S : ℚ) ^ (d - r) := by
    rw [← pow_add]; congr 1; omega
  rw [hSd]
  field_simp

theorem gap_pow_dvd_clearedEval {P : ℤ[X]} {r : ℕ} (hP : (X - 1) ^ r ∣ P) {d : ℕ}
    (hd : P.natDegree ≤ d) (hr : r ≤ d) {R S : ℤ} (hS : S ≠ 0) :
    (R - S) ^ r ∣ clearedEval P d R S := by
  obtain ⟨Q, rfl⟩ := hP
  rw [clearedEval_eq_of_dvd Q r hd hr hS]
  exact dvd_mul_right _ _

/-- A nonzero cleared value of a mask with contact `r` at `1` is at least `|R - S|^r` in
absolute value: contact cannot make the cleared integer small. -/
theorem abs_clearedEval_ge {P : ℤ[X]} {r : ℕ} (hP : (X - 1) ^ r ∣ P) {d : ℕ}
    (hd : P.natDegree ≤ d) (hr : r ≤ d) {R S : ℤ} (hS : S ≠ 0)
    (hne : clearedEval P d R S ≠ 0) :
    |R - S| ^ r ≤ |clearedEval P d R S| := by
  obtain ⟨c, hc⟩ := gap_pow_dvd_clearedEval hP hd hr hS
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc; exact hne hc
  rw [hc, abs_mul, abs_pow]
  have : 1 ≤ |c| := Int.one_le_abs hc0
  exact le_mul_of_one_le_right (pow_nonneg (abs_nonneg _) _) this

/-! ### Adjacent valuation transport -/

/-- Output valuation of the near-unit attached to the relation vector `(p, q)` at a prime with
valuations `m = v(M)`, `n = v(A)`. -/
def outputVal (p q m n : ℤ) : ℤ := q * n - p * m

/-- **Adjacent valuation transport.**  With `ε = p' q - p q'`,
`q' u - q u' = ε m` and `p' u - p u' = ε n`. -/
theorem transport_q (p q p' q' m n : ℤ) :
    q' * outputVal p q m n - q * outputVal p' q' m n = (p' * q - p * q') * m := by
  unfold outputVal; ring

theorem transport_p (p q p' q' m n : ℤ) :
    p' * outputVal p q m n - p * outputVal p' q' m n = (p' * q - p * q') * n := by
  unfold outputVal; ring

/-- Multiplicative form of the transport law in a commutative group: for
`z = A^q M^{-p}` and `z' = A^{q'} M^{-p'}`,
`z^{q'} z'^{-q} = M^{p' q - p q'}` and `z^{p'} z'^{-p} = A^{p' q - p q'}`. -/
theorem transport_zpow {G : Type*} [CommGroup G] (M A : G) (p q p' q' : ℤ) :
    (A ^ q * M ^ (-p)) ^ q' * (A ^ q' * M ^ (-p')) ^ (-q) = M ^ (p' * q - p * q') ∧
    (A ^ q * M ^ (-p)) ^ p' * (A ^ q' * M ^ (-p')) ^ (-p) = A ^ (p' * q - p * q') := by
  constructor
  · rw [mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul, mul_mul_mul_comm,
      ← zpow_add, ← zpow_add, show q * q' + q' * -q = 0 by ring, zpow_zero, one_mul]
    congr 1; ring
  · rw [mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul, mul_mul_mul_comm,
      ← zpow_add, ← zpow_add, show -p * p' + -p' * -p = 0 by ring, zpow_zero, mul_one]
    congr 1; ring

/-! ### Structural primes are not shared by independent reduced gaps -/

/-- If a prime power `π` divides the reduced gap `R - S` of a fraction in lowest terms, then it
divides neither `R` nor `S`. -/
theorem not_dvd_of_dvd_reduced_gap {π R S : ℤ} (hcop : IsCoprime R S) (hπ : ¬ IsUnit π)
    (h : π ∣ R - S) : ¬ π ∣ R ∧ ¬ π ∣ S := by
  constructor
  · intro hR
    have hS : π ∣ S := by
      have : S = R - (R - S) := by ring
      rw [this]; exact dvd_sub hR h
    exact hπ (hcop.isUnit_of_dvd' hR hS)
  · intro hS
    have hR : π ∣ R := by
      have : R = (R - S) + S := by ring
      rw [this]; exact dvd_add h hS
    exact hπ (hcop.isUnit_of_dvd' hR hS)

/-- Two relation vectors orthogonal to the same nonzero integer vector are linearly
dependent: `q n = p m` and `q' n = p' m` with `(m, n) ≠ 0` force `p' q - p q' = 0`. -/
theorem det_eq_zero_of_orthogonal {p q p' q' m n : ℤ} (hmn : (m, n) ≠ (0, 0))
    (h : outputVal p q m n = 0) (h' : outputVal p' q' m n = 0) : p' * q - p * q' = 0 := by
  unfold outputVal at h h'
  have e1 : (p' * q - p * q') * m = 0 := by linear_combination q' * h - q * h'
  have e2 : (p' * q - p * q') * n = 0 := by linear_combination p' * h - p * h'
  rcases mul_eq_zero.mp e1 with h1 | h1
  · exact h1
  · rcases mul_eq_zero.mp e2 with h2 | h2
    · exact h2
    · exact absurd (Prod.ext h1 h2) hmn

end LeanProofs.TwoBaseIntegerExponent.ExponentLatticeMask
