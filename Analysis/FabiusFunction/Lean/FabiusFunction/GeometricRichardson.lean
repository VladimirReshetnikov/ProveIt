import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Finite geometric-root and Richardson polynomials

This module isolates the elementary polynomial algebra common to geometric
finite differences.  For a commutative ring `R`, a base `q : R`, and a
length `n`, the raw polynomial

`geometricRootPolynomial q n = ∏ r < n, (1 - q^(r+1) X)`

has constant coefficient one and annihilates every `x` for which one of the
factor equations `q^(r+1) * x = 1` holds.  Over a field we normalize by the
value at one.  The resulting polynomial has mass one whenever that value is
nonzero, while retaining the inverse-geometric roots.

The second orientation used by Richardson extrapolation is exposed explicitly
as `forwardGeometricRichardsonPolynomial q n`: it is the normalized polynomial
with base `q⁻¹`, so its roots are the forward geometric nodes
`q, q², ..., qⁿ`.  The duality theorem
`geometricRootPolynomial_inv_eval_nextPower` identifies its first value beyond
those roots with the value at one of the original-base polynomial.  Thus the
same algebra covers both the inverse-node Toeplitz rows at `q = 1/2` and the
forward-node Richardson filters at `q = 1/4`.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

open Polynomial

section Raw

variable {R : Type*} [CommRing R]

/-- The finite geometric-root polynomial
`∏ r < n, (1 - q^(r+1) X)` over a commutative ring. -/
noncomputable def geometricRootPolynomial (q : R) (n : ℕ) : Polynomial R :=
  ∏ r ∈ Finset.range n,
    (1 - Polynomial.C (q ^ (r + 1)) * Polynomial.X)

/-- The empty geometric-root polynomial is one. -/
@[simp] theorem geometricRootPolynomial_zero (q : R) :
    geometricRootPolynomial q 0 = 1 := by
  simp [geometricRootPolynomial]

/-- Appending the last geometric factor gives the product recurrence. -/
theorem geometricRootPolynomial_succ (q : R) (n : ℕ) :
    geometricRootPolynomial q (n + 1) =
      geometricRootPolynomial q n *
        (1 - Polynomial.C (q ^ (n + 1)) * Polynomial.X) := by
  simp [geometricRootPolynomial, Finset.prod_range_succ]

/-- Evaluation turns the polynomial into its defining finite scalar product. -/
@[simp] theorem geometricRootPolynomial_eval (q x : R) (n : ℕ) :
    (geometricRootPolynomial q n).eval x =
      ∏ r ∈ Finset.range n, (1 - q ^ (r + 1) * x) := by
  simp [geometricRootPolynomial]

/-- The value at one is the finite geometric Pochhammer product
`∏ r < n, (1 - q^(r+1))`. -/
@[simp] theorem geometricRootPolynomial_eval_one (q : R) (n : ℕ) :
    (geometricRootPolynomial q n).eval 1 =
      ∏ r ∈ Finset.range n, (1 - q ^ (r + 1)) := by
  simp

/-- Every geometric-root polynomial has constant coefficient one. -/
@[simp] theorem geometricRootPolynomial_coeff_zero (q : R) (n : ℕ) :
    (geometricRootPolynomial q n).coeff 0 = 1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp

/-- Geometric-root polynomials commute with change of coefficients. -/
@[simp] theorem geometricRootPolynomial_map
    {S : Type*} [CommRing S] (f : R →+* S) (q : R) (n : ℕ) :
    (geometricRootPolynomial q n).map f =
      geometricRootPolynomial (f q) n := by
  simp [geometricRootPolynomial, Polynomial.map_prod]

/-- If one defining factor vanishes at `x`, then the whole raw polynomial
vanishes at `x`.  This ring-general form needs neither division nor a domain
hypothesis. -/
theorem geometricRootPolynomial_eval_eq_zero_of_mul_eq_one
    (q : R) {n r : ℕ} {x : R} (hr : r < n)
    (hx : q ^ (r + 1) * x = 1) :
    (geometricRootPolynomial q n).eval x = 0 := by
  rw [geometricRootPolynomial_eval]
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hr)
  simp [hx]

/-- Root-facing form of
`geometricRootPolynomial_eval_eq_zero_of_mul_eq_one`. -/
theorem geometricRootPolynomial_isRoot_of_mul_eq_one
    (q : R) {n r : ℕ} {x : R} (hr : r < n)
    (hx : q ^ (r + 1) * x = 1) :
    (geometricRootPolynomial q n).IsRoot x := by
  exact geometricRootPolynomial_eval_eq_zero_of_mul_eq_one q hr hx

/-- The product of the signed geometric powers has the closed triangular
exponent `C(n+1, 2)`. -/
theorem prod_neg_geometric_powers (q : R) (n : ℕ) :
    (∏ r ∈ Finset.range n, (-(q ^ (r + 1)))) =
      (-1 : R) ^ n * q ^ (n + 1).choose 2 := by
  have hsum :
      (∑ r ∈ Finset.range n, (r + 1)) = (n + 1).choose 2 := by
    calc
      (∑ r ∈ Finset.range n, (r + 1)) =
          (∑ r ∈ Finset.range n, r) + n := by
            simp [Finset.sum_add_distrib]
      _ = n.choose 2 + n := by
        rw [Finset.sum_range_id, Nat.choose_two_right]
      _ = (n + 1).choose 2 := by
        rw [show n + 1 = n.succ by omega, show 2 = 1 + 1 by omega,
          Nat.choose_succ_succ]
        simp [Nat.choose_one_right, add_comm]
  calc
    (∏ r ∈ Finset.range n, (-(q ^ (r + 1)))) =
        ∏ r ∈ Finset.range n, ((-1 : R) * q ^ (r + 1)) := by
          apply Finset.prod_congr rfl
          intro r _hr
          ring
    _ = (∏ _r ∈ Finset.range n, (-1 : R)) *
          ∏ r ∈ Finset.range n, q ^ (r + 1) := by
            rw [Finset.prod_mul_distrib]
    _ = (-1 : R) ^ n * q ^ (∑ r ∈ Finset.range n, (r + 1)) := by
      rw [Finset.prod_const, Finset.card_range,
        Finset.prod_pow_eq_pow_sum]
    _ = (-1 : R) ^ n * q ^ (n + 1).choose 2 := by rw [hsum]

variable [NoZeroDivisors R]

private theorem geometricRootFactor_natDegree
    (q : R) (hq : q ≠ 0) (r : ℕ) :
    (1 - Polynomial.C (q ^ (r + 1)) * Polynomial.X : Polynomial R).natDegree = 1 := by
  rw [Polynomial.natDegree_eq_one]
  refine ⟨-(q ^ (r + 1)), neg_ne_zero.mpr (pow_ne_zero _ hq), 1, ?_⟩
  simp only [map_neg, Polynomial.C_1]
  ring

private theorem geometricRootFactor_leadingCoeff
    (q : R) (hq : q ≠ 0) (r : ℕ) :
    (1 - Polynomial.C (q ^ (r + 1)) * Polynomial.X : Polynomial R).leadingCoeff =
      -(q ^ (r + 1)) := by
  rw [← Polynomial.coeff_natDegree,
    geometricRootFactor_natDegree q hq r]
  simp [Polynomial.coeff_one]

/-- Over a domain, a nonzero base gives the raw polynomial its expected
degree `n`. -/
theorem geometricRootPolynomial_natDegree (q : R) (hq : q ≠ 0) (n : ℕ) :
    (geometricRootPolynomial q n).natDegree = n := by
  rw [geometricRootPolynomial, Polynomial.natDegree_prod]
  · simp_rw [geometricRootFactor_natDegree q hq]
    simp
  · intro r _hr hzero
    have hdegree := geometricRootFactor_natDegree q hq r
    rw [hzero] at hdegree
    simp at hdegree

/-- Over a domain, the leading coefficient is the product of the leading
coefficients `-q^(r+1)` of the geometric factors. -/
theorem geometricRootPolynomial_leadingCoeff (q : R) (hq : q ≠ 0) (n : ℕ) :
    (geometricRootPolynomial q n).leadingCoeff =
      ∏ r ∈ Finset.range n, (-(q ^ (r + 1))) := by
  rw [geometricRootPolynomial, Polynomial.leadingCoeff_prod]
  apply Finset.prod_congr rfl
  intro r _hr
  exact geometricRootFactor_leadingCoeff q hq r

/-- Closed leading-coefficient formula with triangular exponent
`C(n+1, 2)`. -/
theorem geometricRootPolynomial_leadingCoeff_closedForm
    (q : R) (hq : q ≠ 0) (n : ℕ) :
    (geometricRootPolynomial q n).leadingCoeff =
      (-1 : R) ^ n * q ^ (n + 1).choose 2 := by
  rw [geometricRootPolynomial_leadingCoeff q hq n,
    prod_neg_geometric_powers q n]

end Raw

section Normalized

variable {K : Type*} [Field K]

/-- The normalizing value is nonzero exactly when none of the finite
geometric factors vanishes at one. -/
theorem geometricRootPolynomial_eval_one_ne_zero_iff
    (q : K) (n : ℕ) :
    (geometricRootPolynomial q n).eval 1 ≠ 0 ↔
      ∀ r < n, q ^ (r + 1) ≠ 1 := by
  rw [geometricRootPolynomial_eval_one, Finset.prod_ne_zero_iff]
  constructor
  · intro h r hr hpow
    exact h r (Finset.mem_range.mpr hr) (by simp [hpow])
  · intro h r hr
    exact sub_ne_zero.mpr (Ne.symm (h r (Finset.mem_range.mp hr)))

/-- The geometric-root polynomial normalized by its value at one.  The
definition is total; the mass-one theorem asks exactly that the denominator
be nonzero. -/
noncomputable def normalizedGeometricRootPolynomial (q : K) (n : ℕ) :
    Polynomial K :=
  geometricRootPolynomial q n *
    Polynomial.C ((geometricRootPolynomial q n).eval 1)⁻¹

/-- Evaluation of the normalized polynomial is the quotient of the two raw
evaluations. -/
@[simp] theorem normalizedGeometricRootPolynomial_eval
    (q x : K) (n : ℕ) :
    (normalizedGeometricRootPolynomial q n).eval x =
      (geometricRootPolynomial q n).eval x /
        (geometricRootPolynomial q n).eval 1 := by
  simp [normalizedGeometricRootPolynomial, div_eq_mul_inv]

/-- The normalized polynomial has mass one whenever its normalizing value is
nonzero. -/
theorem normalizedGeometricRootPolynomial_eval_one
    (q : K) (n : ℕ)
    (hden : (geometricRootPolynomial q n).eval 1 ≠ 0) :
    (normalizedGeometricRootPolynomial q n).eval 1 = 1 := by
  rw [normalizedGeometricRootPolynomial_eval]
  exact div_self hden

/-- The constant coefficient of the normalized polynomial is the reciprocal
of its normalizing value. -/
@[simp] theorem normalizedGeometricRootPolynomial_coeff_zero
    (q : K) (n : ℕ) :
    (normalizedGeometricRootPolynomial q n).coeff 0 =
      ((geometricRootPolynomial q n).eval 1)⁻¹ := by
  rw [Polynomial.coeff_zero_eq_eval_zero,
    normalizedGeometricRootPolynomial_eval]
  simp [div_eq_mul_inv]

/-- Normalization preserves the expected degree when both the base and the
normalizing value are nonzero. -/
theorem normalizedGeometricRootPolynomial_natDegree
    (q : K) (hq : q ≠ 0) (n : ℕ)
    (hden : (geometricRootPolynomial q n).eval 1 ≠ 0) :
    (normalizedGeometricRootPolynomial q n).natDegree = n := by
  rw [normalizedGeometricRootPolynomial,
    Polynomial.natDegree_mul_C (inv_ne_zero hden),
    geometricRootPolynomial_natDegree q hq]

/-- A vanishing raw factor remains a root after normalization.  No
nonvanishing assumption on the normalizer is needed for this implication. -/
theorem normalizedGeometricRootPolynomial_eval_eq_zero_of_mul_eq_one
    (q : K) {n r : ℕ} {x : K} (hr : r < n)
    (hx : q ^ (r + 1) * x = 1) :
    (normalizedGeometricRootPolynomial q n).eval x = 0 := by
  rw [normalizedGeometricRootPolynomial_eval,
    geometricRootPolynomial_eval_eq_zero_of_mul_eq_one q hr hx]
  exact zero_div _

/-- For a nonzero base, the inverse geometric nodes `q^(-(r+1))` are roots
of the normalized polynomial. -/
theorem normalizedGeometricRootPolynomial_eval_inv_pow_eq_zero
    (q : K) (hq : q ≠ 0) {n r : ℕ} (hr : r < n) :
    (normalizedGeometricRootPolynomial q n).eval
        ((q ^ (r + 1))⁻¹) = 0 := by
  apply normalizedGeometricRootPolynomial_eval_eq_zero_of_mul_eq_one q hr
  exact mul_inv_cancel₀ (pow_ne_zero _ hq)

/-- The forward-node Richardson orientation.  Reversing the base makes its
roots `q, q², ..., qⁿ`, instead of their inverses. -/
noncomputable def forwardGeometricRichardsonPolynomial (q : K) (n : ℕ) :
    Polynomial K :=
  normalizedGeometricRootPolynomial q⁻¹ n

/-- Evaluation of the forward-node Richardson polynomial in raw quotient
form. -/
@[simp] theorem forwardGeometricRichardsonPolynomial_eval
    (q x : K) (n : ℕ) :
    (forwardGeometricRichardsonPolynomial q n).eval x =
      (geometricRootPolynomial q⁻¹ n).eval x /
        (geometricRootPolynomial q⁻¹ n).eval 1 := by
  simp [forwardGeometricRichardsonPolynomial]

/-- The forward-node Richardson polynomial has mass one under the exact
nonvanishing condition on its normalizer. -/
theorem forwardGeometricRichardsonPolynomial_eval_one
    (q : K) (n : ℕ)
    (hden : (geometricRootPolynomial q⁻¹ n).eval 1 ≠ 0) :
    (forwardGeometricRichardsonPolynomial q n).eval 1 = 1 := by
  exact normalizedGeometricRootPolynomial_eval_one q⁻¹ n hden

/-- For a nonzero base, every forward node `q^(r+1)` with `r < n` is a root
of the Richardson polynomial. -/
theorem forwardGeometricRichardsonPolynomial_eval_pow_eq_zero
    (q : K) (hq : q ≠ 0) {n r : ℕ} (hr : r < n) :
    (forwardGeometricRichardsonPolynomial q n).eval (q ^ (r + 1)) = 0 := by
  rw [forwardGeometricRichardsonPolynomial]
  apply normalizedGeometricRootPolynomial_eval_eq_zero_of_mul_eq_one q⁻¹ hr
  rw [inv_pow]
  exact inv_mul_cancel₀ (pow_ne_zero _ hq)

/-- Inverse-base duality at the first geometric node beyond the roots:
evaluating the raw `q⁻¹` polynomial at `q^(n+1)` gives the value at one of
the raw `q` polynomial. -/
theorem geometricRootPolynomial_inv_eval_nextPower
    (q : K) (hq : q ≠ 0) (n : ℕ) :
    (geometricRootPolynomial q⁻¹ n).eval (q ^ (n + 1)) =
      (geometricRootPolynomial q n).eval 1 := by
  rw [geometricRootPolynomial_eval, geometricRootPolynomial_eval_one]
  calc
    (∏ r ∈ Finset.range n,
        (1 - (q⁻¹) ^ (r + 1) * q ^ (n + 1))) =
        ∏ r ∈ Finset.range n, (1 - q ^ (n - r)) := by
          apply Finset.prod_congr rfl
          intro r hr
          have hrn : r < n := Finset.mem_range.mp hr
          apply congrArg (fun y => 1 - y)
          calc
            (q⁻¹) ^ (r + 1) * q ^ (n + 1) =
                (q ^ (r + 1))⁻¹ * q ^ (n + 1) := by rw [inv_pow]
            _ = (q ^ (r + 1))⁻¹ *
                (q ^ (r + 1) * q ^ (n - r)) := by
                  congr 1
                  rw [← pow_add]
                  congr 1
                  omega
            _ = q ^ (n - r) := by
                  rw [inv_mul_cancel_left₀ (pow_ne_zero _ hq)]
    _ = ∏ r ∈ Finset.range n, (1 - q ^ (r + 1)) := by
      calc
        (∏ r ∈ Finset.range n, (1 - q ^ (n - r))) =
            ∏ r ∈ Finset.range n,
              (1 - q ^ (n - 1 - r + 1)) := by
                apply Finset.prod_congr rfl
                intro r hr
                have hrn : r < n := Finset.mem_range.mp hr
                rw [show n - r = n - 1 - r + 1 by omega]
        _ = ∏ r ∈ Finset.range n, (1 - q ^ (r + 1)) :=
          Finset.prod_range_reflect (fun r => 1 - q ^ (r + 1)) n

/-- Multiplying the inverse-base normalizer by the signed leading product
recovers the original-base normalizer. -/
theorem geometricRootPolynomial_inv_eval_one_mul_signedPowers
    (q : K) (hq : q ≠ 0) (n : ℕ) :
    (geometricRootPolynomial q⁻¹ n).eval 1 *
        (∏ r ∈ Finset.range n, (-(q ^ (r + 1)))) =
      (geometricRootPolynomial q n).eval 1 := by
  rw [geometricRootPolynomial_eval_one, geometricRootPolynomial_eval_one,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro r _hr
  rw [inv_pow]
  field_simp [pow_ne_zero _ hq]
  <;> ring

/-- The first evaluation beyond the forward Richardson roots is the quotient
of the original- and inverse-base normalizing products. -/
theorem forwardGeometricRichardsonPolynomial_eval_nextPower
    (q : K) (hq : q ≠ 0) (n : ℕ) :
    (forwardGeometricRichardsonPolynomial q n).eval (q ^ (n + 1)) =
      (geometricRootPolynomial q n).eval 1 /
        (geometricRootPolynomial q⁻¹ n).eval 1 := by
  rw [forwardGeometricRichardsonPolynomial_eval,
    geometricRootPolynomial_inv_eval_nextPower q hq n]

/-- Closed first-uncancelled Richardson value.  After the roots
`q, ..., qⁿ`, the next node `q^(n+1)` has the exact value
`(-1)^n q^C(n+1,2)`. -/
theorem forwardGeometricRichardsonPolynomial_eval_nextPower_closedForm
    (q : K) (hq : q ≠ 0) (n : ℕ)
    (hden : (geometricRootPolynomial q⁻¹ n).eval 1 ≠ 0) :
    (forwardGeometricRichardsonPolynomial q n).eval (q ^ (n + 1)) =
      (-1 : K) ^ n * q ^ (n + 1).choose 2 := by
  rw [forwardGeometricRichardsonPolynomial_eval_nextPower q hq n,
    ← prod_neg_geometric_powers q n]
  apply (div_eq_iff hden).2
  simpa [mul_comm] using
    (geometricRootPolynomial_inv_eval_one_mul_signedPowers q hq n).symm

/-- Under a nonzero base and the exact normalizer hypothesis, the next
geometric node is genuinely the first uncancelled one. -/
theorem forwardGeometricRichardsonPolynomial_eval_nextPower_ne_zero
    (q : K) (hq : q ≠ 0) (n : ℕ)
    (hden : (geometricRootPolynomial q⁻¹ n).eval 1 ≠ 0) :
    (forwardGeometricRichardsonPolynomial q n).eval (q ^ (n + 1)) ≠ 0 := by
  rw [forwardGeometricRichardsonPolynomial_eval_nextPower_closedForm q hq n hden]
  exact mul_ne_zero
    (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (pow_ne_zero _ hq)

end Normalized

end Fabius
