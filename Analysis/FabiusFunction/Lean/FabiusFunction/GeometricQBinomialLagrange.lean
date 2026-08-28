import FabiusFunction.FiniteQBinomialCore
import FabiusFunction.GeometricResidualMoments
import Mathlib.Algebra.BigOperators.Field

/-!
# Gaussian closed forms for geometric Lagrange weights

This module connects the denominator-free finite q-binomial algebra to the
geometric Lagrange rows used for finite Richardson extrapolation.  The key
polynomial identity is written in the reversed orientation appropriate for
the coefficients of

`prod j in range n, (z - q ^ (j + 1))`.

After evaluating that polynomial at the first `n + 1` geometric nodes, the
existing moment characterization of Lagrange weights identifies its
normalized coefficients with `geometricLagrangeWeight`.  Node injectivity is
the only field-level hypothesis: it implies that `(q;q)_n` is nonzero, so no
separate division assumption is exposed.

The final theorem evaluates every positive geometric moment, not just the
cancelled moments and the first surviving one:

`sum_k lambda_k (q^k)^d = (-1)^n q^(n(n+1)/2) [d-1 choose n]_q`.

All identities include `n = 0`.  They also retain every valid `q = 0` or
root-of-unity instance; such values are excluded only when they actually
make two of the prescribed nodes coincide.

## Main results

* `reversed_finite_qBinomial_theorem` is the division-free polynomial core.
* `sum_geometricQBinomialWeightNumerator_mul_pow` gives its normalized
  numerator moments over every commutative ring.
* `finiteQPochhammerIn_mul_geometricLagrangeWeight_eq` and
  `geometricLagrangeWeight_eq_gaussianBinomial_div` identify the Lagrange
  weights under the intrinsic distinct-node hypothesis.
* `sum_geometricLagrangeWeight_mul_pow_eq_gaussianBinomial` evaluates every
  positive residual moment.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Finset

/-- The denominator-free numerator of the evaluation-at-zero Lagrange
weight belonging to `q ^ k` among the nodes `1, q, ..., q ^ n`.

The definition retains the reversed Gaussian index because that orientation
follows directly from q-Pascal.  The division-free Gaussian symmetry theorem
gives a forward-index form on the natural row range, and zero extension makes
`geometricQBinomialWeightNumerator_eq_forward` valid at every index.  Thus no
artifact from truncated subtraction remains when `n < k`. -/
def geometricQBinomialWeightNumerator
    {R : Type*} [CommRing R] (q : R) (n k : ℕ) : R :=
  if k ≤ n then
    (-1 : R) ^ (n - k) * q ^ ((n - k + 1).choose 2) *
      gaussianBinomial q n (n - k)
  else 0

/-- On its natural row range, the numerator is the reversed Gaussian closed
form. -/
theorem geometricQBinomialWeightNumerator_eq_of_le
    {R : Type*} [CommRing R] (q : R) {n k : ℕ} (hk : k ≤ n) :
    geometricQBinomialWeightNumerator q n k =
      (-1 : R) ^ (n - k) * q ^ ((n - k + 1).choose 2) *
        gaussianBinomial q n (n - k) := by
  simp [geometricQBinomialWeightNumerator, hk]

/-- Standard forward-index form of the geometric Lagrange numerator.  It is
division-free and remains valid at zero, roots of unity, in positive
characteristic, and with zero divisors. -/
theorem geometricQBinomialWeightNumerator_eq_forward_of_le
    {R : Type*} [CommRing R] (q : R) {n k : ℕ} (hk : k ≤ n) :
    geometricQBinomialWeightNumerator q n k =
      (-1 : R) ^ (n - k) * q ^ ((n - k + 1).choose 2) *
        gaussianBinomial q n k := by
  rw [geometricQBinomialWeightNumerator_eq_of_le q hk,
    gaussianBinomial_symm q hk]

/-- **Global forward-index form of the geometric Lagrange numerator.**
Because both the numerator row and the Gaussian row vanish above the
diagonal, the standard closed form holds for all `n` and `k`, without an
admissibility hypothesis:

`w_(n,k) = (-1)^(n-k) q^((n-k+1 choose 2)) [n choose k]_q`.

The formula is division-free and remains valid at zero, roots of unity, in
positive characteristic, and with zero divisors. -/
theorem geometricQBinomialWeightNumerator_eq_forward
    {R : Type*} [CommRing R] (q : R) (n k : ℕ) :
    geometricQBinomialWeightNumerator q n k =
      (-1 : R) ^ (n - k) * q ^ ((n - k + 1).choose 2) *
        gaussianBinomial q n k := by
  by_cases hk : k ≤ n
  · exact geometricQBinomialWeightNumerator_eq_forward_of_le q hk
  · have hnk : n < k := Nat.lt_of_not_ge hk
    simp only [geometricQBinomialWeightNumerator, if_neg hk,
      gaussianBinomial_eq_zero_of_lt q hnk, mul_zero]

/-- Above its natural row range, the numerator vanishes. -/
@[simp] theorem geometricQBinomialWeightNumerator_eq_zero_of_lt
    {R : Type*} [CommRing R] (q : R) {n k : ℕ} (hk : n < k) :
    geometricQBinomialWeightNumerator q n k = 0 := by
  simp [geometricQBinomialWeightNumerator, show ¬ k ≤ n by omega]

private def reversedQBinomialSummand
    {R : Type*} [CommRing R] (q z : R) (n k : ℕ) : R :=
  (-1 : R) ^ k * q ^ ((k + 1).choose 2) *
    gaussianBinomial q n k * z ^ (n - k)

@[simp] private theorem reversedQBinomialSummand_zero
    {R : Type*} [CommRing R] (q z : R) (n : ℕ) :
    reversedQBinomialSummand q z n 0 = z ^ n := by
  simp [reversedQBinomialSummand]

private theorem reversedQBinomialSummand_above
    {R : Type*} [CommRing R] (q z : R) (n : ℕ) :
    reversedQBinomialSummand q z n (n + 1) = 0 := by
  rw [reversedQBinomialSummand,
    gaussianBinomial_eq_zero_of_lt q (Nat.lt_succ_self n)]
  ring

private theorem choose_succ_two_bridge (k : ℕ) :
    (k + 1).choose 2 = k.choose 2 + k := by
  simpa [Nat.add_comm] using Nat.choose_succ_succ k 1

private theorem reversedQBinomialSummand_succ_succ
    {R : Type*} [CommRing R] (q z : R)
    (n k : ℕ) (hk : k ≤ n) :
    reversedQBinomialSummand q z (n + 1) (k + 1) =
      z * reversedQBinomialSummand q z n (k + 1) -
        q ^ (n + 1) * reversedQBinomialSummand q z n k := by
  have hsub : n + 1 - (k + 1) = n - k := by omega
  have hchoose :
      (k + 1 + 1).choose 2 = (k + 1).choose 2 + (k + 1) :=
    choose_succ_two_bridge (k + 1)
  have hqpow : q ^ (k + 1) * q ^ (n - k) = q ^ (n + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hqtotal :
      q ^ ((k + 1 + 1).choose 2) * q ^ (n - k) =
        q ^ (n + 1) * q ^ ((k + 1).choose 2) := by
    rw [hchoose, pow_add]
    calc
      q ^ ((k + 1).choose 2) * q ^ (k + 1) * q ^ (n - k) =
          q ^ ((k + 1).choose 2) *
            (q ^ (k + 1) * q ^ (n - k)) := by ring
      _ = q ^ ((k + 1).choose 2) * q ^ (n + 1) := by rw [hqpow]
      _ = q ^ (n + 1) * q ^ ((k + 1).choose 2) := by ring
  have hfirst :
      z * reversedQBinomialSummand q z n (k + 1) =
        (-1 : R) ^ (k + 1) * q ^ ((k + 1 + 1).choose 2) *
          gaussianBinomial q n (k + 1) * z ^ (n - k) := by
    rcases Nat.lt_or_eq_of_le hk with hlt | heq
    · have hzexp : n - (k + 1) + 1 = n - k := by omega
      have hzpow : z * z ^ (n - (k + 1)) = z ^ (n - k) := by
        rw [← hzexp, pow_succ]
        ring
      rw [reversedQBinomialSummand]
      calc
        z *
              ((-1 : R) ^ (k + 1) * q ^ ((k + 1 + 1).choose 2) *
                gaussianBinomial q n (k + 1) * z ^ (n - (k + 1))) =
            (-1 : R) ^ (k + 1) * q ^ ((k + 1 + 1).choose 2) *
              gaussianBinomial q n (k + 1) *
                (z * z ^ (n - (k + 1))) := by ring
        _ = (-1 : R) ^ (k + 1) * q ^ ((k + 1 + 1).choose 2) *
              gaussianBinomial q n (k + 1) * z ^ (n - k) := by
          rw [hzpow]
    · rw [reversedQBinomialSummand,
        gaussianBinomial_eq_zero_of_lt q (by omega : n < k + 1)]
      ring
  have hsecond :
      (-1 : R) ^ (k + 1) * q ^ ((k + 1 + 1).choose 2) *
          (q ^ (n - k) * gaussianBinomial q n k) * z ^ (n - k) =
        -(q ^ (n + 1) * reversedQBinomialSummand q z n k) := by
    calc
      (-1 : R) ^ (k + 1) * q ^ ((k + 1 + 1).choose 2) *
            (q ^ (n - k) * gaussianBinomial q n k) * z ^ (n - k) =
          (-1 : R) ^ (k + 1) *
            (q ^ ((k + 1 + 1).choose 2) * q ^ (n - k)) *
              gaussianBinomial q n k * z ^ (n - k) := by ring
      _ = (-1 : R) ^ (k + 1) *
            (q ^ (n + 1) * q ^ ((k + 1).choose 2)) *
              gaussianBinomial q n k * z ^ (n - k) := by rw [hqtotal]
      _ = -(q ^ (n + 1) * reversedQBinomialSummand q z n k) := by
        rw [reversedQBinomialSummand, pow_succ]
        ring
  calc
    reversedQBinomialSummand q z (n + 1) (k + 1) =
        (-1 : R) ^ (k + 1) * q ^ ((k + 1 + 1).choose 2) *
          (gaussianBinomial q n (k + 1) +
            q ^ (n - k) * gaussianBinomial q n k) * z ^ (n - k) := by
      rw [reversedQBinomialSummand, gaussianBinomial_succ_succ, hsub]
    _ =
        ((-1 : R) ^ (k + 1) * q ^ ((k + 1 + 1).choose 2) *
          gaussianBinomial q n (k + 1) * z ^ (n - k)) +
        ((-1 : R) ^ (k + 1) * q ^ ((k + 1 + 1).choose 2) *
          (q ^ (n - k) * gaussianBinomial q n k) * z ^ (n - k)) := by
      ring
    _ = z * reversedQBinomialSummand q z n (k + 1) -
        q ^ (n + 1) * reversedQBinomialSummand q z n k := by
      rw [← hfirst, hsecond]
      ring

private theorem reversed_finite_qBinomial_theorem_aux
    {R : Type*} [CommRing R] (q z : R) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      reversedQBinomialSummand q z n k) =
      ∏ j ∈ Finset.range n, (z - q ^ (j + 1)) := by
  induction n with
  | zero => simp [reversedQBinomialSummand]
  | succ n ih =>
      have hrec :
          (∑ k ∈ Finset.range (n + 1),
              reversedQBinomialSummand q z (n + 1) (k + 1)) =
            ∑ k ∈ Finset.range (n + 1),
              (z * reversedQBinomialSummand q z n (k + 1) -
                q ^ (n + 1) * reversedQBinomialSummand q z n k) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact reversedQBinomialSummand_succ_succ q z n k
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
      have htail :
          z ^ n + (∑ k ∈ Finset.range (n + 1),
              reversedQBinomialSummand q z n (k + 1)) =
            ∑ k ∈ Finset.range (n + 1),
              reversedQBinomialSummand q z n k := by
        calc
          z ^ n + (∑ k ∈ Finset.range (n + 1),
              reversedQBinomialSummand q z n (k + 1)) =
              ∑ k ∈ Finset.range (n + 2),
                reversedQBinomialSummand q z n k := by
            have hs := (Finset.sum_range_succ'
              (fun k => reversedQBinomialSummand q z n k) (n + 1)).symm
            rw [show n + 1 + 1 = n + 2 by omega] at hs
            simpa [add_comm] using hs
          _ = (∑ k ∈ Finset.range (n + 1),
                reversedQBinomialSummand q z n k) +
              reversedQBinomialSummand q z n (n + 1) := by
            exact Finset.sum_range_succ _ _
          _ = _ := by
            rw [reversedQBinomialSummand_above, add_zero]
      rw [show n + 1 + 1 = n + 2 by omega, Finset.sum_range_succ']
      rw [reversedQBinomialSummand_zero, hrec, Finset.sum_sub_distrib]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      calc
        (z * (∑ k ∈ Finset.range (n + 1),
                  reversedQBinomialSummand q z n (k + 1)) -
                q ^ (n + 1) * (∑ k ∈ Finset.range (n + 1),
                  reversedQBinomialSummand q z n k)) + z ^ (n + 1) =
            z * (z ^ n + ∑ k ∈ Finset.range (n + 1),
                reversedQBinomialSummand q z n (k + 1)) -
              q ^ (n + 1) * (∑ k ∈ Finset.range (n + 1),
                reversedQBinomialSummand q z n k) := by
          rw [pow_succ]
          ring
        _ = z * (∑ k ∈ Finset.range (n + 1),
                reversedQBinomialSummand q z n k) -
              q ^ (n + 1) * (∑ k ∈ Finset.range (n + 1),
                reversedQBinomialSummand q z n k) := by
          rw [htail]
        _ = (z - q ^ (n + 1)) *
              (∑ k ∈ Finset.range (n + 1),
                reversedQBinomialSummand q z n k) := by ring
        _ = (z - q ^ (n + 1)) *
              (∏ j ∈ Finset.range n, (z - q ^ (j + 1))) := by rw [ih]
        _ = ∏ j ∈ Finset.range (n + 1), (z - q ^ (j + 1)) := by
          rw [Finset.prod_range_succ]
          ring

/-- **Reversed finite q-binomial polynomial identity.**  These are exactly
the denominator-free numerators of the geometric Lagrange row.  The theorem
is valid over every commutative ring, without division and for every `q`. -/
theorem reversed_finite_qBinomial_theorem
    {R : Type*} [CommRing R] (q z : R) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      geometricQBinomialWeightNumerator q n k * z ^ k) =
      ∏ j ∈ Finset.range n, (z - q ^ (j + 1)) := by
  have hreflect := Finset.sum_range_reflect
    (fun k => reversedQBinomialSummand q z n k) (n + 1)
  calc
    (∑ k ∈ Finset.range (n + 1),
        geometricQBinomialWeightNumerator q n k * z ^ k) =
        ∑ k ∈ Finset.range (n + 1),
          reversedQBinomialSummand q z n (n - k) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      simp only [geometricQBinomialWeightNumerator_eq_of_le q hkn,
        reversedQBinomialSummand, Nat.sub_sub_self hkn]
    _ = ∑ k ∈ Finset.range (n + 1),
          reversedQBinomialSummand q z n k := by
      simpa only [Nat.add_sub_cancel] using hreflect
    _ = ∏ j ∈ Finset.range n, (z - q ^ (j + 1)) :=
      reversed_finite_qBinomial_theorem_aux q z n

/-- The numerator row has the normalized Lagrange moments before division
by `(q;q)_n`: degree zero gives `(q;q)_n`, while every positive degree at
most `n` gives zero. -/
theorem sum_geometricQBinomialWeightNumerator_mul_pow
    {R : Type*} [CommRing R] (q : R) (n d : ℕ) (hd : d ≤ n) :
    (∑ k ∈ Finset.range (n + 1),
      geometricQBinomialWeightNumerator q n k * (q ^ k) ^ d) =
      finiteQPochhammerIn q q n * (0 : R) ^ d := by
  calc
    (∑ k ∈ Finset.range (n + 1),
        geometricQBinomialWeightNumerator q n k * (q ^ k) ^ d) =
        ∑ k ∈ Finset.range (n + 1),
          geometricQBinomialWeightNumerator q n k * (q ^ d) ^ k := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ = ∏ j ∈ Finset.range n, (q ^ d - q ^ (j + 1)) :=
      reversed_finite_qBinomial_theorem q (q ^ d) n
    _ = finiteQPochhammerIn q q n * (0 : R) ^ d := by
      cases d with
      | zero =>
          simp only [pow_zero, mul_one, finiteQPochhammerIn]
          apply Finset.prod_congr rfl
          intro j _hj
          rw [pow_succ']
      | succ d =>
          have hdn : d < n := Nat.succ_le_iff.mp hd
          have hzero :
              (∏ j ∈ Finset.range n,
                (q ^ (d + 1) - q ^ (j + 1))) = 0 := by
            refine Finset.prod_eq_zero (Finset.mem_range.mpr hdn) ?_
            rw [sub_self]
          rw [hzero, zero_pow (Nat.succ_ne_zero d), mul_zero]

/-- Injectivity of `1, q, ..., q^n` implies nonvanishing of `(q;q)_n`.
This includes the empty product at `n = 0`; no independent hypothesis such
as `q != 0` or `q` not being a root of unity is needed. -/
theorem finiteQPochhammerIn_self_ne_zero_of_injOn
    {F : Type*} [Field F] (q : F) (n : ℕ)
    (hnode : Set.InjOn (fun k : ℕ => q ^ k) (Finset.range (n + 1))) :
    finiteQPochhammerIn q q n ≠ 0 := by
  rw [finiteQPochhammerIn, Finset.prod_ne_zero_iff]
  intro j hj
  have hjn : j < n := Finset.mem_range.mp hj
  have hpow : q ^ (j + 1) ≠ 1 := by
    intro h
    have heq : 0 = j + 1 := hnode
      (Finset.mem_range.mpr (by omega))
      (Finset.mem_range.mpr (by omega)) (by simp [h])
    omega
  rw [show q * q ^ j = q ^ (j + 1) by rw [pow_succ']]
  exact sub_ne_zero.mpr hpow.symm

/-- Quotient form of the Gaussian closed formula for a geometric Lagrange
weight.  Its denominator is nonzero by node injectivity. -/
theorem geometricLagrangeWeight_eq_gaussianBinomial_div
    {F : Type*} [Field F] (q : F) (n k : ℕ)
    (hnode : Set.InjOn (fun j : ℕ => q ^ j) (Finset.range (n + 1)))
    (hk : k ≤ n) :
    geometricLagrangeWeight q n k =
      geometricQBinomialWeightNumerator q n k /
        finiteQPochhammerIn q q n := by
  let weight : ℕ → F := fun j =>
    geometricQBinomialWeightNumerator q n j /
      finiteQPochhammerIn q q n
  have hden := finiteQPochhammerIn_self_ne_zero_of_injOn q n hnode
  have hmoment : ∀ d < (Finset.range (n + 1)).card,
      ∑ j ∈ Finset.range (n + 1), weight j * (q ^ j) ^ d =
        (0 : F) ^ d := by
    intro d hd
    have hdn : d ≤ n := by
      simpa only [Finset.card_range, Nat.lt_succ_iff] using hd
    calc
      (∑ j ∈ Finset.range (n + 1), weight j * (q ^ j) ^ d) =
          (∑ j ∈ Finset.range (n + 1),
            geometricQBinomialWeightNumerator q n j * (q ^ j) ^ d) /
              finiteQPochhammerIn q q n := by
        simp only [weight, div_mul_eq_mul_div]
        rw [Finset.sum_div]
      _ = (finiteQPochhammerIn q q n * (0 : F) ^ d) /
            finiteQPochhammerIn q q n := by
        rw [sum_geometricQBinomialWeightNumerator_mul_pow q n d hdn]
      _ = (0 : F) ^ d := mul_div_cancel_left₀ _ hden
  have hweight := eq_lagrangeEvalWeight_of_moments
    (Finset.range (n + 1)) (fun j : ℕ => q ^ j) 0 hnode weight hmoment
    (i := k) (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk))
  simpa only [weight, geometricLagrangeWeight] using hweight.symm

/-- **Division-free pointwise Gaussian/Lagrange bridge.**  Multiplication
by `(q;q)_n` clears the normalized Lagrange denominator.  The theorem has no
division or nonvanishing hypothesis beyond the intrinsic distinct-node
condition. -/
theorem finiteQPochhammerIn_mul_geometricLagrangeWeight_eq
    {F : Type*} [Field F] (q : F) (n k : ℕ)
    (hnode : Set.InjOn (fun j : ℕ => q ^ j) (Finset.range (n + 1)))
    (hk : k ≤ n) :
    finiteQPochhammerIn q q n * geometricLagrangeWeight q n k =
      geometricQBinomialWeightNumerator q n k := by
  have hden := finiteQPochhammerIn_self_ne_zero_of_injOn q n hnode
  have hquot := geometricLagrangeWeight_eq_gaussianBinomial_div
    q n k hnode hk
  rw [hquot]
  exact mul_div_cancel₀ _ hden

/-- **Complete residual moments of the geometric Richardson row.**  For
every positive degree, including degrees above the cancellation range, the
moment is one Gaussian coefficient.  At `d <= n` this specializes to zero;
at `d = n + 1` it specializes to the first-surviving-moment theorem.

Degree zero is intentionally handled by `sum_geometricLagrangeWeight`: the
formula here contains `d - 1` and therefore has a genuinely different
boundary value at zero. -/
theorem sum_geometricLagrangeWeight_mul_pow_eq_gaussianBinomial
    {F : Type*} [Field F] (q : F) (n d : ℕ)
    (hnode : Set.InjOn (fun k : ℕ => q ^ k) (Finset.range (n + 1)))
    (hd : 0 < d) :
    (∑ k ∈ Finset.range (n + 1),
      geometricLagrangeWeight q n k * (q ^ k) ^ d) =
      (-1 : F) ^ n * q ^ (n * (n + 1) / 2) *
        gaussianBinomial q (d - 1) n := by
  simpa [Nat.choose_two_right, Nat.mul_comm] using
    sum_geometricLagrangeWeight_mul_pow_of_pos q n d hnode hd

end Fabius
