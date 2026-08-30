import FabiusFunction.FiniteQBinomialCore

/-!
# The finite q-Cauchy convolution

This module proves the finite q-Cauchy identity for the denominator-free
Gaussian coefficient and finite q-Pochhammer product of
`FiniteQBinomialCore`:

`(u * v; q)_n = sum_{k=0}^n [n choose k]_q (u; q)_k v^k (v; q)_(n-k)`.

The proof is finite algebra over an arbitrary commutative ring.  It uses the
zero-extended q-Pascal recurrence and the last-factor recurrence for finite
q-Pochhammer products, so it needs no division, cancellation, nonvanishing,
topology, or convergence hypothesis.  In particular, the identity remains
valid at roots of unity, in positive characteristic, and in rings with zero
divisors.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Finset

/-- The summand in the finite q-Cauchy convolution. -/
private def qCauchySummand
    {R : Type*} [CommRing R]
    (q u v : R) (n k : ℕ) : R :=
  gaussianBinomial q n k * finiteQPochhammerIn u q k *
    v ^ k * finiteQPochhammerIn v q (n - k)

/-- The part of the next q-Cauchy row retaining the lower index `k`. -/
private def qCauchyLeft
    {R : Type*} [CommRing R]
    (q u v : R) (n k : ℕ) : R :=
  gaussianBinomial q n k * finiteQPochhammerIn u q k *
    v ^ k * finiteQPochhammerIn v q (n + 1 - k)

/-- The part of the next q-Cauchy row shifted from lower index `k` to
`k + 1`. -/
private def qCauchyRight
    {R : Type*} [CommRing R]
    (q u v : R) (n k : ℕ) : R :=
  q ^ (n - k) * gaussianBinomial q n k *
    finiteQPochhammerIn u q (k + 1) * v ^ (k + 1) *
      finiteQPochhammerIn v q (n - k)

private theorem qCauchySummand_succ_succ
    {R : Type*} [CommRing R]
    (q u v : R) (n k : ℕ) :
    qCauchySummand q u v (n + 1) (k + 1) =
      qCauchyLeft q u v n (k + 1) +
        qCauchyRight q u v n k := by
  have hsub : n + 1 - (k + 1) = n - k := by omega
  unfold qCauchySummand qCauchyLeft qCauchyRight
  rw [hsub, gaussianBinomial_succ_succ]
  ring

private theorem qCauchySummand_succ_zero
    {R : Type*} [CommRing R]
    (q u v : R) (n : ℕ) :
    qCauchySummand q u v (n + 1) 0 =
      qCauchyLeft q u v n 0 := by
  simp [qCauchySummand, qCauchyLeft]

private theorem qCauchyLeft_last
    {R : Type*} [CommRing R]
    (q u v : R) (n : ℕ) :
    qCauchyLeft q u v n (n + 1) = 0 := by
  unfold qCauchyLeft
  rw [gaussianBinomial_eq_zero_of_lt q (Nat.lt_succ_self n)]
  simp

private theorem qCauchyLeft_add_right
    {R : Type*} [CommRing R]
    (q u v : R) {n k : ℕ} (hk : k ≤ n) :
    qCauchyLeft q u v n k + qCauchyRight q u v n k =
      (1 - u * v * q ^ n) * qCauchySummand q u v n k := by
  have hsub : n + 1 - k = n - k + 1 := by omega
  have hpow : q ^ (n - k) * q ^ k = q ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  have hcombine :
      (1 - v * q ^ (n - k)) +
          v * q ^ (n - k) * (1 - u * q ^ k) =
        1 - u * v * q ^ n := by
    calc
      (1 - v * q ^ (n - k)) +
          v * q ^ (n - k) * (1 - u * q ^ k) =
          1 - u * v * (q ^ (n - k) * q ^ k) := by ring
      _ = 1 - u * v * q ^ n := by rw [hpow]
  unfold qCauchyLeft qCauchyRight qCauchySummand
  rw [hsub, finiteQPochhammerIn_succ v q (n - k),
    finiteQPochhammerIn_succ u q k, pow_succ]
  calc
    _ = (gaussianBinomial q n k * finiteQPochhammerIn u q k *
          v ^ k * finiteQPochhammerIn v q (n - k)) *
        ((1 - v * q ^ (n - k)) +
          v * q ^ (n - k) * (1 - u * q ^ k)) := by ring
    _ = (gaussianBinomial q n k * finiteQPochhammerIn u q k *
          v ^ k * finiteQPochhammerIn v q (n - k)) *
        (1 - u * v * q ^ n) := by rw [hcombine]
    _ = (1 - u * v * q ^ n) *
        (gaussianBinomial q n k * finiteQPochhammerIn u q k *
          v ^ k * finiteQPochhammerIn v q (n - k)) := by ring

private theorem sum_qCauchySummand_succ
    {R : Type*} [CommRing R]
    (q u v : R) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 2),
        qCauchySummand q u v (n + 1) k) =
      (1 - u * v * q ^ n) *
        ∑ k ∈ Finset.range (n + 1), qCauchySummand q u v n k := by
  have hshift :
      (∑ k ∈ Finset.range (n + 1), qCauchyLeft q u v n (k + 1)) +
          qCauchyLeft q u v n 0 =
        ∑ k ∈ Finset.range (n + 1), qCauchyLeft q u v n k := by
    calc
      (∑ k ∈ Finset.range (n + 1), qCauchyLeft q u v n (k + 1)) +
          qCauchyLeft q u v n 0 =
          ∑ k ∈ Finset.range (n + 2), qCauchyLeft q u v n k := by
            symm
            exact Finset.sum_range_succ'
              (fun k ↦ qCauchyLeft q u v n k) (n + 1)
      _ = (∑ k ∈ Finset.range (n + 1), qCauchyLeft q u v n k) +
          qCauchyLeft q u v n (n + 1) := by
            exact Finset.sum_range_succ
              (fun k ↦ qCauchyLeft q u v n k) (n + 1)
      _ = ∑ k ∈ Finset.range (n + 1), qCauchyLeft q u v n k := by
            rw [qCauchyLeft_last, add_zero]
  calc
    (∑ k ∈ Finset.range (n + 2),
        qCauchySummand q u v (n + 1) k) =
        (∑ k ∈ Finset.range (n + 1),
          qCauchySummand q u v (n + 1) (k + 1)) +
            qCauchySummand q u v (n + 1) 0 := by
              exact Finset.sum_range_succ'
                (fun k ↦ qCauchySummand q u v (n + 1) k) (n + 1)
    _ = (∑ k ∈ Finset.range (n + 1),
          (qCauchyLeft q u v n (k + 1) +
            qCauchyRight q u v n k)) +
          qCauchyLeft q u v n 0 := by
            rw [qCauchySummand_succ_zero]
            apply congrArg (fun x ↦ x + qCauchyLeft q u v n 0)
            apply Finset.sum_congr rfl
            intro k _hk
            rw [qCauchySummand_succ_succ]
    _ = ((∑ k ∈ Finset.range (n + 1),
          qCauchyLeft q u v n (k + 1)) +
            qCauchyLeft q u v n 0) +
          ∑ k ∈ Finset.range (n + 1),
            qCauchyRight q u v n k := by
              rw [Finset.sum_add_distrib]
              ring
    _ = (∑ k ∈ Finset.range (n + 1),
          qCauchyLeft q u v n k) +
        ∑ k ∈ Finset.range (n + 1),
          qCauchyRight q u v n k := by rw [hshift]
    _ = ∑ k ∈ Finset.range (n + 1),
        (qCauchyLeft q u v n k + qCauchyRight q u v n k) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ k ∈ Finset.range (n + 1),
        (1 - u * v * q ^ n) * qCauchySummand q u v n k := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [qCauchyLeft_add_right q u v
            (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
    _ = (1 - u * v * q ^ n) *
        ∑ k ∈ Finset.range (n + 1), qCauchySummand q u v n k := by
          rw [Finset.mul_sum]

private theorem sum_qCauchySummand_eq
    {R : Type*} [CommRing R]
    (q u v : R) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), qCauchySummand q u v n k) =
      finiteQPochhammerIn (u * v) q n := by
  induction n with
  | zero => simp [qCauchySummand]
  | succ n ih =>
      change (∑ k ∈ Finset.range (n + 2),
          qCauchySummand q u v (n + 1) k) =
        finiteQPochhammerIn (u * v) q (n + 1)
      rw [sum_qCauchySummand_succ, ih,
        finiteQPochhammerIn_succ (u * v) q n]
      ring

/-- **Finite q-Cauchy identity over a commutative ring.**  For every base
`q`, parameters `u`, `v`, and length `n`,

`(u * v; q)_n = ∑ k ≤ n, [n choose k]_q (u; q)_k v^k (v; q)_(n-k)`.

The statement is denominator-free and total: it remains valid at roots of
unity, in positive characteristic, and in the presence of zero divisors. -/
theorem finiteQPochhammerIn_mul_eq_sum_gaussianBinomial
    {R : Type*} [CommRing R]
    (q u v : R) (n : ℕ) :
    finiteQPochhammerIn (u * v) q n =
      ∑ k ∈ Finset.range (n + 1),
        gaussianBinomial q n k * finiteQPochhammerIn u q k *
          v ^ k * finiteQPochhammerIn v q (n - k) := by
  symm
  exact sum_qCauchySummand_eq q u v n

end Fabius
