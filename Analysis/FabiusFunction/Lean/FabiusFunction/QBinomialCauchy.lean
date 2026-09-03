import FabiusFunction.QBinomialInversion

/-!
# Finite q-Cauchy identities

This module proves the finite q-Cauchy product identity over an arbitrary
commutative ring.  It is the parameter-convolution companion of the finite
q-binomial theorem:

`(u * v; q)_n = ∑ k≤n, [n choose k]_q (u;q)_k v^k (v;q)_(n-k)`.

The proof follows q-Pascal directly.  Its two contributions combine through

`(1 - v q^(n-k)) + v q^(n-k) (1 - u q^k) = 1 - u v q^n`,

so no division, cancellation, nonvanishing hypothesis, or restriction on
`q` is involved.  In particular the theorem remains valid at roots of unity,
in positive characteristic, and in rings with zero divisors.

## Main results

* `finite_qCauchy_identity` is the finite q-Cauchy convolution.
* `finiteQPochhammerIn_mul_eq_sum_gaussianBinomial` is its compatibility
  spelling from the first denominator-free API.
* `finite_qCauchy_identity_reflected` reflects the Gaussian row and exposes
  the orientation used in nested finite convolutions.
* `qBernsteinBasis` and `sum_qBernsteinBasis` package the `u = 0`
  specialization as a denominator-free partition of unity.
* `finite_qCauchy_second_identity` is the two-product finite Cauchy
  convolution used in the q-Pfaff--Saalschutz summation.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Finset

private def qCauchySummand
    {R : Type*} [CommRing R] (q u v : R) (n k : ℕ) : R :=
  gaussianBinomial q n k * finiteQPochhammerIn u q k * v ^ k *
    finiteQPochhammerIn v q (n - k)

private def qCauchyUnshifted
    {R : Type*} [CommRing R] (q u v : R) (n k : ℕ) : R :=
  gaussianBinomial q n k * finiteQPochhammerIn u q k * v ^ k *
    finiteQPochhammerIn v q (n + 1 - k)

private def qCauchyShifted
    {R : Type*} [CommRing R] (q u v : R) (n k : ℕ) : R :=
  q ^ (n - k) * gaussianBinomial q n k *
    finiteQPochhammerIn u q (k + 1) * v ^ (k + 1) *
      finiteQPochhammerIn v q (n - k)

private theorem qCauchySummand_zero_eq_unshifted
    {R : Type*} [CommRing R] (q u v : R) (n : ℕ) :
    qCauchySummand q u v (n + 1) 0 =
      qCauchyUnshifted q u v n 0 := by
  simp [qCauchySummand, qCauchyUnshifted]

private theorem qCauchySummand_succ_split
    {R : Type*} [CommRing R] (q u v : R)
    (n k : ℕ) (hk : k ≤ n) :
    qCauchySummand q u v (n + 1) (k + 1) =
      qCauchyUnshifted q u v n (k + 1) +
        qCauchyShifted q u v n k := by
  have hsub : n + 1 - (k + 1) = n - k := by omega
  unfold qCauchySummand qCauchyUnshifted qCauchyShifted
  rw [hsub, gaussianBinomial_succ_succ]
  ring

private theorem qCauchyUnshifted_add_shifted
    {R : Type*} [CommRing R] (q u v : R)
    (n k : ℕ) (hk : k ≤ n) :
    qCauchyUnshifted q u v n k + qCauchyShifted q u v n k =
      (1 - u * v * q ^ n) * qCauchySummand q u v n k := by
  have hindex : n + 1 - k = (n - k) + 1 := by omega
  have hq : q ^ (n - k) * q ^ k = q ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  unfold qCauchyUnshifted qCauchyShifted qCauchySummand
  rw [hindex, finiteQPochhammerIn_succ, finiteQPochhammerIn_succ,
    pow_succ]
  calc
    gaussianBinomial q n k * finiteQPochhammerIn u q k * v ^ k *
          (finiteQPochhammerIn v q (n - k) *
            (1 - v * q ^ (n - k))) +
        q ^ (n - k) * gaussianBinomial q n k *
          (finiteQPochhammerIn u q k * (1 - u * q ^ k)) *
            (v ^ k * v) * finiteQPochhammerIn v q (n - k) =
      (gaussianBinomial q n k * finiteQPochhammerIn u q k * v ^ k *
          finiteQPochhammerIn v q (n - k)) *
        ((1 - v * q ^ (n - k)) +
          v * q ^ (n - k) * (1 - u * q ^ k)) := by
      ring
    _ = (gaussianBinomial q n k * finiteQPochhammerIn u q k * v ^ k *
          finiteQPochhammerIn v q (n - k)) *
        (1 - u * v * (q ^ (n - k) * q ^ k)) := by
      ring
    _ = (1 - u * v * q ^ n) *
        (gaussianBinomial q n k * finiteQPochhammerIn u q k * v ^ k *
          finiteQPochhammerIn v q (n - k)) := by
      rw [hq]
      ring

private theorem sum_qCauchySummand_succ
    {R : Type*} [CommRing R] (q u v : R) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 2), qCauchySummand q u v (n + 1) k) =
      ∑ k ∈ Finset.range (n + 1),
        (qCauchyUnshifted q u v n k + qCauchyShifted q u v n k) := by
  have hlast : qCauchyUnshifted q u v n (n + 1) = 0 := by
    simp [qCauchyUnshifted,
      gaussianBinomial_eq_zero_of_lt q (Nat.lt_succ_self n)]
  calc
    (∑ k ∈ Finset.range (n + 2), qCauchySummand q u v (n + 1) k) =
        qCauchySummand q u v (n + 1) 0 +
          ∑ k ∈ Finset.range (n + 1),
            qCauchySummand q u v (n + 1) (k + 1) := by
      simpa only [show n + 2 = n + 1 + 1 by omega, add_comm] using
        Finset.sum_range_succ' (fun k => qCauchySummand q u v (n + 1) k)
          (n + 1)
    _ = qCauchyUnshifted q u v n 0 +
          ∑ k ∈ Finset.range (n + 1),
            (qCauchyUnshifted q u v n (k + 1) +
              qCauchyShifted q u v n k) := by
      rw [qCauchySummand_zero_eq_unshifted]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      exact qCauchySummand_succ_split q u v n k
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    _ = (qCauchyUnshifted q u v n 0 +
          ∑ k ∈ Finset.range (n + 1),
            qCauchyUnshifted q u v n (k + 1)) +
          ∑ k ∈ Finset.range (n + 1), qCauchyShifted q u v n k := by
      rw [Finset.sum_add_distrib]
      ac_rfl
    _ = (∑ k ∈ Finset.range (n + 2), qCauchyUnshifted q u v n k) +
          ∑ k ∈ Finset.range (n + 1), qCauchyShifted q u v n k := by
      congr 1
      simpa only [add_comm, show 1 + (n + 1) = n + 2 by omega] using
        (Finset.sum_range_succ'
          (fun k => qCauchyUnshifted q u v n k) (n + 1)).symm
    _ = (∑ k ∈ Finset.range (n + 1), qCauchyUnshifted q u v n k) +
          ∑ k ∈ Finset.range (n + 1), qCauchyShifted q u v n k := by
      rw [show n + 2 = n + 1 + 1 by omega, Finset.sum_range_succ, hlast,
        add_zero]
    _ = ∑ k ∈ Finset.range (n + 1),
          (qCauchyUnshifted q u v n k + qCauchyShifted q u v n k) := by
      rw [Finset.sum_add_distrib]

/-- **Finite q-Cauchy identity.**  For every commutative ring and all
`q`, `u`, `v`, and `n`,

`(u v;q)_n = ∑_{k=0}^n [n choose k]_q (u;q)_k v^k (v;q)_(n-k)`.

The formula is division-free and therefore includes `q = 0`, roots of
unity, positive-characteristic rings, zero divisors, and the empty product
at `n = 0`. -/
theorem finite_qCauchy_identity
    {R : Type*} [CommRing R] (q u v : R) (n : ℕ) :
    finiteQPochhammerIn (u * v) q n =
      ∑ k ∈ Finset.range (n + 1),
        gaussianBinomial q n k * finiteQPochhammerIn u q k * v ^ k *
          finiteQPochhammerIn v q (n - k) := by
  change finiteQPochhammerIn (u * v) q n =
    ∑ k ∈ Finset.range (n + 1), qCauchySummand q u v n k
  induction n with
  | zero => simp [qCauchySummand]
  | succ n ih =>
      calc
        finiteQPochhammerIn (u * v) q (n + 1) =
            (1 - u * v * q ^ n) * finiteQPochhammerIn (u * v) q n := by
          rw [finiteQPochhammerIn_succ]
          ring
        _ = (1 - u * v * q ^ n) *
              ∑ k ∈ Finset.range (n + 1), qCauchySummand q u v n k := by
          rw [ih]
        _ = ∑ k ∈ Finset.range (n + 1),
              (qCauchyUnshifted q u v n k +
                qCauchyShifted q u v n k) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          exact (qCauchyUnshifted_add_shifted q u v n k
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).symm
        _ = ∑ k ∈ Finset.range (n + 2),
              qCauchySummand q u v (n + 1) k :=
          (sum_qCauchySummand_succ q u v n).symm

/-- Compatibility spelling for `finite_qCauchy_identity`.

This preserves the original public denominator-free API name while exposing
the expanded q-Cauchy family through the shorter canonical name. -/
theorem finiteQPochhammerIn_mul_eq_sum_gaussianBinomial
    {R : Type*} [CommRing R] (q u v : R) (n : ℕ) :
    finiteQPochhammerIn (u * v) q n =
      ∑ k ∈ Finset.range (n + 1),
        gaussianBinomial q n k * finiteQPochhammerIn u q k * v ^ k *
          finiteQPochhammerIn v q (n - k) :=
  finite_qCauchy_identity q u v n

/-- **Reflected finite q-Cauchy identity.**  Reflecting the summation index
in `finite_qCauchy_identity` gives

`(u v;q)_n = ∑_{k=0}^n [n choose k]_q (v;q)_k v^(n-k) (u;q)_(n-k)`.

This orientation is especially useful when a nested convolution naturally
produces the complementary exponent `n - k`.  Like the primary identity, it
is valid in every commutative ring without cancellation or nonvanishing
hypotheses. -/
theorem finite_qCauchy_identity_reflected
    {R : Type*} [CommRing R] (q u v : R) (n : ℕ) :
    finiteQPochhammerIn (u * v) q n =
      ∑ k ∈ Finset.range (n + 1),
        gaussianBinomial q n k * finiteQPochhammerIn v q k *
          v ^ (n - k) * finiteQPochhammerIn u q (n - k) := by
  let f : ℕ → R := fun k =>
    gaussianBinomial q n k * finiteQPochhammerIn u q k * v ^ k *
      finiteQPochhammerIn v q (n - k)
  have hreflect := Finset.sum_range_reflect f (n + 1)
  calc
    finiteQPochhammerIn (u * v) q n =
        ∑ k ∈ Finset.range (n + 1), f k := by
      simpa only [f] using finite_qCauchy_identity q u v n
    _ = ∑ k ∈ Finset.range (n + 1), f (n - k) := by
      symm
      simpa only [Nat.add_sub_cancel] using hreflect
    _ = ∑ k ∈ Finset.range (n + 1),
          gaussianBinomial q n k * finiteQPochhammerIn v q k *
            v ^ (n - k) * finiteQPochhammerIn u q (n - k) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      simp only [f, Nat.sub_sub_self hkn]
      rw [gaussianBinomial_symm q hkn]
      ring

/-! ## The q-Bernstein partition of unity -/

/-- The denominator-free q-Bernstein basis term

`[n choose k]_q x^k (x;q)_(n-k)`.

It is defined over an arbitrary commutative ring and is total in `k`; the
Gaussian coefficient makes every term above row `n` vanish. -/
def qBernsteinBasis
    {R : Type*} [CommRing R] (q x : R) (n k : ℕ) : R :=
  gaussianBinomial q n k * x ^ k * finiteQPochhammerIn x q (n - k)

/-- **q-Bernstein partition of unity.**  The full denominator-free row sums
to one over every commutative ring:

`∑_{k=0}^n [n choose k]_q x^k (x;q)_(n-k) = 1`.

This is `finite_qCauchy_identity` at `u = 0`; it therefore includes every
value of `q` and `x`, including roots of unity and zero divisors. -/
theorem sum_qBernsteinBasis
    {R : Type*} [CommRing R] (q x : R) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), qBernsteinBasis q x n k) = 1 := by
  have h := finite_qCauchy_identity q (0 : R) x n
  simpa [qBernsteinBasis, finiteQPochhammerIn] using h.symm

private def qCauchySecondSummand
    {R : Type*} [CommRing R] (q a b c : R) (n k : ℕ) : R :=
  gaussianBinomial q n k * finiteQPochhammerIn a q k *
    finiteQPochhammerIn b q k * c ^ k *
      finiteQPochhammerIn c q (n - k) *
        finiteQPochhammerIn (a * b * c * q ^ k) q (n - k)

private def qCauchySecondExpanded
    {R : Type*} [CommRing R]
    (q a b c : R) (n k r : ℕ) : R :=
  gaussianBinomial q n k * finiteQPochhammerIn a q k *
    finiteQPochhammerIn b q k * c ^ k *
      finiteQPochhammerIn c q (n - k) *
        (gaussianBinomial q (n - k) r *
          finiteQPochhammerIn (b * q ^ k) q r * (a * c) ^ r *
            finiteQPochhammerIn (a * c) q (n - k - r))

private def qCauchySecondRegrouped
    {R : Type*} [CommRing R]
    (q a b c : R) (n m k : ℕ) : R :=
  (gaussianBinomial q n m * finiteQPochhammerIn b q m * c ^ m *
      finiteQPochhammerIn c q (n - m) *
        finiteQPochhammerIn (a * c) q (n - m)) *
    (gaussianBinomial q m k * finiteQPochhammerIn a q k *
      a ^ (m - k) *
        finiteQPochhammerIn (c * q ^ (n - m)) q (m - k))

private theorem qCauchySecondSummand_expand
    {R : Type*} [CommRing R]
    (q a b c : R) (n k : ℕ) :
    qCauchySecondSummand q a b c n k =
      ∑ r ∈ Finset.range (n - k + 1),
        qCauchySecondExpanded q a b c n k r := by
  have hparameter :
      (b * q ^ k) * (a * c) = a * b * c * q ^ k := by
    ring
  unfold qCauchySecondSummand qCauchySecondExpanded
  rw [← hparameter,
    finite_qCauchy_identity q (b * q ^ k) (a * c) (n - k),
    Finset.mul_sum]

private theorem qCauchySecondExpanded_eq_regrouped
    {R : Type*} [CommRing R]
    (q a b c : R) {n m k : ℕ} (hkm : k ≤ m) (hmn : m ≤ n) :
    qCauchySecondExpanded q a b c n k (m - k) =
      qCauchySecondRegrouped q a b c n m k := by
  have hflag :
      gaussianBinomial q n k *
          gaussianBinomial q (n - k) (m - k) =
        gaussianBinomial q n m * gaussianBinomial q m k :=
    (gaussianBinomial_mul q hkm hmn).symm
  have hb :
      finiteQPochhammerIn b q k *
          finiteQPochhammerIn (b * q ^ k) q (m - k) =
        finiteQPochhammerIn b q m := by
    calc
      finiteQPochhammerIn b q k *
            finiteQPochhammerIn (b * q ^ k) q (m - k) =
          finiteQPochhammerIn b q (k + (m - k)) :=
        (finiteQPochhammerIn_add b q k (m - k)).symm
      _ = finiteQPochhammerIn b q m := by
        rw [Nat.add_sub_of_le hkm]
  have hc :
      finiteQPochhammerIn c q (n - k) =
        finiteQPochhammerIn c q (n - m) *
          finiteQPochhammerIn (c * q ^ (n - m)) q (m - k) := by
    rw [show n - k = (n - m) + (m - k) by omega,
      finiteQPochhammerIn_add]
  have hpower :
      c ^ k * (a * c) ^ (m - k) = c ^ m * a ^ (m - k) := by
    rw [mul_pow]
    calc
      c ^ k * (a ^ (m - k) * c ^ (m - k)) =
          a ^ (m - k) * (c ^ k * c ^ (m - k)) := by ring
      _ = a ^ (m - k) * c ^ m := by
        rw [← pow_add, Nat.add_sub_of_le hkm]
      _ = c ^ m * a ^ (m - k) := by ring
  have hremaining : n - k - (m - k) = n - m := by omega
  unfold qCauchySecondExpanded qCauchySecondRegrouped
  rw [hremaining]
  calc
    gaussianBinomial q n k * finiteQPochhammerIn a q k *
          finiteQPochhammerIn b q k * c ^ k *
            finiteQPochhammerIn c q (n - k) *
              (gaussianBinomial q (n - k) (m - k) *
                finiteQPochhammerIn (b * q ^ k) q (m - k) *
                  (a * c) ^ (m - k) *
                    finiteQPochhammerIn (a * c) q (n - m)) =
        (gaussianBinomial q n k *
            gaussianBinomial q (n - k) (m - k)) *
          (finiteQPochhammerIn b q k *
            finiteQPochhammerIn (b * q ^ k) q (m - k)) *
          (c ^ k * (a * c) ^ (m - k)) *
          finiteQPochhammerIn a q k * finiteQPochhammerIn c q (n - k) *
          finiteQPochhammerIn (a * c) q (n - m) := by
      ring
    _ = (gaussianBinomial q n m * gaussianBinomial q m k) *
          finiteQPochhammerIn b q m *
          (c ^ m * a ^ (m - k)) * finiteQPochhammerIn a q k *
          (finiteQPochhammerIn c q (n - m) *
            finiteQPochhammerIn (c * q ^ (n - m)) q (m - k)) *
          finiteQPochhammerIn (a * c) q (n - m) := by
      rw [hflag, hb, hpower, hc]
    _ = (gaussianBinomial q n m * finiteQPochhammerIn b q m * c ^ m *
          finiteQPochhammerIn c q (n - m) *
            finiteQPochhammerIn (a * c) q (n - m)) *
        (gaussianBinomial q m k * finiteQPochhammerIn a q k *
          a ^ (m - k) *
            finiteQPochhammerIn (c * q ^ (n - m)) q (m - k)) := by
      ring

private theorem sum_qCauchySecondRegrouped
    {R : Type*} [CommRing R]
    (q a b c : R) {n m : ℕ} (hmn : m ≤ n) :
    (∑ k ∈ Finset.range (m + 1),
      qCauchySecondRegrouped q a b c n m k) =
        finiteQPochhammerIn (a * c) q n *
          (gaussianBinomial q n m * finiteQPochhammerIn b q m * c ^ m *
            finiteQPochhammerIn c q (n - m)) := by
  have hparameter :
      (c * q ^ (n - m)) * a = (a * c) * q ^ (n - m) := by
    ring
  have hinner :
      (∑ k ∈ Finset.range (m + 1),
        gaussianBinomial q m k * finiteQPochhammerIn a q k *
          a ^ (m - k) *
            finiteQPochhammerIn (c * q ^ (n - m)) q (m - k)) =
        finiteQPochhammerIn ((a * c) * q ^ (n - m)) q m := by
    calc
      (∑ k ∈ Finset.range (m + 1),
          gaussianBinomial q m k * finiteQPochhammerIn a q k *
            a ^ (m - k) *
              finiteQPochhammerIn (c * q ^ (n - m)) q (m - k)) =
          finiteQPochhammerIn ((c * q ^ (n - m)) * a) q m :=
        (finite_qCauchy_identity_reflected
          q (c * q ^ (n - m)) a m).symm
      _ = finiteQPochhammerIn ((a * c) * q ^ (n - m)) q m := by
        rw [hparameter]
  have hac :
      finiteQPochhammerIn (a * c) q (n - m) *
          finiteQPochhammerIn ((a * c) * q ^ (n - m)) q m =
        finiteQPochhammerIn (a * c) q n := by
    calc
      finiteQPochhammerIn (a * c) q (n - m) *
            finiteQPochhammerIn ((a * c) * q ^ (n - m)) q m =
          finiteQPochhammerIn (a * c) q ((n - m) + m) :=
        (finiteQPochhammerIn_add (a * c) q (n - m) m).symm
      _ = finiteQPochhammerIn (a * c) q n := by
        rw [Nat.sub_add_cancel hmn]
  unfold qCauchySecondRegrouped
  rw [← Finset.mul_sum, hinner]
  calc
    (gaussianBinomial q n m * finiteQPochhammerIn b q m * c ^ m *
          finiteQPochhammerIn c q (n - m) *
            finiteQPochhammerIn (a * c) q (n - m)) *
        finiteQPochhammerIn ((a * c) * q ^ (n - m)) q m =
      (finiteQPochhammerIn (a * c) q (n - m) *
          finiteQPochhammerIn ((a * c) * q ^ (n - m)) q m) *
        (gaussianBinomial q n m * finiteQPochhammerIn b q m * c ^ m *
          finiteQPochhammerIn c q (n - m)) := by
      ring
    _ = finiteQPochhammerIn (a * c) q n *
        (gaussianBinomial q n m * finiteQPochhammerIn b q m * c ^ m *
          finiteQPochhammerIn c q (n - m)) := by
      rw [hac]

/-- **Second finite q-Cauchy identity.**  For every commutative ring,

`(a c;q)_n (b c;q)_n = ∑_{k=0}^n [n choose k]_q
  (a;q)_k (b;q)_k c^k (c;q)_(n-k) (a b c q^k;q)_(n-k)`.

The proof expands the last factor by `finite_qCauchy_identity`, reindexes
the resulting finite triangle, and evaluates the inner and outer sums by the
two orientations of finite q-Cauchy.  Every step is polynomial: the result
therefore includes `q = 0`, roots of unity, positive characteristic, zero
divisors, and `n = 0` without additional hypotheses. -/
theorem finite_qCauchy_second_identity
    {R : Type*} [CommRing R] (q a b c : R) (n : ℕ) :
    finiteQPochhammerIn (a * c) q n *
        finiteQPochhammerIn (b * c) q n =
      ∑ k ∈ Finset.range (n + 1),
        gaussianBinomial q n k * finiteQPochhammerIn a q k *
          finiteQPochhammerIn b q k * c ^ k *
            finiteQPochhammerIn c q (n - k) *
              finiteQPochhammerIn (a * b * c * q ^ k) q (n - k) := by
  symm
  change (∑ k ∈ Finset.range (n + 1),
    qCauchySecondSummand q a b c n k) = _
  calc
    (∑ k ∈ Finset.range (n + 1),
        qCauchySecondSummand q a b c n k) =
      ∑ k ∈ Finset.range (n + 1),
        ∑ r ∈ Finset.range (n - k + 1),
          qCauchySecondExpanded q a b c n k r := by
      apply Finset.sum_congr rfl
      intro k _hk
      exact qCauchySecondSummand_expand q a b c n k
    _ = ∑ k ∈ Finset.range (n + 1),
        ∑ r ∈ Finset.range (n + 1 - k),
          qCauchySecondExpanded q a b c n k r := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [show n - k + 1 = n + 1 - k by omega]
    _ = ∑ m ∈ Finset.range (n + 1),
        ∑ k ∈ Finset.range (m + 1),
          qCauchySecondExpanded q a b c n k (m - k) := by
      simpa using
        (Finset.sum_range_diag_flip (n + 1)
          (fun k r => qCauchySecondExpanded q a b c n k r)).symm
    _ = ∑ m ∈ Finset.range (n + 1),
        ∑ k ∈ Finset.range (m + 1),
          qCauchySecondRegrouped q a b c n m k := by
      apply Finset.sum_congr rfl
      intro m hm
      have hmn : m ≤ n :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      apply Finset.sum_congr rfl
      intro k hk
      have hkm : k ≤ m :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      exact qCauchySecondExpanded_eq_regrouped q a b c hkm hmn
    _ = ∑ m ∈ Finset.range (n + 1),
        finiteQPochhammerIn (a * c) q n *
          (gaussianBinomial q n m * finiteQPochhammerIn b q m * c ^ m *
            finiteQPochhammerIn c q (n - m)) := by
      apply Finset.sum_congr rfl
      intro m hm
      exact sum_qCauchySecondRegrouped q a b c
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))
    _ = finiteQPochhammerIn (a * c) q n *
        ∑ m ∈ Finset.range (n + 1),
          gaussianBinomial q n m * finiteQPochhammerIn b q m * c ^ m *
            finiteQPochhammerIn c q (n - m) := by
      rw [Finset.mul_sum]
    _ = finiteQPochhammerIn (a * c) q n *
        finiteQPochhammerIn (b * c) q n := by
      rw [← finite_qCauchy_identity q b c n]

end Fabius
